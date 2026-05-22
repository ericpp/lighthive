import array
import hashlib
import struct
import time
from binascii import hexlify
from binascii import unhexlify
from collections import OrderedDict
from datetime import timedelta

import ecdsa
from dateutil.parser import parse

from .chains import known_chains
from .key_objects import PrivateKey
from .utils import compat_bytes

try:
    import secp256k1
    USE_SECP256K1 = (
        hasattr(secp256k1, 'ffi')
        and hasattr(secp256k1, 'lib')
        and hasattr(secp256k1.lib, 'secp256k1_ecdsa_sign_recoverable')
    )
except ImportError:
    USE_SECP256K1 = False


def _secp256k1_context():
    """Shared libsecp256k1 context (0.14+) or None for legacy per-key ctx."""
    return getattr(secp256k1, 'secp256k1_ctx', None)


class TransactionBuilder:

    def __init__(self, client):
        self.client = client
        self.transaction = OrderedDict()
        self.message = None
        self.digest = None

    def prepare(self):
        properties = self.client('condenser_api').get_dynamic_global_properties()
        ref_block_num = (properties["last_irreversible_block_num"] - 1) & 0xFFFF
        ref_block_header = self.client('condenser_api').get_block_header(
            properties["last_irreversible_block_num"])
        head_block_id = ref_block_header["previous"] if ref_block_header else '0000000000000000000000000000000000000000'
        ref_block_prefix = struct.unpack_from("<I", unhexlify(head_block_id), 4)[0]
        expiration = (
                parse(properties["time"]) + timedelta(seconds=600)
        ).strftime('%Y-%m-%dT%H:%M:%S')
        self.transaction["ref_block_num"] = ref_block_num
        self.transaction["ref_block_prefix"] = ref_block_prefix
        self.transaction["expiration"] = expiration

        return self

    def get_known_chains(self):
        return known_chains

    def get_chain_params(self, chain):
        chains = self.get_known_chains()
        if isinstance(chain, str) and chain in chains:
            chain_params = chains[chain]
        elif isinstance(chain, dict):
            chain_params = chain
        else:
            raise Exception("Invalid chain")

        return chain_params

    def derive_digest(self, chain, hex):
        chain_params = self.get_chain_params(chain)
        self.chainid = chain_params["chain_id"]
        self.message = unhexlify(self.chainid + hex[0:-2])
        self.digest = hashlib.sha256(self.message).digest()

    def recover_public_key(self, digest, signature, i):
        curve = ecdsa.SECP256k1.curve
        G = ecdsa.SECP256k1.generator
        order = ecdsa.SECP256k1.order
        yp = (i % 2)
        r, s = ecdsa.util.sigdecode_string(signature, order)
        x = r + (i // 2) * order
        alpha = ((x * x * x) + (curve.a() * x) + curve.b()) % curve.p()
        beta = ecdsa.numbertheory.square_root_mod_prime(alpha, curve.p())
        y = beta if (beta - yp) % 2 == 0 else curve.p() - beta
        R = ecdsa.ellipticcurve.Point(curve, x, y, order)
        e = ecdsa.util.string_to_number(digest)
        Q = ecdsa.numbertheory.inverse_mod(r, order) * (s * R +
                                                        (-e % order) * G)
        if not ecdsa.VerifyingKey.from_public_point(
                Q, curve=ecdsa.SECP256k1).verify_digest(
                    signature, digest, sigdecode=ecdsa.util.sigdecode_string):
            return None
        return ecdsa.VerifyingKey.from_public_point(Q, curve=ecdsa.SECP256k1)

    def compressed_pubkey(self, pk):
        order = pk.curve.generator.order()
        p = pk.pubkey.point
        x_str = ecdsa.util.number_to_string(p.x(), order)
        return compat_bytes(chr(2 + (p.y() & 1)), 'ascii') + x_str

    def recover_pubkey_parameter(self, digest, signature, pubkey):
        for i in range(0, 4):
            if USE_SECP256K1:
                sig = pubkey.ecdsa_recoverable_deserialize(signature, i)
                p = secp256k1.PublicKey(
                    pubkey.ecdsa_recover(self.message, sig))
                if p.serialize() == pubkey.serialize():
                    return i
            else:
                p = self.recover_public_key(digest, signature, i)
                if (p.to_string() == pubkey.to_string()
                        or self.compressed_pubkey(p) == pubkey.to_string()):
                    return i
        return None

    def _is_canonical(self, sig):
        return (not (sig[0] & 0x80)
                and not (sig[0] == 0 and not (sig[1] & 0x80))
                and not (sig[32] & 0x80)
                and not (sig[32] == 0 and not (sig[33] & 0x80)))

    def _transaction_id(self, tx_hex):
        raw_bytes = bytes.fromhex(tx_hex[:-2])
        return hashlib.sha256(raw_bytes).digest()[:20].hex()

    def _wait_for_inclusion(self, tx_id, timeout=15.0):
        """Poll transaction_status_api after async broadcast (sync API replacement)."""
        deadline = time.time() + timeout

        while time.time() < deadline:
            try:
                tx_data = self.client('condenser_api').get_transaction(tx_id)
                if tx_data and tx_data.get("block_num"):
                    return {
                        "id": tx_id,
                        "block_num": tx_data["block_num"],
                        "trx_num": tx_data.get("transaction_num", 0),
                        "expired": False,
                    }
            except Exception:
                pass

            time.sleep(1.0)

        return {"id": tx_id, "block_num": 0, "trx_num": 0, "expired": False}

    def broadcast(self, operations, chain=None, dry_run=False, sync=False):
        preferred_api_type = self.client.api_type

        try:
            if not isinstance(operations, list):
                operations = [operations, ]

            op_list = []
            for operation in operations:
                op_list.append(operation.to_dict())

            self.prepare()

            self.transaction["operations"] = op_list
            self.transaction["extensions"] = []
            self.transaction["signatures"] = []
            tx_hex = self.client('condenser_api').get_transaction_hex(self.transaction)
            self.derive_digest(chain, tx_hex)

            sigs = []
            for wif in self.client.keys:
                p = compat_bytes(PrivateKey(wif))
                i = 0
                if USE_SECP256K1:
                    ndata = secp256k1.ffi.new("const int *ndata")
                    ndata[0] = 0
                    while True:
                        ndata[0] += 1
                        privkey = secp256k1.PrivateKey(p, raw=True)
                        ctx = _secp256k1_context()
                        sig = secp256k1.ffi.new(
                            'secp256k1_ecdsa_recoverable_signature *')
                        signed = secp256k1.lib.secp256k1_ecdsa_sign_recoverable(
                            ctx, sig, self.digest, privkey.private_key,
                            secp256k1.ffi.NULL, ndata)
                        assert signed == 1
                        signature, i = privkey.ecdsa_recoverable_serialize(sig)
                        if self._is_canonical(signature):
                            i += 4
                            i += 27
                            break
                else:
                    cnt = 0
                    sk = ecdsa.SigningKey.from_string(p, curve=ecdsa.SECP256k1)
                    while 1:
                        cnt += 1
                        if not cnt % 20:
                            print("Still searching for a canonical signature. "
                                  "Tried %d times already!" % cnt)

                        k = ecdsa.rfc6979.generate_k(
                            sk.curve.generator.order(),
                            sk.privkey.secret_multiplier,
                            hashlib.sha256,
                            hashlib.sha256(
                                self.digest + struct.pack("d", time.time(
                                ))
                            ).digest())

                        sigder = sk.sign_digest(
                            self.digest, sigencode=ecdsa.util.sigencode_der, k=k)

                        r, s = ecdsa.util.sigdecode_der(sigder,
                                                        sk.curve.generator.order())
                        signature = ecdsa.util.sigencode_string(
                            r, s, sk.curve.generator.order())

                        sigder = array.array('B', sigder)
                        lenR = sigder[3]
                        lenS = sigder[5 + lenR]
                        if lenR == 32 and lenS == 32:
                            i = self.recover_pubkey_parameter(
                                self.digest, signature, sk.get_verifying_key())
                            i += 4
                            i += 27
                            break

                sigstr = struct.pack("<B", i)
                sigstr += signature
                sigs.append(hexlify(sigstr).decode('ascii'))

            self.transaction["signatures"] = sigs
            if dry_run:
                return self.transaction

            self.client('condenser_api').broadcast_transaction(self.transaction)
            if sync:
                tx_id = self._transaction_id(tx_hex)
                return self._wait_for_inclusion(tx_id)
            return {}
        finally:
            self.client.api_type = preferred_api_type
