#!/usr/bin/env python3
"""
PAK Tool - Flet GUI Application for PUBG Mobile PAK file manipulation.
Single file main.py - Complete GUI version.
"""

import flet as ft
import argparse
import sys
import os
import json
import time
import shutil
import struct
import math
import hashlib
import zlib
import tempfile
import uuid
import platform
import subprocess
import base64
import ctypes
import itertools as it
import colorsys
import random
import threading
import traceback
from pathlib import Path, PurePath
from typing import List, Dict, Tuple, Optional, Any
from dataclasses import dataclass
from functools import lru_cache
from datetime import datetime

# Optional imports with fallbacks
try:
    import requests
except ImportError:
    requests = None

try:
    import pytz
except ImportError:
    pytz = None

try:
    import gmalg
except ImportError:
    gmalg = None

try:
    from Crypto.Cipher import AES
    from Crypto.Cipher.AES import MODE_CBC
    from Crypto.Hash import SHA1
    from Crypto.Util.Padding import unpad
except ImportError:
    AES = None
    MODE_CBC = None
    SHA1 = None
    unpad = None

try:
    from zstandard import ZstdDecompressor, ZstdCompressionDict, DICT_TYPE_AUTO, ZstdCompressor
except ImportError:
    ZstdDecompressor = None
    ZstdCompressionDict = None
    DICT_TYPE_AUTO = None
    ZstdCompressor = None


# ==================== CONSTANTS ====================

ZUC_KEY = bytes.fromhex('01010101010101010101010101010101')
ZUC_IV = bytes.fromhex('FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF')

RSA_MOD_1 = bytes.fromhex('CBE8B9F2504050EF9831B719E9A6249A6D238505ADE909BDE78C180DED6072A0C3347B8AF4780E1F212D952D82D4BF7F233C1ECA499E1F9D9A85B4FAD759F54BABC1666C5DE411EA9E4B2374425DD6C6F54333BBC8F2610FE6063E4D0D6C21A671A8F7C3740555E5DC06D4E1691C456DB4116C0C012BF7B206E8311AAAEC689952BF804EF638F09D5822B4117B114208F14DEB459E80CB770E5B0D7978E21F5E6CED4999D3583108221A7AB28B960277ADB5690A332784019D9C195BE4EA9EA0A09459010F236465DE0D59C3EF7324E954E1118D93EE19F299760C2CDB963CE87973EA5ECC9BBE81C27D4C7C8572AC07E9BCEAC9BD72AB7A56A3C0AD736ABCE4')
RSA_MOD_2 = bytes.fromhex('7F58E8A39A4DA4E87357DDD650EAA16D3B5CE95B213D1030A662566444796A78A84AE9AC3DBFFDE7F41094896696835DAF13B89E6EC2B84963B1B1BAF7151DA245C3FBFAE2A6AE18B2684D03F9229DE2C91440F2A3A3BCDE1E5680C16722A88039C73560D5D43F4B6562C2EEA5B1D926D86B51108A2643C70FB74D6442CE3A08339B8FD8F660AE88129B7AB8C46F2FA58124485CCCB1E987B05A6DA65A01858ED3F89905449AE42BB07290FCB9994BF22E26610BCABB9804783A3B9587917F3D97316EDDA15C5E13F79066407B55A93B291B68A4AC42A98D6E35FED84B14A792D154E62028DDAD20FC301951E5924BE9AD62FB719DD94CC30CAB871BEC4377A8')

SIMPLE1_DECRYPT_KEY = 121
SIMPLE2_DECRYPT_KEY = bytes.fromhex('E55B4ED1')
SIMPLE2_BLOCK_SIZE = 16

SM4_SECRET_4 = 'eb691efea914241317a8'
SM4_SECRET_2 = 'Q0hVTKey$as*1ZFlQCiA'
SM4_SECRET_NEW = [
    'xG2qW5lP7lV2iN5fN5pG',
    'xT1cJ6dL5wC0kK1rB4dK',
    'qC4jS5bZ6fL5xE6nD4zA',
    'gD4jQ2aL3bS3lC3xT0iW',
    'xU1yQ8wE9zY3gZ3bT5aE',
    'gW1fR0jK6wQ4oN0oK1kZ',
    'uQ3cO2dX7xY4xU7gH7iS',
    'aJ4pV7iZ7pU4wP2aC2cZ',
    'cX6jT3cM2oT3vK0kJ1qN',
    'iT2vS0cS6yT6cZ1sE1lO',
    'hM1pH9iY8wM9hT4lN5uJ',
    'kG6bC8jK0fL0dE4sH4mL',
    'dB6lB3vE0eZ8wM8rI0aC',
    'tP7sP7nI9rA2vQ4cV5yQ',
    'aT0cL1yN4pT3sZ7eM2vY',
    'uV6fU8fC9zN3mP5dH8mN',
    'jU5bH7IQ0fM9hK2kl0oF',
    'WJyb2tlci13cy0xMzE0M',
    'iQ0eM0mJ7uT0kV6kL5zY',
    'wD2rP3lP9xF4mE1eC5jS',
    '9ydE1vbml0b3JMb2cmbG',
    'fO3kW1fE6eD0pU1kY7xK',
]

EM_SIMPLE1 = 1
EM_SIMPLE2 = 16
EM_SM4_2 = 2
EM_SM4_4 = 4
EM_SM4_NEW_BASE = 31
EM_SM4_NEW_MASK = ~EM_SM4_NEW_BASE
EM_UNKNOWN_17 = 17

CM_NONE = 0
CM_ZLIB = 1
CM_ZSTD = 6
CM_ZSTD_DICT = 8
CM_MASK = 15

SKIP_NAMES = {'pak_manifest.json', '.DS_Store', 'index.csv', 'Debug_'}


# ==================== SM4 CIPHER ====================

class SM4:
    _S_BOX = bytes([
        52, 102, 37, 116, 137, 120, 228, 169, 90, 65, 188, 122, 214, 22, 33, 35,
        77, 97, 218, 148, 155, 223, 19, 60, 105, 58, 49, 10, 95, 215, 153, 149,
        241, 174, 114, 61, 7, 96, 36, 182, 152, 238, 196, 162, 45, 136, 221, 141,
        4, 234, 187, 17, 202, 62, 93, 161, 246, 63, 176, 151, 128, 71, 43, 166,
        230, 247, 217, 177, 89, 192, 124, 190, 84, 40, 183, 126, 79, 248, 67, 110,
        160, 80, 14, 245, 144, 184, 251, 163, 123, 98, 25, 70, 3, 42, 185, 143,
        159, 119, 180, 91, 131, 135, 8, 235, 226, 30, 66, 240, 15, 232, 113, 106,
        117, 173, 85, 31, 181, 171, 51, 250, 127, 21, 189, 133, 216, 6, 104, 179,
        82, 48, 72, 11, 0, 237, 239, 178, 87, 142, 231, 108, 213, 229, 46, 83,
        130, 5, 249, 129, 244, 86, 191, 140, 75, 227, 219, 74, 145, 76, 44, 211,
        64, 41, 78, 32, 20, 54, 121, 9, 111, 209, 55, 224, 57, 12, 138, 146,
        56, 18, 53, 109, 225, 253, 147, 154, 23, 212, 201, 156, 107, 132, 38, 157,
        175, 118, 193, 158, 208, 150, 197, 203, 233, 115, 73, 210, 205, 100, 195, 199,
        1, 125, 243, 172, 252, 222, 164, 68, 50, 27, 194, 186, 28, 2, 198, 39,
        69, 139, 242, 24, 167, 16, 81, 29, 200, 207, 99, 255, 47, 13, 88, 206,
        101, 165, 220, 26, 59, 134, 254, 34, 92, 168, 94, 103, 170, 236, 112, 204
    ])
    _FK = [1184304796, 1270900830, 1493524870, 3164752158]
    _CK = [964907, 973793155, 2654690407, 2916866751, 2071233739, 1226140771, 3348805095, 2045549823, 388349611, 800627875, 612403927, 3721562911, 1195432523, 3150178931, 612053223, 2445162591, 67183755, 1174197155, 1393249511, 3331183455, 3822152747, 1332317203, 1804781383, 1990130463, 1282653851, 3376591251, 2910902311, 925872959, 332098219, 735840931, 396665415, 3588844719]

    @staticmethod
    def ROL32(x, n):
        return (x << n) & 0xFFFFFFFF | (x >> (32 - n))

    @staticmethod
    def _BS(X):
        return (SM4._S_BOX[X >> 24 & 255] << 24 |
                SM4._S_BOX[X >> 16 & 255] << 16 |
                SM4._S_BOX[X >> 8 & 255] << 8 |
                SM4._S_BOX[X & 255])

    @staticmethod
    def _T0(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 2) ^ SM4.ROL32(X, 10) ^ SM4.ROL32(X, 18) ^ SM4.ROL32(X, 24)

    @staticmethod
    def _T1(X):
        X = SM4._BS(X)
        return X ^ SM4.ROL32(X, 13) ^ SM4.ROL32(X, 23)

    @staticmethod
    def _key_expand(key: bytes, rkey: list):
        K0 = int.from_bytes(key[0:4], 'big') ^ SM4._FK[0]
        K1 = int.from_bytes(key[4:8], 'big') ^ SM4._FK[1]
        K2 = int.from_bytes(key[8:12], 'big') ^ SM4._FK[2]
        K3 = int.from_bytes(key[12:16], 'big') ^ SM4._FK[3]
        for i in range(0, 32, 4):
            K0 = K0 ^ SM4._T1(K1 ^ K2 ^ K3 ^ SM4._CK[i])
            rkey[i] = K0
            K1 = K1 ^ SM4._T1(K2 ^ K3 ^ K0 ^ SM4._CK[i + 1])
            rkey[i + 1] = K1
            K2 = K2 ^ SM4._T1(K3 ^ K0 ^ K1 ^ SM4._CK[i + 2])
            rkey[i + 2] = K2
            K3 = K3 ^ SM4._T1(K0 ^ K1 ^ K2 ^ SM4._CK[i + 3])
            rkey[i + 3] = K3

    @classmethod
    def key_length(cls):
        return 16

    @classmethod
    def block_length(cls):
        return 16

    def __init__(self, key: bytes):
        if len(key) != self.key_length():
            raise ValueError(f'Key must be {self.key_length()} bytes')
        self._key = key
        self._rkey = [0] * 32
        SM4._key_expand(self._key, self._rkey)
        self._block_buffer = bytearray()
        if not hasattr(SM4, '_T_TABLES'):
            SM4._T_TABLES = SM4._make_t_tables()

    def encrypt(self, block: bytes) -> bytes:
        if len(block) != self.block_length():
            raise ValueError(f'Block must be {self.block_length()} bytes')
        RK = self._rkey
        X0 = int.from_bytes(block[0:4], 'big')
        X1 = int.from_bytes(block[4:8], 'big')
        X2 = int.from_bytes(block[8:12], 'big')
        X3 = int.from_bytes(block[12:16], 'big')
        for i in range(0, 32, 4):
            X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[i])
            X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[i + 1])
            X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[i + 2])
            X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[i + 3])
        BUFFER = self._block_buffer
        BUFFER.clear()
        BUFFER.extend(X3.to_bytes(4, 'big'))
        BUFFER.extend(X2.to_bytes(4, 'big'))
        BUFFER.extend(X1.to_bytes(4, 'big'))
        BUFFER.extend(X0.to_bytes(4, 'big'))
        return bytes(BUFFER)

    def decrypt(self, block: bytes) -> bytes:
        if len(block) != self.block_length():
            raise ValueError(f'Block must be {self.block_length()} bytes')
        RK = self._rkey
        X0 = int.from_bytes(block[0:4], 'big')
        X1 = int.from_bytes(block[4:8], 'big')
        X2 = int.from_bytes(block[8:12], 'big')
        X3 = int.from_bytes(block[12:16], 'big')
        for i in range(0, 32, 4):
            X0 = X0 ^ SM4._T0(X1 ^ X2 ^ X3 ^ RK[31 - i])
            X1 = X1 ^ SM4._T0(X2 ^ X3 ^ X0 ^ RK[30 - i])
            X2 = X2 ^ SM4._T0(X3 ^ X0 ^ X1 ^ RK[29 - i])
            X3 = X3 ^ SM4._T0(X0 ^ X1 ^ X2 ^ RK[28 - i])
        BUFFER = self._block_buffer
        BUFFER.clear()
        BUFFER.extend(X3.to_bytes(4, 'big'))
        BUFFER.extend(X2.to_bytes(4, 'big'))
        BUFFER.extend(X1.to_bytes(4, 'big'))
        BUFFER.extend(X0.to_bytes(4, 'big'))
        return bytes(BUFFER)

    @classmethod
    def _make_t_tables(cls):
        S = cls._S_BOX
        def rol(x, n):
            return (x << n) & 0xFFFFFFFF | (x >> (32 - n))
        def L(y):
            return y ^ rol(y, 2) ^ rol(y, 10) ^ rol(y, 18) ^ rol(y, 24)
        T0 = [0] * 256; T1 = [0] * 256; T2 = [0] * 256; T3 = [0] * 256
        for i in range(256):
            s = S[i]
            T0[i] = L(s << 24)
            T1[i] = L(s << 16)
            T2[i] = L(s << 8)
            T3[i] = L(s)
        return (T0, T1, T2, T3)

    def _bulk(self, data: bytes, rk) -> bytes:
        n = len(data)
        out = bytearray(n)
        T0, T1, T2, T3 = self._T_TABLES
        unpack_from = struct.unpack_from
        pack_into = struct.pack_into
        idx = 0
        while idx < n:
            X0, X1, X2, X3 = unpack_from('>IIII', data, idx)
            for i in range(0, 32, 4):
                t = X1 ^ X2 ^ X3 ^ rk[i]
                X0 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X2 ^ X3 ^ X0 ^ rk[i + 1]
                X1 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X3 ^ X0 ^ X1 ^ rk[i + 2]
                X2 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
                t = X0 ^ X1 ^ X2 ^ rk[i + 3]
                X3 ^= T0[t >> 24] ^ T1[t >> 16 & 255] ^ T2[t >> 8 & 255] ^ T3[t & 255]
            pack_into('>IIII', out, idx, X3, X2, X1, X0)
            idx += 16
        return bytes(out)

    def encrypt_bulk(self, data: bytes) -> bytes:
        return self._bulk(data, self._rkey)

    def decrypt_bulk(self, data: bytes) -> bytes:
        return self._bulk(data, self._rkey[::-1])


# ==================== UTILITY CLASSES ====================

class Misc:
    @staticmethod
    def pad_to_n(data: bytes, n: int) -> bytes:
        assert n > 0
        padding = n - len(data) % n
        if padding == n:
            return data
        return data + b'\x00' * padding

    @staticmethod
    def align_up(x: int, n: int) -> int:
        return (x + n - 1) // n * n


class Reader:
    def __init__(self, buffer, cursor=0):
        self._buffer = buffer
        self._cursor = cursor

    def u1(self, move_cursor=True) -> int:
        return self.unpack('B', move_cursor=move_cursor)[0]

    def u4(self, move_cursor=True) -> int:
        return self.unpack('<I', move_cursor=move_cursor)[0]

    def u8(self, move_cursor=True) -> int:
        return self.unpack('<Q', move_cursor=move_cursor)[0]

    def i1(self, move_cursor=True) -> int:
        return self.unpack('b', move_cursor=move_cursor)[0]

    def i4(self, move_cursor=True) -> int:
        return self.unpack('<i', move_cursor=move_cursor)[0]

    def i8(self, move_cursor=True) -> int:
        return self.unpack('<q', move_cursor=move_cursor)[0]

    def s(self, n: int, move_cursor=True) -> bytes:
        return self.unpack(f'{n}s', move_cursor=move_cursor)[0]

    def unpack(self, f: str, offset=0, move_cursor=True):
        x = struct.unpack_from(f, self._buffer, self._cursor + offset)
        if move_cursor:
            self._cursor += struct.calcsize(f)
        return x

    def string(self, move_cursor=True) -> str:
        length = self.i4(move_cursor=move_cursor)
        if length == 0:
            return str()
        assert length > 0
        offset = 0 if move_cursor else 4
        return self.unpack(f'{length}s', offset=offset, move_cursor=move_cursor)[0].rstrip(b'\x00').decode()


# ==================== PAK INFO CLASSES ====================

class PakInfo:
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_index_encrypted(x: int) -> int:
            return (x ^ keystream[3]) & 255

        def decrypt_magic(x: int) -> int:
            return x ^ keystream[2]

        def decrypt_index_hash(x: bytes) -> bytes:
            key = struct.pack('<5I', *keystream[4:][:5])
            return bytes((a ^ b for a, b in zip(x, key)))

        def decrypt_index_size(x: int) -> int:
            return x ^ (keystream[10] << 32 | keystream[11])

        def decrypt_index_offset(x: int) -> int:
            return x ^ (keystream[0] << 32 | keystream[1])

        reader = Reader(buffer[-PakInfo._mem_size((-1)):])
        self.index_encrypted = decrypt_index_encrypted(reader.u1()) == 1
        self.magic = decrypt_magic(reader.u4())
        self.version = reader.u4()
        self.index_hash = decrypt_index_hash(reader.s(20)) if self.version >= 6 else bytes()
        self.index_size = decrypt_index_size(reader.u8())
        self.index_offset = decrypt_index_offset(reader.u8())
        if self.version <= 3:
            self.index_encrypted = False

    @staticmethod
    def _mem_size(_: int) -> int:
        return 45


class TencentPakInfo(PakInfo):
    def __init__(self, buffer, keystream: List[int]):
        def decrypt_unk(x: bytes) -> bytes:
            key = struct.pack('<8I', *keystream[7:][:8])
            return bytes((a ^ b for a, b in zip(x, key)))

        def decrypt_stem_hash(x: int) -> int:
            return x ^ keystream[8]

        def decrypt_unk_hash(x: int) -> int:
            return x ^ keystream[9]

        super().__init__(buffer, keystream)
        reader = Reader(buffer[-TencentPakInfo._mem_size(self.version):])
        self.unk1 = decrypt_unk(reader.s(32)) if self.version >= 7 else bytes()
        self.packed_key = reader.s(256) if self.version >= 8 else bytes()
        self.packed_iv = reader.s(256) if self.version >= 8 else bytes()
        self.packed_index_hash = reader.s(256) if self.version >= 8 else bytes()
        self.stem_hash = decrypt_stem_hash(reader.u4()) if self.version >= 9 else 0
        self.unk2 = decrypt_unk_hash(reader.u4()) if self.version >= 9 else 0
        self.content_org_hash = reader.s(20) if self.version >= 12 else bytes()

    @staticmethod
    def _mem_size(version: int) -> int:
        size_for_7 = 32 if version >= 7 else 0
        size_for_8 = 768 if version >= 8 else 0
        size_for_9 = 8 if version >= 9 else 0
        size_for_12 = 20 if version >= 12 else 0
        return PakInfo._mem_size(version) + size_for_7 + size_for_8 + size_for_9 + size_for_12


class PakCompressedBlock:
    def __init__(self, reader: Reader):
        self.start = reader.u8()
        self.end = reader.u8()


@dataclass
class TencentPakEntry:
    def __init__(self, reader: Reader, version: int):
        self.content_hash = reader.s(20)
        if version <= 1:
            _ = reader.u8()
        self.offset = reader.u8()
        self.uncompressed_size = reader.u8()
        self.compression_method = reader.u4() & CM_MASK
        self.size = reader.u8()
        self.unk1 = reader.u1() if version >= 5 else 0
        self.unk2 = reader.s(20) if version >= 5 else bytes()
        if self.compression_method != 0 and version >= 3:
            self.compressed_blocks = [PakCompressedBlock(reader) for _ in range(reader.u4())]
        else:
            self.compressed_blocks = []
        self.compression_block_size = reader.u4() if version >= 4 else 0
        self.encrypted = reader.u1() == 1 if version >= 4 else False
        self.encryption_method = reader.u4() if version >= 12 else 0
        self.index_new_sep = reader.u4() if version >= 12 else 0


# ==================== CRYPTO ====================

class PakCrypto:
    class _LCG:
        def __init__(self, seed: int):
            self.state = seed

        def next(self) -> int:
            MASK_32 = 4294967295
            MSB_1 = 2147483648

            def wrap(x: int) -> int:
                x &= MASK_32
                if not x & MSB_1:
                    return x
                return (x + MSB_1 & MASK_32) - MSB_1

            x1 = wrap(1103515245 * self.state)
            self.state = wrap(x1 + 12345)
            x2 = wrap(x1 + 77880) if self.state < 0 else self.state
            return (x2 >> 16 & MASK_32) % 32767

    @staticmethod
    def zuc_keystream() -> List[int]:
        if gmalg is None:
            raise ImportError("gmalg library required for ZUC keystream generation")
        zuc = gmalg.ZUC(ZUC_KEY, ZUC_IV)
        return [struct.unpack('>I', zuc.generate())[0] for _ in range(16)]

    @staticmethod
    def _xorxor(buffer, x) -> bytes:
        return bytes((buffer[i] ^ x[i % len(x)] for i in range(len(buffer))))

    @staticmethod
    def _hashhash(buffer, n: int) -> bytes:
        if SHA1 is None:
            raise ImportError("pycryptodome library required")
        result = bytes()
        for i in range(math.ceil(n / SHA1.digest_size)):
            result += SHA1.new(buffer).digest()
        if len(result) >= n:
            return result[:n]
        result += b'\x00' * (n - len(result))
        return result

    @staticmethod
    def _meowmeow(buffer) -> bytes:
        def unpad(x):
            skip = 1 + next((i for i in range(len(x)) if x[i] != 0))
            return x[skip:]

        if len(buffer) < 43:
            return bytes()
        x1 = buffer[1:][:SHA1.digest_size]
        x2 = buffer[SHA1.digest_size + 1:]
        x1 = PakCrypto._xorxor(x1, PakCrypto._hashhash(x2, len(x1)))
        x2 = PakCrypto._xorxor(x2, PakCrypto._hashhash(x1, len(x2)))
        part1, m = (x2[:SHA1.digest_size], x2[SHA1.digest_size:])
        if part1 != SHA1.new(b'\x00' * SHA1.digest_size).digest():
            return bytes()
        return unpad(m)

    @staticmethod
    def rsa_extract(signature: bytes, modulus: bytes) -> bytes:
        c = int.from_bytes(signature, 'little')
        n = int.from_bytes(modulus, 'little')
        e = 65537
        m = pow(c, e, n).to_bytes(256, 'little').rstrip(b'\x00')
        return PakCrypto._meowmeow(Misc.pad_to_n(m, 4))

    @staticmethod
    def _decrypt_simple1(ciphertext) -> bytes:
        return bytes((x ^ SIMPLE1_DECRYPT_KEY for x in ciphertext))

    @staticmethod
    def _decrypt_simple2(ciphertext) -> bytes:
        class RollingKey:
            def __init__(self, initial_value: int):
                self._value = initial_value

            def update(self, x: int) -> int:
                self._value ^= x
                return self._value

        assert len(ciphertext) % SIMPLE2_BLOCK_SIZE == 0
        initial_key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
        rolling_key = RollingKey(initial_key)
        plaintext = (struct.pack('<I', rolling_key.update(x)) for x in struct.unpack(f'<{len(ciphertext) // 4}I', ciphertext))
        return bytes(it.chain.from_iterable(plaintext))

    @staticmethod
    @lru_cache(maxsize=4096)
    def _derive_sm4_key(file_path: PurePath, encryption_method: int) -> bytes:
        part1 = file_path.stem.lower()
        if encryption_method == EM_SM4_2:
            secret = SM4_SECRET_2
        elif encryption_method == EM_SM4_4:
            secret = SM4_SECRET_4
        elif encryption_method == EM_UNKNOWN_17:
            index = (encryption_method - EM_SM4_NEW_BASE) % len(SM4_SECRET_NEW)
            secret = SM4_SECRET_NEW[index]
        else:
            index = (encryption_method - EM_SM4_NEW_BASE) % len(SM4_SECRET_NEW)
            secret = f'{SM4_SECRET_NEW[index]}{encryption_method}'
        return SHA1.new(str(part1 + secret).encode()).digest()[:SM4.key_length()]

    @staticmethod
    @lru_cache(maxsize=4096)
    def _sm4_context_for_key(key: bytes) -> SM4:
        return SM4(key)

    @staticmethod
    def _decrypt_sm4(ciphertext, file_path: PurePath, encryption_method: int) -> bytes:
        assert len(ciphertext) % SM4.block_length() == 0
        key = PakCrypto._derive_sm4_key(file_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        return sm4.decrypt_bulk(ciphertext)

    @staticmethod
    def decrypt_index(ciphertext, pak_info: TencentPakInfo) -> bytes:
        if pak_info.version > 7:
            if AES is None:
                raise ImportError("pycryptodome library required for AES decryption")
            key = PakCrypto.rsa_extract(pak_info.packed_key, RSA_MOD_1)
            iv = PakCrypto.rsa_extract(pak_info.packed_iv, RSA_MOD_1)
            assert len(key) == 32 and len(iv) == 32
            aes = AES.new(key, MODE_CBC, iv[:16])
            return unpad(aes.decrypt(ciphertext), AES.block_size)
        return bytes(PakCrypto._decrypt_simple1(ciphertext))

    @staticmethod
    def _is_simple1_method(encryption_method: int) -> bool:
        return encryption_method == EM_SIMPLE1

    @staticmethod
    def _is_simple2_method(encryption_method: int) -> bool:
        return encryption_method == EM_SIMPLE2

    @staticmethod
    def _is_sm4_method(encryption_method: int) -> bool:
        return (encryption_method == EM_SM4_2 or encryption_method == EM_SM4_4 or
                encryption_method == EM_UNKNOWN_17 or encryption_method & EM_SM4_NEW_MASK != 0)

    @staticmethod
    def align_encrypted_content_size(n: int, encryption_method: int) -> int:
        if PakCrypto._is_simple2_method(encryption_method):
            return Misc.align_up(n, SIMPLE2_BLOCK_SIZE)
        if PakCrypto._is_sm4_method(encryption_method):
            return Misc.align_up(n, SM4.block_length())
        return n

    @staticmethod
    def decrypt_block(ciphertext, file: PurePath, encryption_method: int) -> bytes:
        if PakCrypto._is_simple1_method(encryption_method):
            return PakCrypto._decrypt_simple1(ciphertext)
        if PakCrypto._is_simple2_method(encryption_method):
            return PakCrypto._decrypt_simple2(ciphertext)
        if PakCrypto._is_sm4_method(encryption_method):
            return PakCrypto._decrypt_sm4(ciphertext, file, encryption_method)
        raise ValueError(f'Unknown encryption method: {encryption_method}')

    @staticmethod
    @lru_cache(maxsize=33)
    def generate_block_indices(n: int, encryption_method: int) -> List[int]:
        if not PakCrypto._is_sm4_method(encryption_method):
            return list(range(n))
        permutation = []
        lcg = PakCrypto._LCG(n)
        while len(permutation) != n:
            x = lcg.next() % n
            if x not in permutation:
                permutation.append(x)
        inverse = [0] * len(permutation)
        for i, x in enumerate(permutation):
            inverse[x] = i
        return inverse


# ==================== COMPRESSION ====================

class PakCompression:
    @staticmethod
    @lru_cache(maxsize=33)
    def _zstd_decompressor(dict: ZstdCompressionDict) -> ZstdDecompressor:
        return ZstdDecompressor(dict)

    @staticmethod
    def zstd_dictionary(dict_data) -> ZstdCompressionDict:
        return ZstdCompressionDict(dict_data, DICT_TYPE_AUTO)

    @staticmethod
    def decompress_block(block, dict: Optional[ZstdCompressionDict], compression_method: int) -> bytes:
        if compression_method == CM_ZLIB:
            try:
                return zlib.decompress(block)
            except zlib.error:
                return block
        if compression_method in (CM_ZSTD, CM_ZSTD_DICT):
            if compression_method != CM_ZSTD_DICT:
                dict = None
            return PakCompression._zstd_decompressor(dict).decompress(block)
        raise ValueError(f'Unknown compression method: {compression_method}')


# ==================== TENCENT PAK FILE ====================

class TencentPakFile:
    def __init__(self, file_path: PurePath, is_od=False):
        self._file_path = file_path
        with open(file_path, 'rb') as file:
            self._file_content = memoryview(file.read())
        self._is_od = is_od
        self._mount_point = PurePath()
        self._is_zstd_with_dict = 'zsdic' in str(self._file_path)
        self._zstd_dict = None
        self._zstd_dict_entry = None
        self._files = []
        self._index = {}
        self._pak_info = TencentPakInfo(self._file_content, PakCrypto.zuc_keystream())
        self._verify_stem_hash()
        self._tencent_load_index()

    def _verify_stem_hash(self) -> None:
        if not self._is_od and self._pak_info.version >= 9:
            try:
                assert self._pak_info.stem_hash == zlib.crc32(self._file_path.stem.encode('utf-32le'))
            except AssertionError:
                pass

    def _tencent_load_index(self) -> None:
        index_data = self._file_content[self._pak_info.index_offset:][:self._pak_info.index_size]
        if self._pak_info.index_encrypted:
            index_data = PakCrypto.decrypt_index(index_data, self._pak_info)
        self._verify_index_hash(index_data)
        self._load_index(index_data)

    def _verify_index_hash(self, index_data) -> None:
        expected_hash = self._pak_info.index_hash
        if not self._is_od and self._pak_info.version >= 8:
            if expected_hash != PakCrypto.rsa_extract(self._pak_info.packed_index_hash, RSA_MOD_2):
                pass
        assert expected_hash == SHA1.new(index_data).digest()

    @staticmethod
    def _construct_mount_point(mount_point: str) -> PurePath:
        result = PurePath()
        for part in PurePath(mount_point).parts:
            if part != '..':
                result /= part
        return result

    def _peek_content(self, offset: int, size: int, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(size, encryption_method)
        return self._file_content[offset:][:size]

    def _peek_block_content(self, block: PakCompressedBlock, encryption_method: int) -> memoryview:
        size = PakCrypto.align_encrypted_content_size(block.end - block.start, encryption_method)
        return self._file_content[block.start:][:size]

    def _construct_zstd_dict(self, dict_entry: TencentPakEntry) -> None:
        assert not self._zstd_dict
        assert not dict_entry.encrypted
        assert dict_entry.compression_method == CM_NONE
        reader = Reader(self._peek_content(dict_entry.offset, dict_entry.size, 0))
        dict_size = reader.u8()
        _ = reader.u4()
        assert dict_size == reader.u4()
        dict_data = reader.s(dict_size)
        self._zstd_dict = PakCompression.zstd_dictionary(dict_data)

    def _load_index(self, index_data) -> None:
        if self._pak_info.version <= 10:
            raise ValueError(f'Unsupported version: {self._pak_info.version}')
        reader = Reader(index_data)
        self._mount_point = self._construct_mount_point(reader.string())
        self._files = [TencentPakEntry(reader, self._pak_info.version) for _ in range(reader.u4())]
        for _ in range(reader.u8()):
            dir_path = PurePath(reader.string())
            e = {reader.string(): self._files[~reader.i4()] for _ in range(reader.u8())}
            if self._is_zstd_with_dict and dir_path.name == 'zstddic':
                assert len(e) == 1
                self._zstd_dict_entry = e[[*e.keys()][0]]
                self._construct_zstd_dict(self._zstd_dict_entry)
            else:
                self._index.update({PurePath(dir_path): e})

    def _write_to_disk(self, file_path: Path, entry: TencentPakEntry) -> None:
        encryption_method = entry.encryption_method
        compression_method = entry.compression_method

        if entry.encrypted and encryption_method == EM_UNKNOWN_17:
            self._dump_raw_unsupported_17(file_path, entry)
            return

        if entry.encrypted and entry.compression_method != CM_NONE and PakCrypto._is_sm4_method(encryption_method):
            try:
                if entry.compressed_blocks:
                    probe_idx = next(iter(PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method)))
                    probe = bytes(self._peek_block_content(entry.compressed_blocks[probe_idx], encryption_method))
                    probe = PakCrypto.decrypt_block(probe, file_path, encryption_method)
                    if not self._decrypted_looks_valid(bytes(probe), compression_method):
                        raise ValueError(f'Decrypt probe failed (wrong SM4 key for Type {encryption_method})')
            except Exception:
                with open(file_path, 'wb') as _f:
                    raw = bytearray()
                    for blk in entry.compressed_blocks:
                        raw += bytes(self._peek_block_content(blk, encryption_method))
                    _f.write(raw)
                return

        with open(file_path, 'wb') as file:
            if compression_method == CM_NONE:
                data = self._peek_content(entry.offset, entry.size, encryption_method)
                if entry.encrypted:
                    data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                data = bytes(data)
                if entry.uncompressed_size and len(data) > entry.uncompressed_size:
                    data = data[:entry.uncompressed_size]
                file.write(data)
                return
            else:
                try:
                    for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), encryption_method):
                        data = self._peek_block_content(entry.compressed_blocks[x], encryption_method)
                        if entry.encrypted:
                            data = PakCrypto.decrypt_block(data, file_path, encryption_method)
                        data = PakCompression.decompress_block(data, self._zstd_dict, compression_method)
                        file.write(data)
                except Exception:
                    file.seek(0)
                    file.truncate()
                    raw = bytearray()
                    for blk in entry.compressed_blocks:
                        raw += self._peek_block_content(blk, encryption_method)
                    file.write(raw)

    @staticmethod
    def _decrypted_looks_valid(data: bytes, compression_method: int) -> bool:
        if compression_method == CM_ZLIB:
            return len(data) >= 2 and data[0] == 0x78 and data[1] in (0x01, 0x9C, 0xDA)
        if compression_method in (CM_ZSTD, CM_ZSTD_DICT):
            return bytes(data[:4]) == b'\x28\xb5\x2f\xfd'
        return True

    def _dump_raw_unsupported_17(self, file_path: Path, entry: TencentPakEntry) -> None:
        with open(file_path, 'wb') as file:
            if entry.compression_method == CM_NONE:
                file.write(bytes(self._peek_content(entry.offset, entry.size, entry.encryption_method)))
            else:
                for blk in entry.compressed_blocks:
                    file.write(bytes(self._file_content[blk.start:blk.end]))

    def dump(self, out_path: Path, progress_callback=None) -> None:
        out_path = out_path / self._mount_point
        out_path.mkdir(parents=True, exist_ok=True)
        total_files = sum(len(d) for d in self._index.values())
        processed = 0
        for dir_path, dir_content in self._index.items():
            current_out_path = out_path / dir_path
            current_out_path.mkdir(parents=True, exist_ok=True)
            for file_name, entry in dir_content.items():
                self._write_to_disk(current_out_path / file_name, entry)
                processed += 1
                if progress_callback:
                    progress_callback(processed, total_files, file_name)


# ==================== HELPER FUNCTIONS ====================

def build_fullpath_entry_map(pak_file) -> Dict[str, Any]:
    m = {}
    for dir_path, files in pak_file._index.items():
        for name, entry in files.items():
            full = str(PurePath(dir_path) / name).replace("\\", "/").lstrip("/")
            if full.startswith("./"):
                full = full[2:]
            m[full] = entry
    return m


def _get_all_dirs_and_mp(pak_file):
    raw = bytes(pak_file._file_content[
        pak_file._pak_info.index_offset:][:pak_file._pak_info.index_size])
    if pak_file._pak_info.index_encrypted:
        raw = PakCrypto.decrypt_index(raw, pak_file._pak_info)
    r = Reader(raw)
    mp = r.string()
    num_files = r.u4()
    for _ in range(num_files):
        TencentPakEntry(r, pak_file._pak_info.version)
    dirs = {}
    for _ in range(r.u8()):
        dp = r.string()
        cnt = r.u8()
        dirs[dp] = {r.string(): pak_file._files[~r.i4()] for _ in range(cnt)}
    return mp, dirs


def _normalize_dir_key(path_str):
    s = str(path_str).replace('\\', '/').strip('/')
    return (s + '/') if s else ''


def _find_existing_dir(all_dirs, want_dir):
    want = _normalize_dir_key(want_dir).strip('/').lower()
    if not want:
        return ''
    for k in all_dirs:
        if k.strip('/').lower() == want:
            return k
    best = None
    for k in all_dirs:
        key = k.strip('/').lower()
        if key and want.endswith('/' + key):
            if best is None or len(key) > len(best):
                best = k
    return best


def _strip_mount_prefix(pak_file, rel_dir):
    mp = str(pak_file._mount_point).replace('\\', '/').strip('/')
    rd = str(rel_dir).replace('\\', '/').strip('/')
    if mp and (rd.lower() == mp.lower() or rd.lower().startswith(mp.lower() + '/')):
        return rd[len(mp):].lstrip('/')
    return rd


def _pick_template(pak_file, all_dirs, target_dir, file_name):
    ext = Path(file_name).suffix.lower()
    if target_dir in all_dirs:
        for name, e in all_dirs[target_dir].items():
            if Path(name).suffix.lower() == ext:
                return e
    for dp, files in all_dirs.items():
        for name, e in files.items():
            if Path(name).suffix.lower() == ext:
                return e
    for dp, files in all_dirs.items():
        for name, e in files.items():
            return e
    return pak_file._files[0] if pak_file._files else None


def _default_compression(pak_file):
    cm_counter = {}
    for e in pak_file._files:
        cm = e.compression_method
        if cm in (CM_ZLIB, CM_ZSTD, CM_ZSTD_DICT):
            cm_counter[cm] = cm_counter.get(cm, 0) + 1
    if pak_file._is_zstd_with_dict and cm_counter.get(CM_ZSTD_DICT, 0):
        return CM_ZSTD_DICT
    if cm_counter.get(CM_ZSTD, 0):
        return CM_ZSTD
    if cm_counter.get(CM_ZSTD_DICT, 0):
        return CM_ZSTD
    return CM_ZLIB


def _write_entry_content(out_buf, ne, plaintext, pak_rel, zstd_dict, fast=False):
    if ne.compression_method == CM_NONE:
        cipher = (_encrypt_plaintext(plaintext, pak_rel, ne.encryption_method)
                  if ne.encrypted else plaintext)
        ne.offset = len(out_buf)
        ne.size = len(plaintext)
        ne.uncompressed_size = len(plaintext)
        out_buf += cipher
        return
    cs = ne.compression_block_size if ne.compression_block_size > 0 else 65536
    chunks = [plaintext[i:i + cs] for i in range(0, len(plaintext), cs)]
    if not chunks:
        ne.compressed_blocks = []
        ne.offset = len(out_buf)
        ne.size = 0
        ne.uncompressed_size = 0
        return
    n = len(chunks)
    inv = PakCrypto.generate_block_indices(n, ne.encryption_method) if ne.encrypted else list(range(n))
    file_order = [0] * n
    for j in range(n):
        file_order[inv[j]] = j
    new_blks = [None] * n
    for k in range(n):
        chunk = chunks[file_order[k]]
        compressed = _best_compress(chunk, ne.compression_method, zstd_dict, fast=fast)
        cipher = (_encrypt_plaintext(compressed, pak_rel, ne.encryption_method)
                  if ne.encrypted else compressed)
        blk = PakCompressedBlock.__new__(PakCompressedBlock)
        blk.start = len(out_buf)
        blk.end = blk.start + len(cipher)
        out_buf += cipher
        new_blks[k] = blk
    ne.compressed_blocks = new_blks
    ne.offset = new_blks[0].start
    ne.size = sum(b.end - b.start for b in new_blks)
    ne.uncompressed_size = len(plaintext)


def _extract_entry_plaintext(pak_file, entry, full_path):
    em = entry.encryption_method
    cm = entry.compression_method
    path = PurePath(full_path)
    if cm == CM_NONE:
        data = pak_file._peek_content(entry.offset, entry.size, em)
        if entry.encrypted:
            data = PakCrypto.decrypt_block(data, path, em)
        return bytes(data[:entry.uncompressed_size])
    out = bytearray()
    for x in PakCrypto.generate_block_indices(len(entry.compressed_blocks), em):
        data = pak_file._peek_block_content(entry.compressed_blocks[x], em)
        if entry.encrypted:
            data = PakCrypto.decrypt_block(data, path, em)
        out += PakCompression.decompress_block(data, pak_file._zstd_dict, cm)
    return bytes(out)


def _copy_original_content(out_buf, pak_file, ne, old_entry):
    em = old_entry.encryption_method
    if old_entry.compression_method == CM_NONE:
        read_sz = (PakCrypto.align_encrypted_content_size(old_entry.size, em)
                   if old_entry.encrypted else old_entry.size)
        ne.offset = len(out_buf)
        out_buf += bytes(pak_file._file_content[old_entry.offset: old_entry.offset + read_sz])
    elif old_entry.compressed_blocks:
        new_blks = []
        for ob in old_entry.compressed_blocks:
            unc = ob.end - ob.start
            enc = (PakCrypto.align_encrypted_content_size(unc, em)
                   if old_entry.encrypted else unc)
            nb = PakCompressedBlock.__new__(PakCompressedBlock)
            nb.start = len(out_buf)
            nb.end = nb.start + unc
            out_buf += bytes(pak_file._file_content[ob.start: ob.start + enc])
            new_blks.append(nb)
        ne.compressed_blocks = new_blks
        ne.offset = new_blks[0].start
    ne.encryption_method = old_entry.encryption_method
    ne.encrypted = old_entry.encrypted


def _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path):
    version = pak_file._pak_info.version
    keystream = PakCrypto.zuc_keystream()
    eidx = {id(new_files[i]): i for i in range(len(new_files))}
    old_id_to_new_idx = {id(pak_file._files[i]): i for i in range(len(pak_file._files))}
    idx = bytearray(_pw_string(mp_str))
    idx += struct.pack('<I', len(new_files))
    for ne in new_files:
        idx += _pw_entry(ne, version)
    idx += struct.pack('<Q', len(all_dirs))
    for dp_str, dir_files in all_dirs.items():
        idx += _pw_string(dp_str)
        idx += struct.pack('<Q', len(dir_files))
        for name, old_e in dir_files.items():
            idx += _pw_string(name)
            found_idx = eidx.get(id(old_e))
            if found_idx is None:
                found_idx = old_id_to_new_idx.get(id(old_e))
            if found_idx is None:
                copy_of = next((k for k, v in old_to_new.items() if v is old_e), None)
                if copy_of is not None:
                    found_idx = eidx.get(id(old_to_new[copy_of]))
            if found_idx is None:
                for i, e in enumerate(new_files):
                    if e.offset == old_e.offset and e.size == old_e.size:
                        found_idx = i
                        break
            idx += struct.pack('<i', ~found_idx if found_idx is not None else -1)
    index_plain = bytes(idx)
    new_sha1 = SHA1.new(index_plain).digest()
    if pak_file._pak_info.index_encrypted:
        key = PakCrypto.rsa_extract(pak_file._pak_info.packed_key, RSA_MOD_1)
        iv = PakCrypto.rsa_extract(pak_file._pak_info.packed_iv, RSA_MOD_1)
        aes = AES.new(key, MODE_CBC, iv[:16])
        pad = (-len(index_plain)) % AES.block_size or AES.block_size
        index_bytes = aes.encrypt(index_plain + bytes([pad] * pad))
    else:
        index_bytes = index_plain
    new_idx_offset = len(out_buf)
    new_idx_size = len(index_bytes)
    out_buf += index_bytes
    footer_sz = TencentPakInfo._mem_size(version)
    new_footer = bytearray(pak_file._file_content[-footer_sz:])
    h_key = struct.pack('<5I', *keystream[4:9])
    new_footer[-36:-16] = bytes(a ^ b for a, b in zip(new_sha1, h_key))
    new_footer[-16:-8] = ((new_idx_size ^ (keystream[10] << 32 | keystream[11])).to_bytes(8, 'little'))
    new_footer[-8:] = ((new_idx_offset ^ (keystream[0] << 32 | keystream[1])).to_bytes(8, 'little'))
    out_buf += new_footer
    with open(output_path, 'wb') as f:
        f.write(out_buf)


def _pw_string(s):
    if not s:
        return struct.pack('<i', 0)
    b = s.encode('utf-8') + b'\x00'
    return struct.pack('<i', len(b)) + b


def _pw_entry(e, v):
    w = bytearray(e.content_hash)
    w += struct.pack('<Q', e.offset)
    w += struct.pack('<Q', e.uncompressed_size)
    w += struct.pack('<I', e.compression_method)
    w += struct.pack('<Q', e.size)
    if v >= 5:
        w += bytes([e.unk1])
        w += e.unk2
    if e.compression_method != CM_NONE and v >= 3:
        w += struct.pack('<I', len(e.compressed_blocks))
        for b in e.compressed_blocks:
            w += struct.pack('<QQ', b.start, b.end)
    if v >= 4:
        w += struct.pack('<I', e.compression_block_size)
        w += bytes([1 if e.encrypted else 0])
    if v >= 12:
        w += struct.pack('<II', e.encryption_method, e.index_new_sep)
    return bytes(w)


def _best_compress(chunk, cm, zstd_dict=None, fast=False):
    if cm == CM_ZLIB:
        return zlib.compress(chunk, 1 if fast else 9)
    if cm in (CM_ZSTD, CM_ZSTD_DICT):
        zd = zstd_dict if cm == CM_ZSTD_DICT else None
        levels = [6, 3, 1] if fast else [22, 19, 16, 13, 10, 7, 4, 1]
        for lvl in levels:
            try:
                return ZstdCompressor(level=lvl, dict_data=zd, threads=1).compress(chunk)
            except Exception:
                continue
    return chunk


def _encrypt_plaintext(plaintext: bytes, pak_relative_path: PurePath, encryption_method: int) -> bytes:
    if PakCrypto._is_simple1_method(encryption_method):
        return bytes((b ^ SIMPLE1_DECRYPT_KEY for b in plaintext))
    if PakCrypto._is_simple2_method(encryption_method):
        pad = -len(plaintext) % SIMPLE2_BLOCK_SIZE
        plaintext += b'\x00' * pad
        key, = struct.unpack('<I', SIMPLE2_DECRYPT_KEY)
        rolling = key
        out = []
        for x, in struct.iter_unpack('<I', plaintext):
            c = rolling ^ x
            out.append(c)
            rolling ^= c
        return struct.pack(f'<{len(out)}I', *out)
    if PakCrypto._is_sm4_method(encryption_method):
        key = PakCrypto._derive_sm4_key(pak_relative_path, encryption_method)
        sm4 = PakCrypto._sm4_context_for_key(key)
        pad_len = -len(plaintext) % 16
        if pad_len > 0:
            plaintext = plaintext + b'\x00' * pad_len
        return sm4.encrypt_bulk(plaintext)
    return plaintext


def inject_edit_files(pak_file, edit_root, output_path, protect_new=False, sm4_type=47):
    import copy as _cp
    version = pak_file._pak_info.version
    if version < 12:
        raise ValueError(f'Unsupported pak version: {version} (need >= 12)')

    edit_files = [p for p in Path(edit_root).rglob('*') if p.is_file()]
    if not edit_files:
        raise ValueError(f'No files found in EDIT folder: {edit_root}')

    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)

    injections = {}
    for p in edit_files:
        rel = p.relative_to(edit_root)
        parts = rel.parts
        file_name = parts[-1]
        rel_dir = '/'.join(parts[:-1]).replace('\\', '/')
        rel_dir = _strip_mount_prefix(pak_file, rel_dir)
        target_dir = _find_existing_dir(all_dirs, rel_dir) if rel_dir.strip('/') else ''
        if target_dir is None:
            target_dir = _normalize_dir_key(rel_dir)
        existing = None
        if target_dir in all_dirs:
            for name, e in list(all_dirs[target_dir].items()):
                if name.lower() == file_name.lower():
                    existing = (name, e)
                    break
        if existing:
            full_path = target_dir + existing[0]
            injections[full_path] = (p, existing[1], False)
        else:
            full_path = target_dir + file_name
            template = _pick_template(pak_file, all_dirs, target_dir, file_name)
            injections[full_path] = (p, template, True)

    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)
    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}

    out_buf = bytearray()
    edited_count = 0
    new_count = 0

    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str) / name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne

            if full_path in injections:
                p, template, is_new = injections[full_path]
                new_raw = p.read_bytes()
                pak_rel = PurePath(full_path)
                ne.content_hash = SHA1.new(new_raw).digest()
                ne.uncompressed_size = len(new_raw)
                if is_new:
                    ne.compression_method = _default_compression(pak_file)
                    if protect_new:
                        ne.encryption_method = sm4_type
                        ne.encrypted = True
                    else:
                        ne.encryption_method = template.encryption_method if template else 0
                        ne.encrypted = template.encrypted if template else False
                    ne.unk1 = template.unk1 if template else 0
                    ne.compression_block_size = (template.compression_block_size if template
                                                 and template.compression_block_size > 0 else 65536)
                    ne.index_new_sep = template.index_new_sep if template else 0
                    new_count += 1
                else:
                    ne.compression_method = old_entry.compression_method
                    if protect_new:
                        ne.encryption_method = sm4_type
                        ne.encrypted = True
                    else:
                        ne.encryption_method = old_entry.encryption_method
                        ne.encrypted = old_entry.encrypted
                    ne.unk1 = old_entry.unk1
                    ne.compression_block_size = (old_entry.compression_block_size
                                                 if old_entry.compression_block_size > 0 else 65536)
                    ne.index_new_sep = old_entry.index_new_sep
                    edited_count += 1
                ne.unk2 = SHA1.new((mp_str + full_path).lower().encode('utf-8')).digest()
                _write_entry_content(out_buf, ne, new_raw, pak_rel, pak_file._zstd_dict)
            else:
                _copy_original_content(out_buf, pak_file, ne, old_entry)

    for full_path, (p, template, is_new) in injections.items():
        if not is_new:
            continue
        already = False
        for dp_str, dir_files in all_dirs.items():
            for name, entry in dir_files.items():
                if str(PurePath(dp_str) / name).replace('\\', '/') == full_path:
                    already = True
                    break
            if already:
                break
        if already:
            continue
        ne = _cp.copy(template) if template else None
        if ne is None:
            ne = TencentPakEntry(Reader(b''), version)
            ne.compression_method = CM_NONE
            ne.encrypted = False
        else:
            ne.compressed_blocks = [_cp.copy(b) for b in template.compressed_blocks]
        new_raw = p.read_bytes()
        pak_rel = PurePath(full_path)
        ne.content_hash = SHA1.new(new_raw).digest()
        ne.uncompressed_size = len(new_raw)
        ne.compression_method = _default_compression(pak_file)
        if protect_new:
            ne.encryption_method = sm4_type
            ne.encrypted = True
        else:
            ne.encryption_method = template.encryption_method if template else 0
            ne.encrypted = template.encrypted if template else False
        ne.unk1 = template.unk1 if template else 0
        ne.compression_block_size = (template.compression_block_size if template
                                     and template.compression_block_size > 0 else 65536)
        ne.index_new_sep = template.index_new_sep if template else 0
        ne.unk2 = SHA1.new((mp_str + full_path).lower().encode('utf-8')).digest()
        _write_entry_content(out_buf, ne, new_raw, pak_rel, pak_file._zstd_dict)
        new_files.append(ne)
        old_to_new[id(ne)] = ne
        dp_key = full_path.rsplit('/', 1)[0] + '/' if '/' in full_path else ''
        all_dirs.setdefault(dp_key, {})[full_path.rsplit('/', 1)[-1]] = ne
        new_count += 1

    _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path)
    return edited_count, new_count


def protect_pak_file(pak_file, output_path, sm4_type=47, progress_callback=None):
    import copy as _cp
    version = pak_file._pak_info.version
    if version < 12:
        raise ValueError(f'Unsupported pak version: {version} (need >= 12)')

    mp_str, all_dirs = _get_all_dirs_and_mp(pak_file)
    new_files = []
    for e in pak_file._files:
        ne = _cp.copy(e)
        ne.compressed_blocks = [_cp.copy(b) for b in e.compressed_blocks]
        new_files.append(ne)
    old_to_new = {id(pak_file._files[i]): new_files[i] for i in range(len(pak_file._files))}

    out_buf = bytearray()
    protected = 0
    skipped = 0
    total = sum(len(d) for d in all_dirs.values())
    processed = 0

    for dp_str, dir_files in list(all_dirs.items()):
        for name, old_entry in list(dir_files.items()):
            full_path = str(PurePath(dp_str) / name).replace('\\', '/')
            ne = old_to_new.get(id(old_entry), None)
            if ne is None:
                ne = _cp.copy(old_entry)
                ne.compressed_blocks = [_cp.copy(b) for b in old_entry.compressed_blocks]
                new_files.append(ne)
                old_to_new[id(old_entry)] = ne

            is_marker = (old_entry.compression_method == CM_NONE and old_entry.size == 0)
            is_zdict = (pak_file._zstd_dict_entry is not None and old_entry is pak_file._zstd_dict_entry)
            if is_marker or is_zdict:
                _copy_original_content(out_buf, pak_file, ne, old_entry)
                skipped += 1
                processed += 1
                if progress_callback:
                    progress_callback(processed, total, name)
                continue

            try:
                plaintext = _extract_entry_plaintext(pak_file, old_entry, full_path)
            except Exception:
                _copy_original_content(out_buf, pak_file, ne, old_entry)
                skipped += 1
                processed += 1
                if progress_callback:
                    progress_callback(processed, total, name)
                continue
            ne.compression_method = old_entry.compression_method
            if ne.compression_method == CM_NONE:
                ne.compression_method = CM_ZLIB
            ne.encryption_method = sm4_type
            ne.encrypted = True
            ne.unk1 = old_entry.unk1
            ne.unk2 = old_entry.unk2
            ne.index_new_sep = old_entry.index_new_sep
            ne.compression_block_size = (old_entry.compression_block_size
                                         if old_entry.compression_block_size > 0 else 65536)
            _write_entry_content(out_buf, ne, plaintext, PurePath(full_path), pak_file._zstd_dict, fast=True)
            protected += 1
            processed += 1
            if progress_callback:
                progress_callback(processed, total, name)

    _write_pak_index_footer(pak_file, mp_str, all_dirs, new_files, old_to_new, out_buf, output_path)
    return protected, skipped


# ==================== FLET GUI APPLICATION ====================

class PAKToolApp:
    def __init__(self, page: ft.Page):
        self.page = page
        self.page.title = "PAK Tool - PUBG Mobile PAK Manager"
        self.page.theme_mode = ft.ThemeMode.DARK
        self.page.padding = 20
        self.page.window_width = 1000
        self.page.window_height = 750
        self.page.window_min_width = 800
        self.page.window_min_height = 600

        # State variables
        self.pak_path = None
        self.edit_dir = None
        self.output_path = None
        self.is_processing = False

        # UI Components
        self.pak_path_field = ft.TextField(
            label="PAK File Path",
            hint_text="Select or enter the path to your .pak file",
            expand=True,
            read_only=True,
        )
        self.edit_dir_field = ft.TextField(
            label="Edit Directory",
            hint_text="Select directory containing edited files",
            expand=True,
            read_only=True,
        )
        self.output_field = ft.TextField(
            label="Output Path",
            hint_text="Output PAK file path (auto-generated if empty)",
            expand=True,
        )

        self.sm4_type_field = ft.TextField(
            label="SM4 Type",
            value="47",
            width=120,
            hint_text="47",
        )

        self.encrypt_switch = ft.Switch(
            label="Encrypt injected files with SM4",
            value=True,
        )

        self.progress_bar = ft.ProgressBar(
            width=None,
            visible=False,
            bar_color=ft.Colors.BLUE_400,
        )
        self.progress_text = ft.Text(
            "",
            visible=False,
            size=12,
            color=ft.Colors.GREY_400,
        )

        self.status_text = ft.Text(
            "Ready",
            size=14,
            color=ft.Colors.GREEN_400,
        )

        self.log_container = ft.Column(
            scroll=ft.ScrollMode.AUTO,
            expand=True,
            spacing=5,
        )

        # File pickers
        self.pak_file_picker = ft.FilePicker(on_result=self._on_pak_file_picked)
        self.dir_picker = ft.FilePicker(on_result=self._on_dir_picked)
        self.save_file_picker = ft.FilePicker(on_result=self._on_save_file_picked)

        self.page.overlay.extend([
            self.pak_file_picker,
            self.dir_picker,
            self.save_file_picker,
        ])

        self._build_ui()

    def _build_ui(self):
        # Header
        header = ft.Container(
            content=ft.Column([
                ft.Text("PAK Tool", size=32, weight=ft.FontWeight.BOLD, color=ft.Colors.BLUE_300),
                ft.Text("PUBG Mobile PAK file manipulation tool", size=14, color=ft.Colors.GREY_400),
            ]),
            margin=ft.margin.only(bottom=20),
        )

        # File selection section
        file_section = ft.Card(
            content=ft.Container(
                content=ft.Column([
                    ft.Text("File Selection", size=18, weight=ft.FontWeight.BOLD),
                    ft.Divider(),
                    ft.Row([
                        self.pak_path_field,
                        ft.ElevatedButton(
                            "Browse PAK",
                            icon=ft.Icons.FOLDER_OPEN,
                            on_click=lambda _: self.pak_file_picker.pick_files(
                                allowed_extensions=["pak"],
                                dialog_title="Select PAK file",
                            ),
                        ),
                    ]),
                    ft.Row([
                        self.edit_dir_field,
                        ft.ElevatedButton(
                            "Browse Edit Dir",
                            icon=ft.Icons.FOLDER_OPEN,
                            on_click=lambda _: self.dir_picker.get_directory_path(
                                dialog_title="Select edit directory",
                            ),
                        ),
                    ]),
                    ft.Row([
                        self.output_field,
                        ft.ElevatedButton(
                            "Browse Output",
                            icon=ft.Icons.SAVE_AS,
                            on_click=lambda _: self.save_file_picker.save_file(
                                allowed_extensions=["pak"],
                                dialog_title="Save output PAK as",
                            ),
                        ),
                    ]),
                ]),
                padding=15,
            ),
        )

        # Options section
        options_section = ft.Card(
            content=ft.Container(
                content=ft.Column([
                    ft.Text("Options", size=18, weight=ft.FontWeight.BOLD),
                    ft.Divider(),
                    ft.Row([
                        self.sm4_type_field,
                        self.encrypt_switch,
                    ]),
                ]),
                padding=15,
            ),
        )

        # Action buttons
        actions_section = ft.Card(
            content=ft.Container(
                content=ft.Column([
                    ft.Text("Actions", size=18, weight=ft.FontWeight.BOLD),
                    ft.Divider(),
                    ft.Row([
                        ft.ElevatedButton(
                            "Unpack",
                            icon=ft.Icons.UNARCHIVE,
                            on_click=self._on_unpack,
                            style=ft.ButtonStyle(bgcolor=ft.Colors.BLUE_700),
                            width=140,
                        ),
                        ft.ElevatedButton(
                            "Repack",
                            icon=ft.Icons.ARCHIVE,
                            on_click=self._on_repack,
                            style=ft.ButtonStyle(bgcolor=ft.Colors.GREEN_700),
                            width=140,
                        ),
                        ft.ElevatedButton(
                            "Inject",
                            icon=ft.Icons.ADD_CIRCLE,
                            on_click=self._on_inject,
                            style=ft.ButtonStyle(bgcolor=ft.Colors.ORANGE_700),
                            width=140,
                        ),
                        ft.ElevatedButton(
                            "Protect",
                            icon=ft.Icons.SECURITY,
                            on_click=self._on_protect,
                            style=ft.ButtonStyle(bgcolor=ft.Colors.PURPLE_700),
                            width=140,
                        ),
                    ], wrap=True),
                    ft.Row([
                        ft.ElevatedButton(
                            "Info",
                            icon=ft.Icons.INFO,
                            on_click=self._on_info,
                            width=140,
                        ),
                        ft.ElevatedButton(
                            "List Files",
                            icon=ft.Icons.LIST,
                            on_click=self._on_list,
                            width=140,
                        ),
                        ft.ElevatedButton(
                            "Clear Log",
                            icon=ft.Icons.CLEAR,
                            on_click=self._on_clear_log,
                            width=140,
                        ),
                    ], wrap=True),
                ]),
                padding=15,
            ),
        )

        # Progress section
        progress_section = ft.Container(
            content=ft.Column([
                self.progress_bar,
                self.progress_text,
            ]),
            margin=ft.margin.only(top=10, bottom=10),
            visible=True,
        )

        # Status
        status_section = ft.Container(
            content=ft.Row([
                ft.Icon(ft.Icons.CIRCLE, size=10, color=ft.Colors.GREEN_400),
                self.status_text,
            ]),
            margin=ft.margin.only(bottom=10),
        )

        # Log section
        log_section = ft.Card(
            content=ft.Container(
                content=ft.Column([
                    ft.Text("Log Output", size=18, weight=ft.FontWeight.BOLD),
                    ft.Divider(),
                    ft.Container(
                        content=self.log_container,
                        height=200,
                        bgcolor=ft.Colors.BLACK54,
                        border_radius=8,
                        padding=10,
                    ),
                ]),
                padding=15,
            ),
        )

        # Build layout
        self.page.add(
            ft.Column([
                header,
                ft.Row([
                    ft.Column([
                        file_section,
                        options_section,
                        actions_section,
                    ], expand=3),
                    ft.Column([
                        status_section,
                        progress_section,
                        log_section,
                    ], expand=2),
                ], expand=True, spacing=20),
            ], expand=True)
        )

    def _log(self, message: str, color: str = None):
        timestamp = datetime.now().strftime("%H:%M:%S")
        text = ft.Text(
            f"[{timestamp}] {message}",
            size=12,
            color=color or ft.Colors.GREY_300,
            selectable=True,
        )
        self.log_container.controls.append(text)
        self.page.update()

    def _set_status(self, message: str, color: str = ft.Colors.GREEN_400):
        self.status_text.value = message
        self.status_text.color = color
        self.page.update()

    def _set_progress(self, visible: bool, value: float = 0, text: str = ""):
        self.progress_bar.visible = visible
        self.progress_bar.value = value
        self.progress_text.visible = visible
        self.progress_text.value = text
        self.page.update()

    def _on_pak_file_picked(self, e: ft.FilePickerResultEvent):
        if e.files and len(e.files) > 0:
            self.pak_path = e.files[0].path
            self.pak_path_field.value = self.pak_path
            self.page.update()
            self._log(f"Selected PAK: {Path(self.pak_path).name}")

    def _on_dir_picked(self, e: ft.FilePickerResultEvent):
        if e.path:
            self.edit_dir = e.path
            self.edit_dir_field.value = self.edit_dir
            self.page.update()
            self._log(f"Selected edit directory: {Path(self.edit_dir).name}")

    def _on_save_file_picked(self, e: ft.FilePickerResultEvent):
        if e.path:
            self.output_path = e.path
            self.output_field.value = self.output_path
            self.page.update()
            self._log(f"Output path: {Path(self.output_path).name}")

    def _run_in_thread(self, func, *args, **kwargs):
        def wrapper():
            try:
                self.is_processing = True
                func(*args, **kwargs)
            except Exception as ex:
                self._log(f"Error: {str(ex)}", ft.Colors.RED_400)
                self._set_status(f"Error: {str(ex)}", ft.Colors.RED_400)
                traceback.print_exc()
            finally:
                self.is_processing = False
                self._set_progress(False)
                self.page.update()
        threading.Thread(target=wrapper, daemon=True).start()

    def _validate_paths(self, need_edit=False):
        if not self.pak_path or not Path(self.pak_path).exists():
            self._log("Error: Please select a valid PAK file", ft.Colors.RED_400)
            return False
        if need_edit and (not self.edit_dir or not Path(self.edit_dir).exists()):
            self._log("Error: Please select a valid edit directory", ft.Colors.RED_400)
            return False
        return True

    def _on_unpack(self, e):
        if self.is_processing:
            return
        if not self._validate_paths():
            return

        def do_unpack():
            pak_path = Path(self.pak_path)
            out_dir = Path(self.output_path) if self.output_path else pak_path.parent / "UNPACK" / pak_path.stem

            self._log(f"Starting unpack: {pak_path.name}")
            self._set_status("Unpacking...", ft.Colors.BLUE_400)
            self._set_progress(True, 0, "Loading PAK...")

            pak = TencentPakFile(pak_path)
            
            def progress_cb(current, total, name):
                self._set_progress(True, current / total, f"Extracting {current}/{total}: {name}")

            pak.dump(out_dir, progress_callback=progress_cb)

            # Write index.csv
            csv_path = out_dir / "index.csv"
            paths = sorted(set(build_fullpath_entry_map(pak).keys()))
            with open(csv_path, 'w', encoding='utf-8') as f:
                for p in paths:
                    f.write(p + "\n")

            self._log(f"Unpacked {len(paths)} files to {out_dir}", ft.Colors.GREEN_400)
            self._set_status(f"Unpack complete: {len(paths)} files", ft.Colors.GREEN_400)

        self._run_in_thread(do_unpack)

    def _on_repack(self, e):
        if self.is_processing:
            return
        if not self._validate_paths(need_edit=True):
            return

        def do_repack():
            pak_path = Path(self.pak_path)
            edit_dir = Path(self.edit_dir)
            output_path = Path(self.output_path) if self.output_path else pak_path.parent / "RESULT" / pak_path.name

            self._log(f"Starting repack: {pak_path.name}")
            self._set_status("Repacking...", ft.Colors.BLUE_400)
            self._set_progress(True, 0, "Loading PAK...")

            try:
                sm4_type = int(self.sm4_type_field.value or "47")
            except ValueError:
                sm4_type = 47

            pak = TencentPakFile(pak_path)
            edited, added = inject_edit_files(
                pak, edit_dir, output_path,
                protect_new=self.encrypt_switch.value,
                sm4_type=sm4_type,
            )

            self._log(f"Repack complete: {edited} edited, {added} added", ft.Colors.GREEN_400)
            self._log(f"Output: {output_path}", ft.Colors.GREEN_400)
            self._set_status(f"Repack complete: {edited + added} files", ft.Colors.GREEN_400)

        self._run_in_thread(do_repack)

    def _on_inject(self, e):
        if self.is_processing:
            return
        if not self._validate_paths(need_edit=True):
            return

        def do_inject():
            pak_path = Path(self.pak_path)
            edit_dir = Path(self.edit_dir)
            output_path = Path(self.output_path) if self.output_path else pak_path.parent / "RESULT" / pak_path.name

            self._log(f"Starting inject: {pak_path.name}")
            self._set_status("Injecting...", ft.Colors.BLUE_400)
            self._set_progress(True, 0, "Loading PAK...")

            try:
                sm4_type = int(self.sm4_type_field.value or "47")
            except ValueError:
                sm4_type = 47

            pak = TencentPakFile(pak_path)
            edited, added = inject_edit_files(
                pak, edit_dir, output_path,
                protect_new=self.encrypt_switch.value,
                sm4_type=sm4_type,
            )

            self._log(f"Inject complete: {edited} edited, {added} added", ft.Colors.GREEN_400)
            self._log(f"Output: {output_path}", ft.Colors.GREEN_400)
            self._set_status(f"Inject complete: {edited + added} files", ft.Colors.GREEN_400)

        self._run_in_thread(do_inject)

    def _on_protect(self, e):
        if self.is_processing:
            return
        if not self._validate_paths():
            return

        def do_protect():
            pak_path = Path(self.pak_path)
            output_path = Path(self.output_path) if self.output_path else pak_path.parent / "RESULT" / pak_path.name

            self._log(f"Starting protect: {pak_path.name}")
            self._set_status("Protecting...", ft.Colors.PURPLE_400)
            self._set_progress(True, 0, "Loading PAK...")

            try:
                sm4_type = int(self.sm4_type_field.value or "47")
            except ValueError:
                sm4_type = 47

            pak = TencentPakFile(pak_path)

            def progress_cb(current, total, name):
                self._set_progress(True, current / total, f"Protecting {current}/{total}: {name}")

            protected, skipped = protect_pak_file(
                pak, output_path,
                sm4_type=sm4_type,
                progress_callback=progress_cb,
            )

            self._log(f"Protect complete: {protected} protected, {skipped} skipped", ft.Colors.GREEN_400)
            self._log(f"Output: {output_path}", ft.Colors.GREEN_400)
            self._set_status(f"Protect complete: {protected} files", ft.Colors.GREEN_400)

        self._run_in_thread(do_protect)

    def _on_info(self, e):
        if self.is_processing:
            return
        if not self._validate_paths():
            return

        def do_info():
            pak_path = Path(self.pak_path)
            self._log(f"Reading info: {pak_path.name}")
            self._set_status("Reading info...", ft.Colors.BLUE_400)

            pak = TencentPakFile(pak_path)
            info = {
                "File": pak_path.name,
                "Version": pak._pak_info.version,
                "Mount Point": str(pak._mount_point),
                "Total Files": len(pak._files),
                "Index Encrypted": pak._pak_info.index_encrypted,
                "File Size": f"{pak_path.stat().st_size:,} bytes",
            }

            self._log("=== PAK Info ===", ft.Colors.CYAN_400)
            for key, value in info.items():
                self._log(f"  {key}: {value}", ft.Colors.WHITE)
            self._log("================", ft.Colors.CYAN_400)

            self._set_status("Info retrieved", ft.Colors.GREEN_400)

        self._run_in_thread(do_info)

    def _on_list(self, e):
        if self.is_processing:
            return
        if not self._validate_paths():
            return

        def do_list():
            pak_path = Path(self.pak_path)
            self._log(f"Listing files: {pak_path.name}")
            self._set_status("Listing files...", ft.Colors.BLUE_400)

            pak = TencentPakFile(pak_path)
            files = build_fullpath_entry_map(pak)

            self._log(f"=== {len(files)} files ===", ft.Colors.CYAN_400)
            for path in sorted(files.keys()):
                self._log(f"  {path}", ft.Colors.WHITE)
            self._log("=====================", ft.Colors.CYAN_400)

            self._set_status(f"Listed {len(files)} files", ft.Colors.GREEN_400)

        self._run_in_thread(do_list)

    def _on_clear_log(self, e):
        self.log_container.controls.clear()
        self.page.update()


def main(page: ft.Page):
    PAKToolApp(page)


if __name__ == "__main__":
    ft.app(target=main)
