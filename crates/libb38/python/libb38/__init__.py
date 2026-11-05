"""libb38 — the key, for Python.

Pure ctypes wrapper over the libb38 C-ABI. No dependency beyond the
standard library. Balanced base-38 strings in, exact answers out.

    >>> import libb38
    >>> libb38.add("f", "g")      # 15 + 16 = 31
    '+v'
    >>> libb38.mul("f", "g")      # 15 * 16 = 240
    '+6c'
    >>> libb38.div_rem("-7", "2") # -7 / 2 = -4 remainder 1
    ('-4', '+1')

Every digit is balanced base-38 (0-9, a-z, _ = 36, ~ = 37), MSB-first,
sign prefixed. "0" is zero (the Void). No leading zeros. Parse errors,
refusals (the Void divisor, a beyond-shore value) and values outside
the i128 shore raise ValueError — never a wrapped lie.
"""

import ctypes
import glob
import os
import sys

__version__ = "0.3.1"

_HERE = os.path.dirname(os.path.abspath(__file__))


def _find_library():
    candidates = []
    for pattern in ("liblibb38*.so", "liblibb38*.dylib", "liblibb38*.dll"):
        candidates += glob.glob(os.path.join(_HERE, pattern))
    if not candidates:
        # fall back to the workspace build tree
        root = os.path.abspath(os.path.join(_HERE, "..", "..", "..", ".."))
        candidates = glob.glob(os.path.join(root, "target", "debug", "liblibb38*.so"))
        candidates += glob.glob(os.path.join(root, "target", "debug", "liblibb38*.dylib"))
    if not candidates:
        raise ImportError(
            "liblibb38 native library not found. Build it first: "
            "cargo build -p libb38 in the workspace."
        )
    return max(candidates, key=os.path.getmtime)


_lib = ctypes.CDLL(_find_library())

_lib.b38_version.restype = ctypes.c_uint

_lib.b38_add.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.b38_add.restype = ctypes.c_void_p

_lib.b38_sub.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.b38_sub.restype = ctypes.c_void_p

_lib.b38_mul.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.b38_mul.restype = ctypes.c_void_p

_lib.b38_neg.argtypes = [ctypes.c_char_p]
_lib.b38_neg.restype = ctypes.c_void_p

_lib.b38_free.argtypes = [ctypes.c_void_p]
_lib.b38_free.restype = None

_lib.b38_div_rem.argtypes = [
    ctypes.c_char_p,
    ctypes.c_char_p,
    ctypes.POINTER(ctypes.c_void_p),
    ctypes.POINTER(ctypes.c_void_p),
]
_lib.b38_div_rem.restype = ctypes.c_int

_lib.b38_to_i128.argtypes = [ctypes.c_char_p, ctypes.c_void_p]
_lib.b38_to_i128.restype = ctypes.c_int


class _c_i128(ctypes.Structure):
    """The C `__int128` by value, as its two little-endian 64-bit limbs."""

    _fields_ = [("lo", ctypes.c_uint64), ("hi", ctypes.c_uint64)]


_lib.b38_from_i128.argtypes = [_c_i128, ctypes.POINTER(ctypes.c_void_p)]
_lib.b38_from_i128.restype = ctypes.c_int

_lib.b38_cmp.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.b38_cmp.restype = ctypes.c_int

for _fn in ("b38_ratio_add", "b38_ratio_sub", "b38_ratio_mul", "b38_ratio_div"):
    getattr(_lib, _fn).argtypes = [ctypes.c_char_p, ctypes.c_char_p]
    getattr(_lib, _fn).restype = ctypes.c_void_p
for _fn in ("b38_ratio_neg", "b38_ratio_to_radix", "b38_ratio_from_radix"):
    getattr(_lib, _fn).argtypes = [ctypes.c_char_p]
    getattr(_lib, _fn).restype = ctypes.c_void_p
_lib.b38_ratio_cmp.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
_lib.b38_ratio_cmp.restype = ctypes.c_int

B38_CMP_REFUSAL = 1000000


def _read(raw):
    try:
        return ctypes.string_at(raw).decode("utf-8")
    finally:
        _lib.b38_free(raw)


def version() -> int:
    """The C-ABI version — check it before trusting the surface."""
    return int(_lib.b38_version())


def add(a: str, b: str) -> str:
    """Add two balanced base-38 strings exactly. ValueError on bad input."""
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.add takes two str")
    raw = _lib.b38_add(a.encode("utf-8"), b.encode("utf-8"))
    if not raw:
        raise ValueError(
            f"libb38 refused ({a!r} + {b!r}): bad input or beyond the i128 shore"
        )
    return _read(raw)


def sub(a: str, b: str) -> str:
    """Subtract b from a exactly. ValueError on bad input."""
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.sub takes two str")
    raw = _lib.b38_sub(a.encode("utf-8"), b.encode("utf-8"))
    if not raw:
        raise ValueError(
            f"libb38 refused ({a!r} - {b!r}): bad input or beyond the i128 shore"
        )
    return _read(raw)


def mul(a: str, b: str) -> str:
    """Multiply a by b exactly. ValueError on bad input or a beyond-shore product."""
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.mul takes two str")
    raw = _lib.b38_mul(a.encode("utf-8"), b.encode("utf-8"))
    if not raw:
        raise ValueError(
            f"libb38 refused ({a!r} * {b!r}): bad input or product beyond the i128 shore"
        )
    return _read(raw)


def neg(a: str) -> str:
    """Negate a exactly. ValueError on bad input."""
    if not isinstance(a, str):
        raise TypeError("libb38.neg takes one str")
    raw = _lib.b38_neg(a.encode("utf-8"))
    if not raw:
        raise ValueError(f"libb38 refused (-{a!r}): bad input or beyond the i128 shore")
    return _read(raw)


def div_rem(a: str, b: str):
    """Euclidean quotient and remainder of a / b, as (str, str).

    The remainder always lies in 0..|b|. ValueError on bad input, the
    Void divisor, or a beyond-shore result.
    """
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.div_rem takes two str")
    q = ctypes.c_void_p()
    r = ctypes.c_void_p()
    rc = _lib.b38_div_rem(a.encode("utf-8"), b.encode("utf-8"), ctypes.byref(q), ctypes.byref(r))
    if rc != 0:
        raise ValueError(
            f"libb38 refused ({a!r} / {b!r}): bad input, the Void divisor, "
            "or a beyond-shore result"
        )
    try:
        return (ctypes.string_at(q).decode("utf-8"), ctypes.string_at(r).decode("utf-8"))
    finally:
        _lib.b38_free(q)
        _lib.b38_free(r)


def to_i128(a: str) -> int:
    """The honest shore door: the exact int value a string names.

    ValueError on bad input or a string whose value sits beyond the
    i128 shore. Never wraps.
    """
    if not isinstance(a, str):
        raise TypeError("libb38.to_i128 takes one str")
    buf = (ctypes.c_uint8 * 16)()
    rc = _lib.b38_to_i128(a.encode("utf-8"), ctypes.byref(buf))
    if rc != 0:
        raise ValueError(
            f"libb38 refused to_i128({a!r}): bad input or beyond the i128 shore"
        )
    return int.from_bytes(bytes(buf), "little", signed=True)


def from_i128(v: int) -> str:
    """Format an exact int as its canonical balanced base-38 string.

    The value never refuses — only a value outside the i128 shore
    raises ValueError, up front in Python (the C door is infallible).
    """
    if not isinstance(v, int):
        raise TypeError("libb38.from_i128 takes one int")
    if not (-(1 << 127) <= v <= (1 << 127) - 1):
        raise ValueError(f"libb38.from_i128({v}): outside the i128 shore")
    lo = v & ((1 << 64) - 1)
    hi = (v >> 64) & ((1 << 64) - 1)
    out = ctypes.c_void_p()
    rc = _lib.b38_from_i128(_c_i128(lo, hi), ctypes.byref(out))
    if rc != 0:
        raise ValueError(f"libb38.from_i128({v}): allocation failure")
    return _read(out)


def cmp(a: str, b: str) -> int:
    """Order a and b as exact integers: -1, 0, or +1.

    ValueError on bad input (the refusal sentinel never leaks out).
    """
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.cmp takes two str")
    rc = int(_lib.b38_cmp(a.encode("utf-8"), b.encode("utf-8")))
    if rc == B38_CMP_REFUSAL:
        raise ValueError(f"libb38 refused cmp({a!r}, {b!r}): bad input")
    return rc


def _binary_ratio(fn, name, a, b):
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError(f"libb38.{name} takes two str")
    raw = fn(a.encode("utf-8"), b.encode("utf-8"))
    if not raw:
        raise ValueError(f"libb38 refused {name}({a!r}, {b!r}): bad input or refusal")
    return _read(raw)


def ratio_add(a: str, b: str) -> str:
    """Add two fractions exactly ("+3/+4" + "+1/+2" = "+5/+4")."""
    return _binary_ratio(_lib.b38_ratio_add, "ratio_add", a, b)


def ratio_sub(a: str, b: str) -> str:
    """Subtract two fractions exactly."""
    return _binary_ratio(_lib.b38_ratio_sub, "ratio_sub", a, b)


def ratio_mul(a: str, b: str) -> str:
    """Multiply two fractions exactly."""
    return _binary_ratio(_lib.b38_ratio_mul, "ratio_mul", a, b)


def ratio_div(a: str, b: str) -> str:
    """Divide two fractions exactly; the Void divisor refuses."""
    return _binary_ratio(_lib.b38_ratio_div, "ratio_div", a, b)


def _unary_ratio(fn, name, a):
    if not isinstance(a, str):
        raise TypeError(f"libb38.{name} takes one str")
    raw = fn(a.encode("utf-8"))
    if not raw:
        raise ValueError(f"libb38 refused {name}({a!r}): bad input or refusal")
    return _read(raw)


def ratio_neg(a: str) -> str:
    """Negate a fraction exactly."""
    return _unary_ratio(_lib.b38_ratio_neg, "ratio_neg", a)


def ratio_cmp(a: str, b: str) -> int:
    """Order two fractions as exact values: -1, 0, or +1."""
    if not isinstance(a, str) or not isinstance(b, str):
        raise TypeError("libb38.ratio_cmp takes two str")
    rc = int(_lib.b38_ratio_cmp(a.encode("utf-8"), b.encode("utf-8")))
    if rc == B38_CMP_REFUSAL:
        raise ValueError(f"libb38 refused ratio_cmp({a!r}, {b!r}): bad input or refusal")
    return rc


def ratio_to_radix(a: str) -> str:
    """The VIEW door out: a fraction's base-38 radix expansion, its
    recurring block in trailing "(...)". "0.(cp)" is a third, "0.sj"
    is three quarters, "-1.j" is minus one half (the Euclidean floor
    split puts the sign on the integer part)."""
    return _unary_ratio(_lib.b38_ratio_to_radix, "ratio_to_radix", a)


def ratio_from_radix(a: str) -> str:
    """The VIEW door in: a radix string back into the canonical
    fraction store ("0.(cp)" = "+1/+3"). A long view or a malformed
    string refuses — the closed form never re-reads a lie."""
    return _unary_ratio(_lib.b38_ratio_from_radix, "ratio_from_radix", a)


__all__ = [
    "version",
    "add",
    "sub",
    "mul",
    "neg",
    "div_rem",
    "to_i128",
    "from_i128",
    "cmp",
    "ratio_add",
    "ratio_sub",
    "ratio_mul",
    "ratio_div",
    "ratio_neg",
    "ratio_cmp",
    "ratio_to_radix",
    "ratio_from_radix",
    "__version__",
]