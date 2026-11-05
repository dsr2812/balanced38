# libb38 (Python)

The key, for Python. Balanced base-38 strings in, exact answers out — no
rounding, no overflow surprises, no binary-decimal conversion tax. The
native library ships inside the wheel; consumers need no compiler.
Bindings are plain ctypes over the C-ABI.

## The API

```python
>>> import libb38
>>> libb38.version()
3
>>> libb38.add("f", "g")            # 15 + 16 = 31
'+v'
>>> libb38.sub("+528", "+4pe")      # 7304 - 6740 = 564
'+ew'
>>> libb38.mul("f", "g")            # 15 * 16 = 240
'+6c'
>>> libb38.neg("-ew")
'+ew'
>>> libb38.div_rem("-7", "2")       # -7 / 2 = -4 remainder 1
('-4', '+1')
>>> libb38.cmp("+528", "+4pe")
1
>>> libb38.to_i128("+528")          # the honest shore door
7304
>>> libb38.from_i128(-58)           # the value never refuses
'-1k'
>>> libb38.ratio_add("+3/+4", "+1/+2")   # fractions are exact storage
'+5/+4'
>>> libb38.ratio_div("1", "0")      # the Void is not an operand
Traceback (most recent call last):
  ...
ValueError
>>> libb38.ratio_to_radix("+1/+3")  # the VIEW: a third, recurring marked
'0.(cp)'
>>> libb38.ratio_from_radix("0.sj") # three quarters, re-read exactly
'+3/+4'
>>> libb38.ratio_to_radix("+3r/+p") # the Hubble fraction's view
'+5.(oc631jsxgrdpvy_i94la)'
```

Every digit is balanced base-38 (0-9, a-z, `_` = 36, `~` = 37), MSB-first,
sign prefixed. `"0"` is zero (the Void). No leading zeros. The strings are
base-38, never decimal — decimal 7304 is written `"+528"`, not `"+7304"`.

## The receipt

`python tests/test_receipt.py` runs the same exact cases as the C smoke
test — one arithmetic, two doors.

## Honest limits

- The lane is an i128-shore lane: results whose magnitude exceeds the
  shore are refused loudly, never wrapped silently.
- Refusals (bad input, the Void divisor, a beyond-shore result) and a
  value outside the i128 shore raise `ValueError` in the bindings.