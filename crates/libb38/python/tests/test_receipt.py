"""The Python wheel's receipt — plain assert tests, no framework.

Every string is balanced base-38, never decimal (the INANNA trap):
"+528" is 7304, "+4pe" is 6740, "+ew" is 564. The same exact cases
run through the C smoke test and this receipt — one arithmetic, two
doors.
"""

import libb38


def main() -> int:
    assert libb38.version() == 3
    cases = []
    refusals = 0

    add_cases = [
        ("2", "3", "+5"),
        ("0", "0", "0"),
        ("+1", "-1", "0"),
        ("-3", "-4", "-7"),
        ("f", "g", "+v"),
        ("1z", "1", "+1_"),
        ("-100", "-100", "-200"),
        # the Hubble receipt: decimal 7304 = "+528", 6740 = "+4pe",
        # residual 564 = "+ew"; 564/100 = 141/25 = 5.64
        ("+528", "-4pe", "+ew"),
    ]
    cases += [("add", a, b, want) for (a, b, want) in add_cases]

    sub_cases = [
        ("5", "3", "+2"),
        ("+1", "-1", "+2"),
        ("-3", "4", "-7"),
        ("+528", "+4pe", "+ew"),  # 7304 - 6740 = 564
        ("ew", "ew", "0"),
    ]
    cases += [("sub", a, b, want) for (a, b, want) in sub_cases]

    mul_cases = [
        ("f", "g", "+6c"),   # 15 * 16 = 240
        ("1z", "1", "+1z"),
        ("-7", "2", "-e"),
        ("0", "f", "0"),
        ("2o", "2o", "+6z6"),  # 100 * 100 = 10000
        # 2^63 * 2^63 = 2^126, exact
        ("+10p4451iy8_~i", "+10p4451iy8_~i", "+11coup_jar_ds8z4zwsn~l2ak"),
    ]
    cases += [("mul", a, b, want) for (a, b, want) in mul_cases]

    neg_cases = [
        ("+528", "-528"),
        ("-ew", "+ew"),
        ("0", "0"),
        ("-1k", "+1k"),
    ]
    cases += [("neg", a, None, want) for (a, want) in neg_cases]

    div_rem_cases = [
        ("-7", "2", "-4", "+1"),  # -7 / 2 = -4 remainder 1
        ("-7", "-2", "+4", "+1"),
        ("1", "4a", "0", "+1"),   # 1 / 38 = 0 remainder 1
        ("+528", "+4pe", "+1", "+ew"),  # 7304 / 6740 = 1 remainder 564
    ]
    cases += [("div_rem", a, b, (q, r)) for (a, b, q, r) in div_rem_cases]

    cmp_cases = [
        ("+528", "+4pe", 1),
        ("+4pe", "+528", -1),
        ("7", "7", 0),
        ("0", "0", 0),
        ("f", "g", -1),
    ]
    cases += [("cmp", a, b, want) for (a, b, want) in cmp_cases]

    to_i128_cases = [
        ("+528", 7304),
        ("-7", -7),
        ("0", 0),
        ("1z", 73),
        ("-1k", -58),
        ("+22pbndz0lhyrihw9xrj9~44l1", (1 << 127) - 1),
    ]
    cases += [("to_i128", a, None, want) for (a, want) in to_i128_cases]

    from_i128_cases = [
        (7304, "+528"),
        (-58, "-1k"),
        (0, "0"),
        (240, "+6c"),
        ((1 << 127) - 1, "+22pbndz0lhyrihw9xrj9~44l1"),
        (-(1 << 127), "-22pbndz0lhyrihw9xrj9~44l2"),
    ]
    cases += [("from_i128", v, None, want) for (v, want) in from_i128_cases]

    # ── the rational doors (v3): the promise lands ────────────────
    ratio_add_cases = [
        ("+3/+4", "+1/+2", "+5/+4"),       # the receipt, as a fraction
        ("-3/4", "+1/8", "-5/+8"),
        ("6/8", "0", "+3/+4"),             # reduced on entry, Void binds
        ("+3r/+p", "+3r/+p", "+7g/+p"),    # 141/25 twice: 282/25 = 7·38+16
    ]
    cases += [("ratio_add", a, b, want) for (a, b, want) in ratio_add_cases]

    ratio_sub_cases = [
        ("+3/+4", "+1/+2", "+1/+4"),
        ("1/2", "1/3", "+1/+6"),
        ("0", "1/7", "-1/+7"),
    ]
    cases += [("ratio_sub", a, b, want) for (a, b, want) in ratio_sub_cases]

    ratio_mul_cases = [
        ("1/4", "2/3", "+1/+6"),
        ("-2", "1/3", "-2/+3"),
        ("0", "1/7", "0"),
    ]
    cases += [("ratio_mul", a, b, want) for (a, b, want) in ratio_mul_cases]

    ratio_div_cases = [
        ("1/2", "1/3", "+3/+2"),
        ("+3r/+p", "2", "+3r/+1c"),      # 141/25 ÷ 2 = 141/50 ('1c'=50)
        ("1/7", "1/7", "+1"),
    ]
    cases += [("ratio_div", a, b, want) for (a, b, want) in ratio_div_cases]

    ratio_neg_cases = [
        ("-3/4", "+3/+4"),
        ("0", "0"),
        ("6/8", "-3/+4"),
    ]
    cases += [("ratio_neg", a, None, want) for (a, want) in ratio_neg_cases]

    ratio_cmp_cases = [
        ("1/2", "1/3", 1),
        ("-1/2", "-1/3", -1),
        ("+3/+4", "+6/+8", 0),
        ("0", "1/z", -1),              # 0 < 1/35 ('z' is the digit 35)
        ("1/7", "6/31", 1),            # 1/7 ≈ 0.1428 > 6/115 ('31'=115)
        ("5/4", "6/5", 1),
    ]
    cases += [("ratio_cmp", a, b, want) for (a, b, want) in ratio_cmp_cases]

    to_radix_cases = [
        ("+1/+3", "0.(cp)"),
        ("+1/+10", "0.1"),             # "10" is thirty-eight
        ("+3/+4", "0.sj"),
        ("+1/+7", "0.(5gawlr)"),
        ("-1/2", "-1.j"),              # the Euclidean floor split
        ("-3/4", "-1.9j"),
        ("+2/+1", "+2"),
        ("0", "0"),
        ("+3r/+p", "+5.(oc631jsxgrdpvy_i94la)"),
    ]
    cases += [("to_radix", a, None, want) for (a, want) in to_radix_cases]

    from_radix_cases = [
        ("0.(cp)", "+1/+3"),
        ("0.1", "+1/+10"),
        ("0.sj", "+3/+4"),
        ("0.(5gawlr)", "+1/+7"),
        ("-1.j", "-1/+2"),
        ("+5.(oc631jsxgrdpvy_i94la)", "+3r/+p"),
        ("1", "+1"),
    ]
    cases += [("from_radix", a, None, want) for (a, want) in from_radix_cases]

    for op, a, b, want in cases:
        if op == "add":
            got = libb38.add(a, b)
            where = f"{a}+{b}"
        elif op == "sub":
            got = libb38.sub(a, b)
            where = f"{a}-{b}"
        elif op == "mul":
            got = libb38.mul(a, b)
            where = f"{a}*{b}"
        elif op == "neg":
            got = libb38.neg(a)
            where = f"-({a})"
        elif op == "div_rem":
            got = libb38.div_rem(a, b)
            where = f"{a}/{b}"
        elif op == "cmp":
            got = libb38.cmp(a, b)
            where = f"cmp({a},{b})"
        elif op == "to_i128":
            got = libb38.to_i128(a)
            where = f"to_i128({a})"
        elif op == "ratio_add":
            got = libb38.ratio_add(a, b)
            where = f"ratio_add({a},{b})"
        elif op == "ratio_sub":
            got = libb38.ratio_sub(a, b)
            where = f"ratio_sub({a},{b})"
        elif op == "ratio_mul":
            got = libb38.ratio_mul(a, b)
            where = f"ratio_mul({a},{b})"
        elif op == "ratio_div":
            got = libb38.ratio_div(a, b)
            where = f"ratio_div({a},{b})"
        elif op == "ratio_neg":
            got = libb38.ratio_neg(a)
            where = f"ratio_neg({a})"
        elif op == "ratio_cmp":
            got = libb38.ratio_cmp(a, b)
            where = f"ratio_cmp({a},{b})"
        elif op == "to_radix":
            got = libb38.ratio_to_radix(a)
            where = f"ratio_to_radix({a})"
        elif op == "from_radix":
            got = libb38.ratio_from_radix(a)
            where = f"ratio_from_radix({a})"
        else:  # from_i128
            got = libb38.from_i128(a)
            where = f"from_i128({a:d})"
        assert got == want, f"{op} {where}: got {got!r}, want {want!r}"

    # the extremes round-trip through the doors, hand in hand
    for v in ((1 << 127) - 1, -(1 << 127), 0, 1, -1, 1 << 64, -(1 << 64)):
        assert libb38.to_i128(libb38.from_i128(v)) == v, f"extreme broke at {v}"

    for bad in ("", "+", "-", "07", "ZZZ"):
        for op in (libb38.add, libb38.sub, libb38.mul):
            try:
                op(bad, "1")
            except ValueError:
                pass
            else:
                raise AssertionError(f"{bad!r} must be refused by {op.__name__}")
            refusals += 1
        try:
            libb38.cmp(bad, "1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{bad!r} must be refused by cmp")
        refusals += 1

    try:
        libb38.div_rem("5", "0")  # the Void divisor
    except ValueError:
        pass
    else:
        raise AssertionError("the Void divisor must be refused by div_rem")
    refusals += 1

    try:
        libb38.mul("+21c88a2~uhz__", "+21c88a2~uhz__")  # 2^64 * 2^64 = 2^128
    except ValueError:
        pass
    else:
        raise AssertionError("a beyond-shore product must be refused by mul")
    refusals += 1

    try:
        libb38.to_i128("z" * 25)  # a 25-place all-19 string, past the shore
    except ValueError:
        pass
    else:
        raise AssertionError("a beyond-shore string must be refused by to_i128")
    refusals += 1

    try:
        libb38.from_i128(1 << 127)  # one past the i128 shore, refused up front
    except ValueError:
        pass
    else:
        raise AssertionError("a value outside the i128 shore must be refused up front")
    refusals += 1

    # ── the rational refusals, all loud ───────────────────────────
    try:
        libb38.ratio_div("1", "0")  # the Void divisor
    except ValueError:
        pass
    else:
        raise AssertionError("the Void divisor must be refused by ratio_div")
    refusals += 1

    try:
        libb38.ratio_add("1/0", "1")
    except ValueError:
        pass
    else:
        raise AssertionError("a Void denominator must be refused by ratio_add")
    refusals += 1

    try:
        libb38.ratio_add("1/2/3", "1")
    except ValueError:
        pass
    else:
        raise AssertionError("a two-slash string must be refused")
    refusals += 1

    try:
        libb38.ratio_mul("+21c88a2~uhz__/1", "+21c88a2~uhz__/1")  # 2^128
    except ValueError:
        pass
    else:
        raise AssertionError("a beyond-shore ratio product must be refused")
    refusals += 1

    try:
        libb38.ratio_cmp("ZZZ", "1")
    except ValueError:
        pass
    else:
        raise AssertionError("bad ratio cmp must be refused")
    refusals += 1

    try:
        libb38.ratio_from_radix("5.")
    except ValueError:
        pass
    else:
        raise AssertionError("a bare dot must be refused")
    refusals += 1

    try:
        libb38.ratio_from_radix("0.(2)(3)")
    except ValueError:
        pass
    else:
        raise AssertionError("a doubled period must be refused")
    refusals += 1

    try:
        libb38.ratio_to_radix("1/+11coup_jar_ds8z4zwsn~l2ak")  # the 38*r walk shore
    except ValueError:
        pass
    else:
        raise AssertionError("a beyond-shore radix walk must be refused")
    refusals += 1

    print(f"python wheel receipt: version {libb38.version()}, "
          f"{len(cases)} cases + {refusals} refusals OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())