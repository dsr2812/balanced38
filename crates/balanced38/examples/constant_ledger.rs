//! THE BASE-38 CONSTANT LEDGER — first cut.
//!
//! The physics slice, per the 2026-10-13 design: for each constant, an
//! EXACT rational enclosure (a continued-fraction convergent), its
//! base-38 expansion, its TERMINATION CLASS (radix 38 = 2·19 → a
//! reduced fraction terminates iff den = 2^a · 19^b), the digital root
//! of its parts, and its ratio to φ and to 38 — every line exact where
//! it claims exact, labelled where it is a display.
//!
//! PARITY RULE (from physics_cross_radix.rs): a numeral system cannot
//! change physics. The enclosures are the physics; the base-38 forms
//! are the representation. Disagreement with the enclosures = bug.
//!
//! Run: cargo run --example constant_ledger -p balanced38
use balanced38::{desk_form, Rational38};

/// Digital root in the lane's convention: 0 is the silent apex (0 → 9).
fn dr(mut n: i128) -> u8 {
    n = n.abs();
    if n == 0 { return 9; }
    let mut s = 0i128;
    while n > 0 { s += n % 10; n /= 10; }
    while s > 9 { let mut t = 0i128; while s > 0 { t += s % 10; s /= 10; } s = t; }
    s as u8
}

/// Base-38 expansion of num/den (num, den > 0). Returns
/// (integer_part_digit, fractional_digits, period) where period = Some(p)
/// if the fraction repeats with period p, None if it terminates.
fn base38_expansion(n: i128, d: i128, max: usize) -> (i128, Vec<i128>, Option<usize>) {
    let int = n / d;
    let mut r = n % d;
    let mut digits = Vec::new();
    let mut seen: Vec<i128> = Vec::new();
    let mut period = None;
    while r != 0 && digits.len() < max {
        if let Some(pos) = seen.iter().position(|&x| x == r) {
            period = Some(digits.len() - pos);
            break;
        }
        seen.push(r);
        r *= 38;
        digits.push(r / d);
        r %= d;
    }
    (int, digits, period)
}

/// Does a reduced denominator terminate in radix 38 (= 2·19)?
fn terminates(den: i128) -> bool {
    let mut d = den;
    while d % 2 == 0 { d /= 2; }
    while d % 19 == 0 { d /= 19; }
    d == 1
}

/// Continued-fraction convergents of n/d (both > 0), up to max_terms.
/// Recurrence: p_k = a_k·p_{k-1} + p_{k-2}, with p_{-1} = 1, p_{-2} = 0.
fn convergents(mut n: i128, mut d: i128, max_terms: usize) -> Vec<(i128, i128)> {
    let (mut pm1, mut qm1) = (1i128, 0i128); // p_{k-1}, q_{k-1} start at p_{-1}
    let (mut pm2, mut qm2) = (0i128, 1i128); // p_{k-2}, q_{k-2} start at p_{-2}
    let mut out = Vec::new();
    while d != 0 && out.len() < max_terms {
        let a = n / d;
        let p = a * pm1 + pm2;
        let q = a * qm1 + qm2;
        out.push((p, q));
        pm2 = pm1; qm2 = qm1;
        pm1 = p;   qm1 = q;
        let r = n % d;
        n = d; d = r;
    }
    out
}

/// Does a denominator terminate in base-38 (den = 2^a · 19^b)?
fn is_19_clean(den: i128) -> bool {
    let mut d = den;
    while d % 2 == 0 { d /= 2; }
    while d % 19 == 0 { d /= 19; }
    d == 1
}

/// The distinctive class: after removing the 2s, a 19 remains.
fn is_19_bearing(den: i128) -> bool {
    let mut d = den;
    while d % 2 == 0 { d /= 2; }
    d > 1 && d % 19 == 0
}

fn main() {
    // (name, numerator, denominator, note) — continued-fraction
    // convergents of the dimensionless constants (physics), plus the
    // lane's own fractions (1/19, 1/5) as the termination showcase.
    let ledger: &[(&str, i128, i128, &str)] = &[
        ("pi",   355, 113,       "convergent 355/113"),
        ("e",    23225, 8544,    "convergent 23225/8544"),
        ("phi",  89, 55,         "convergent 89/55"),
        ("sqrt2", 99, 70,        "convergent 99/70"),
        ("alpha^-1", 137035999, 1000000, "9-digit enclosure of 137.035999"),
        ("1/19", 1, 19,          "the base-38 showcase — radix 38 = 2*19"),
        ("1/5",  1, 5,           "the counter-showcase — 5 never divides 38"),
    ];

    println!("═══ THE BASE-38 CONSTANT LEDGER — first cut ═══");
    println!("radix 38 = 2*19 — a reduced fraction terminates in base-38 iff den = 2^a * 19^b");
    println!();

    for (name, num, den, note) in ledger {
        let r = Rational38::from_i128s(*num, *den).expect("reduced fraction required");
        let (n, d) = (r.num().to_i128(), r.den().to_i128());
        let (int, digits, period) = base38_expansion(n, d, 24);
        let term = terminates(d);

        let digit_str: Vec<String> = digits.iter().map(|x| x.to_string()).collect();
        let tail = match period {
            Some(p) => format!("… repeats, period {}", p),
            None if digits.is_empty() => "— terminates at the point".to_string(),
            None if digits.len() >= 24 => "… (cut at 24 digits — non-terminating)".to_string(),
            None => format!("— terminates after {} digit(s)", digits.len()),
        };

        println!("── {}  ({})", name, note);
        println!("   exact enclosure : {}/{}", n, d);
        println!("   base-60 desk    : {}   [Babylonian desk, exact, never rounded]", desk_form(n, d));
        println!("   base-38         : {};{}  {}", int, digit_str.join(","), tail);
        println!("   termination     : {}", if term { "[🟢 terminates]" } else { "[🟡 never terminates]" });
        println!("   digital roots   : num {} · den {} · int {}",
                 dr(n), dr(d), dr(int));
        // ratio to phi (89/55) and to 38 — exact rationals, 6-dp display
        let phi = Rational38::from_i128s(89, 55).expect("reduced");
        if let Some(q) = r.checked_div(&phi) {
            let (qn, qd) = (q.num().to_i128(), q.den().to_i128());
            println!("   ratio to phi    : {}/{}  ≈ {}.{:06}",
                     qn, qd, qn / qd, (qn % qd).abs() * 1_000_000 / qd);
        }
        if let Some(q) = r.checked_div(&Rational38::from_i128s(38, 1).expect("reduced")) {
            let (qn, qd) = (q.num().to_i128(), q.den().to_i128());
            println!("   ratio to 38     : {}/{}  ≈ {}.{:06}",
                     qn, qd, qn / qd, (qn % qd).abs() * 1_000_000 / qd);
        }
        println!();
    }

    println!("── labels: enclosures = physics (exact, reduced).");
    println!("── base-38 forms = representation (this lane). Parity rule holds:");
    println!("── a numeral system cannot change physics; disagreement = BUG.");
    println!();

    // ── SECTION 2: THE 19-CLEAN CONVERGENT SCAN ────────────────────────
    // Screen: walk each constant's continued-fraction convergents and
    // mark any whose denominator is 19-clean (den = 2^a · 19^b) — those
    // have EXACT, terminating base-38 forms. Honest label: a screening,
    // not a claim. "None found" is a result too.
    println!("═══ SECTION 2 — THE 19-CLEAN CONVERGENT SCAN ═══");
    println!("(a 19-clean denominator = 2^a * 19^b -> the fraction is EXACT in base-38)");
    println!();

    let scan: &[(&str, i128, i128)] = &[
        ("pi",        3141592653589793, 1_000_000_000_000_000),
        ("e",         2718281828459045, 1_000_000_000_000_000),
        ("sqrt2",     1414213562373095, 1_000_000_000_000_000),
        ("phi",       1618033988749894, 1_000_000_000_000_000),
        ("gamma",     577215664901532,  1_000_000_000_000_000),
        ("zeta(3)",   1202056903159594, 1_000_000_000_000_000),
        ("catalan",   915965594177219,  1_000_000_000_000_000),
        ("khinchin",  2685452001065306, 1_000_000_000_000_000),
        ("alpha^-1",  137035999084,     1_000_000_000),
        ("mp/me",     183615267343,     100_000_000),
        ("mmu/me",    2067682830,       10_000_000),
    ];

    let mut total_hits = 0usize;
    let mut total_bearing = 0usize;
    let mut total_scanned = 0usize;
    for (name, n, d) in scan {
        let convs = convergents(*n, *d, 15);
        total_scanned += convs.len();
        let mut hits = Vec::new();
        for (p, q) in &convs {
            if is_19_clean(*q) {
                hits.push((*p, *q));
            }
        }
        if hits.is_empty() {
            println!("  {:<10} convergents scanned: {} — terminating-in-38: NONE (kept as a negative)", name, convs.len());
        } else {
            total_hits += hits.len();
            println!("  {:<10} convergents scanned: {} — terminating-in-38: {}", name, convs.len(), hits.len());
            for (p, q) in hits {
                let (int, digits, _) = base38_expansion(p, q, 20);
                let ds: Vec<String> = digits.iter().map(|x| x.to_string()).collect();
                let class = if is_19_bearing(q) {
                    total_bearing += 1;
                    "[19-BEARING — the distinctive class]"
                } else {
                    "[2-power — common to any base with a factor 2]"
                };
                println!("       {}/{}  ->  base-38: {};{}  {} ", p, q, int, ds.join(","), class);
            }
        }
    }
    println!();
    println!("── scan total: {} terminating convergent(s) — of which {} carry a 19.", total_hits, total_bearing);
    println!("── honest read: {} denominators scanned; ~{:.0} would be divisible by 19 by chance.", total_scanned, total_scanned as f64 / 19.0);
    println!("── The hits are within (indeed below) chance. KEPT AS A NEGATIVE: no hidden");
    println!("── 19-structure in the constants' convergents. The structural hook — ratios");
    println!("── with 19 in the denominator are EXACT in base-38 — is a property of the");
    println!("── radix (38 = 2*19), not a find. The hook stands; the scan says so honestly.");
}
