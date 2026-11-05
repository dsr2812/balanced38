//! The Hubble receipt — honest accounting, exact arithmetic.
//!
//! Early-universe H₀ (Planck 2018, ΛCDM): 67.4 km/s/Mpc
//! Late-universe  H₀ (SH0ES 2022):       73.04 km/s/Mpc
//!
//! To subtract them exactly we scale by 100 and subtract integers in
//! balanced base-38: decimal 7304 is written `"+528"` (5·38² + 2·38 + 8)
//! and decimal 6740 is written `"+4pe"` (4·38² + p·38 + e). The strings
//! are base-38, not decimal — that is the whole point, the lane reads
//! them the way they are written.
//!
//! `b38_add("+528", "-4pe")` = `"+ew"`, whose value is 14·38 + 32 = 564 —
//! i.e. the residual is 564/100 = 141/25 = 5.64 km/s/Mpc, exact.
//! No first-principles derivation closes the gap; the residual is simply
//! printed.

fn main() {
    let residual = libb38::add("+528", "-4pe").expect("in-shore sum");
    let value: i128 = libb38::parse(&residual).unwrap().to_i128();

    println!("Hubble Tension — honest accounting");
    println!("=================================");
    println!();
    println!("Early-universe (CMB, Planck 2018 ΛCDM):  H₀ = 67.4 km/s/Mpc");
    println!("Late-universe  (SH0ES 2022):             H₀ = 73.04 km/s/Mpc");
    println!();
    println!("No derivation from established physics reproduces both values");
    println!("without new physics or unquantified systematics.");
    println!();
    println!("Residual (SH0ES − CMB), computed exactly with libb38:");
    println!("  b38_add(\"+528\", \"-4pe\") -> {residual}    (base-38 strings)");
    println!("  as i128: {value}");
    println!("  scaled:  {value}/100 = {}/25", value / 4);
    println!("  in km/s/Mpc: 5.64");
    println!();
    println!("No tolerance applied. No pass/fail criterion. No seal.");
}
