//! Hubble tension — exact accounting on the membrane's lane.
//! Same inputs the code-writer got: 1826/25 − 337/5, answered by the kernel,
//! not by the model's arithmetic.
use balanced38::{desk_form, Rational38};

fn main() {
    let local = Rational38::from_i128s(1826, 25).expect("reduced");
    let early = Rational38::from_i128s(337, 5).expect("reduced");
    let tension = local.checked_sub(&early).expect("exact");

    let num = tension.num().to_i128();
    let den = tension.den().to_i128();
    println!("local = 1826/25");
    println!("early = 337/5");
    println!("tension = {}/{}", num, den);
    assert_eq!((num, den), (141, 25), "the membrane says 141/25");
    println!("desk = {}", desk_form(num, den));
}
