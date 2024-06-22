/// Return 2^n modulo p (be aware of numerics).

use vstd::prelude::*;
fn main() {}

verus!{
fn modp(n: u32, p: u32) -> (result: u32) {
    
    let mut result = 1;
    let mut base = 2;
    let mut exponent = n;
    let modulus = p;

    while exponent > 0 {
        if exponent % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exponent /= 2;
    }

    result
}
}
