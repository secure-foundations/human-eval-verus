/// xs represent coefficients of a polynomial.
/// xs[0] + xs[1] * x + xs[2] * x^2 + ....
/// Return derivative of this polynomial in the same form.

use vstd::prelude::*;
fn main() {}

verus!{
fn derivative(xs: Vec<i32>) -> (ret: Vec<i32>) {
    let mut result: Vec<i32> = Vec::new();
    let mut i = 1;
    while i < xs.len() {
        let coeff = xs[i];
        result.push(coeff * (i as i32));
        i += 1;
    }
    result
}
}
