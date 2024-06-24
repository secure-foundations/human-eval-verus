/// Given a positive integer n, return the count of the numbers of n-digit
/// positive integers that start or end with 1.

use vstd::prelude::*;
fn main() {}

verus!{
fn starts_one_ends(n: u32) -> (ret: u32) {
    
    if n == 1 {
        return 1;
    }
    18 * pow10(n - 2)
}

fn pow10(exp: u32) -> (ret: u32) {
    let mut result = 1;
    let mut i = 0;
    while i < exp {
        result *= 10;
        i += 1;
    }
    result
}
}