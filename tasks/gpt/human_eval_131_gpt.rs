/// Given a positive integer n, return the product of the odd digits.
/// Return 0 if all digits are even.
/// For example:
/// digits(1)  == 1
/// digits(4)  == 0
/// digits(235) == 15

use vstd::prelude::*;
fn main() {}

verus!{
fn digits(n: u32) -> (product: u32) {
    
    let mut product = 1;
    let mut has_odd = false;
    let mut num = n;

    while num > 0 {
        let digit = num % 10;
        if digit % 2 != 0 {
            product *= digit;
            has_odd = true;
        }
        num /= 10;
    }

    if has_odd {
        product
    } else {
        0
    }
}
}
