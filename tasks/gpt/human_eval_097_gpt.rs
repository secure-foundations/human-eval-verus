/// Complete the function that takes two integers and returns 
/// the product of their unit digits.
/// Assume the input is always valid.
/// Examples:
/// multiply(148, 412) should return 16.
/// multiply(19, 28) should return 72.
/// multiply(2020, 1851) should return 0.
/// multiply(14,-15) should return 20.

use vstd::prelude::*;
fn main() {}

verus!{
fn custom_modulo(mut a: i32) -> (ret: i32) {
    let a_sign = if a < 0 { -1 } else { 1 };
    a = a * a_sign; // Make 'a' positive
    while a >= 10 {
        a -= 10;
    }
    a * a_sign // Return the result with the original sign
}

fn multiply(a: i32, b: i32) -> (ret: i32) {
    let a_last_digit = custom_modulo(a);
    let b_last_digit = custom_modulo(b);
    a_last_digit * b_last_digit
}
}
