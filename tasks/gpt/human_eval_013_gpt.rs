/// Return a greatest common divisor of two integers a and b
///
/// # Examples
///
/// ```
/// assert_eq!(greatest_common_divisor(3, 5), 1);
/// assert_eq!(greatest_common_divisor(25, 15), 5);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn greatest_common_divisor(mut a: i32, mut b: i32) -> (ret: i32) {
    // Ensure a and b are non-negative
    if a < 0 { a = -a; }
    if b < 0 { b = -b; }

    while b != 0 {
        let t = b;
        // Manually implement modulus for non-negative integers
        b = manual_mod(a, b);
        a = t;
    }
    // The absolute value of a is the GCD
    a
}

fn manual_mod(a: i32, b: i32) -> (ret: i32) {
    // Assuming a and b are non-negative
    let mut result = a;
    while result >= b {
        result = result - b;
    }
    result
}
}
