/// The Brazilian factorial is defined as:
/// brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
/// where n > 0
///
/// For example:
/// ```
/// let result = special_factorial(4);
/// assert_eq!(result, 288);
/// ```
///
/// The function will receive an integer as input and should return the special
/// factorial of this integer.

use vstd::prelude::*;
fn main() {}

verus!{
fn special_factorial(n: u32) -> (result: u64) {
    
    let mut result = 1u64;
    let mut factorial = 1u64;
    let mut i = 1u64;
    while i <= n as u64 {
        factorial *= i;
        result *= factorial;
        i += 1;
    }
    result
}
}
