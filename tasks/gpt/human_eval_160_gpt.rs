/// Given two vectors `operator` and `operand`, the first vector has basic algebra operations as strings,
/// and the second vector is a vector of integers. Use the two given vectors to build the algebraic
/// expression and return the evaluation of this expression.
///
/// The basic algebra operations:
/// Addition ( + )
/// Subtraction ( - )
/// Multiplication ( * )
/// Floor division ( // ) - Note: Rust uses `/` for division and does not have a direct equivalent to Python's `//`.
/// Exponentiation ( ** ) - Note: Rust uses `pow` method for exponentiation.
///
/// # Examples
///
/// ```
/// let operators = vec!['+', '*', '-'];
/// let operands = vec![2, 3, 4, 5];
/// let result = do_algebra(operators, operands);
/// assert_eq!(result, 9);
/// ```
///
/// # Notes
///
/// - The length of `operator` vector is equal to the length of `operand` vector minus one.
/// - `operand` is a vector of non-negative integers.
/// - `operator` vector has at least one operator, and `operand` vector has at least two operands.

use vstd::prelude::*;
fn main() {}

verus!{
fn do_algebra(operator: Vec<char>, operand: Vec<i32>) -> (result: i32) {
    
    let mut result = operand[0];
    let mut index = 0;
    while index < operator.len() {
        let op = operator[index];
        match op {
            '+' => result += operand[index + 1],
            '-' => result -= operand[index + 1],
            '*' => result *= operand[index + 1],
            '/' => {
                // Convert to unsigned, perform division, then convert back to signed
                let dividend = result as u32;
                let divisor = operand[index + 1] as u32;
                result = (dividend / divisor) as i32;
            },
            '^' => {
                // Implement power function manually
                let mut power = operand[index + 1] as u32; // Convert to unsigned
                let mut base = result;
                result = 1;
                while power > 0 {
                    if power & 1 == 1 { // Use bitwise AND to check if power is odd
                        result *= base;
                    }
                    base *= base;
                    power >>= 1; // Use bitwise shift for division by 2
                }
            },
            _ => { /* no-op for unsupported operations */ }
        }
        index += 1;
    }
    result
}
}
