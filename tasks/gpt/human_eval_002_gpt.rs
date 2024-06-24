/// Given a positive floating point number, it can be decomposed into
/// an integer part (largest integer smaller than given number) and decimals
/// (leftover part always smaller than 1).
///
/// Return the decimal part of the number.
///
/// # Examples
///
/// ```
/// assert_eq!(truncate_number(3.5), 0.5);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn truncate_number(number: i32) -> (ret:i32) {
    number
}
}
