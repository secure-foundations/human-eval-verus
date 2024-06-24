/// Evaluate whether the given number `n` can be written as the sum of exactly 4 positive even numbers
///
/// # Examples
///
/// ```
/// assert_eq!(is_equal_to_sum_even(4), false);
/// assert_eq!(is_equal_to_sum_even(6), false);
/// assert_eq!(is_equal_to_sum_even(8), true);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn is_equal_to_sum_even(n: u32) -> (result: bool) {
    
    if n < 8 {
        return false;
    }
    n % 2 == 0
}
}
