/// Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
///
/// # Examples
///
/// ```
/// assert_eq!(solution(&[5, 8, 7, 1]), 12);
/// assert_eq!(solution(&[3, 3, 3, 3, 3]), 9);
/// assert_eq!(solution(&[30, 13, 24, 321]), 0);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn is_even(n: i32) -> (ret: bool) {
    // Check if the least significant bit is not set (even number)
    n & 1 == 0
}

fn solution(lst: Vec<i32>) -> (ret: i32) {
    let mut sum = 0;
    let mut i = 0;
    while i < lst.len() {
        // Use the is_even function to check evenness
        if is_even(i as i32) && !is_even(lst[i]) {
            sum += lst[i];
        }
        i += 1;
    }
    sum
}
}
