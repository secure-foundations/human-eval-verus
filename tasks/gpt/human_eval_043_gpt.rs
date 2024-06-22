/// pairs_sum_to_zero takes a slice of integers as an input.
/// it returns true if there are two distinct elements in the slice that
/// sum to zero, and false otherwise.
///
/// # Examples
/// ```
/// # use your_module::pairs_sum_to_zero;
/// assert_eq!(pairs_sum_to_zero(&[1, 3, 5, 0]), false);
/// assert_eq!(pairs_sum_to_zero(&[1, 3, -2, 1]), false);
/// assert_eq!(pairs_sum_to_zero(&[1, 2, 3, 7]), false);
/// assert_eq!(pairs_sum_to_zero(&[2, 4, -5, 3, 5, 7]), true);
/// assert_eq!(pairs_sum_to_zero(&[1]), false);
/// ```

use vstd::prelude::*;

fn main() {}

verus!{
fn pairs_sum_to_zero(l: Vec<i32>) -> (result: bool) {
    let mut seen: Vec<i32> = Vec::new();

    let mut i = 0;
    while i < l.len() {
        let value = l[i];
        let mut j = 0;
        let mut found = false;
        while j < seen.len() {
            if seen[j] == -value {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            return true;
        }
        seen.push(value);
        i += 1;
    }

    false
}
}
