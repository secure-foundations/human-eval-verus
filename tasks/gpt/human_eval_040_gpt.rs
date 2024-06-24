/// triples_sum_to_zero takes a list of integers as an input.
/// it returns True if there are three distinct elements in the list that
/// sum to zero, and False otherwise.
///
/// # Examples
///
/// ```
/// # use your_crate_name::triples_sum_to_zero;
/// assert_eq!(triples_sum_to_zero(&[1, 3, 5, 0]), false);
/// assert_eq!(triples_sum_to_zero(&[1, 3, -2, 1]), true);
/// assert_eq!(triples_sum_to_zero(&[1, 2, 3, 7]), false);
/// assert_eq!(triples_sum_to_zero(&[2, 4, -5, 3, 9, 7]), true);
/// assert_eq!(triples_sum_to_zero(&[1]), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn triples_sum_to_zero(l: Vec<i32>) -> (result: bool) {
    
    let len = l.len();
    let mut i = 0;
    while i < len {
        let mut j = i + 1;
        while j < len {
            let mut k = j + 1;
            while k < len {
                if l[i] + l[j] + l[k] == 0 {
                    return true;
                }
                k += 1;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
}
