/// Return True if all numbers in the list `l` are below threshold `t`.
///
/// # Examples
///
/// ```
/// assert_eq!(below_threshold(&[1, 2, 4, 10], 100), true);
/// assert_eq!(below_threshold(&[1, 20, 4, 10], 5), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn below_threshold(l: Vec<i32>, t: i32) -> (result: bool) {
    let mut i = 0;
    while i < l.len() {
        if l[i] >= t {
            return false;
        }
        i += 1;
    }
    true
}
}
