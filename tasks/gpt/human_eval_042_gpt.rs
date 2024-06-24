/// Return list with elements incremented by 1.
///
/// # Examples
///
/// ```
/// let result = incr_list(vec![1, 2, 3]);
/// assert_eq!(result, vec![2, 3, 4]);
///
/// let result = incr_list(vec![5, 3, 5, 2, 3, 3, 9, 0, 123]);
/// assert_eq!(result, vec![6, 4, 6, 3, 4, 4, 10, 1, 124]);
/// ```
use vstd::prelude::*;
fn main() {}

verus!{
fn incr_list(l: Vec<i32>) -> (ret: Vec<i32>) {
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < l.len() {
        result.push(l[index] + 1);
        index += 1;
    }
    result
}
}