/// Return only positive numbers in the list.
///
/// # Examples
///
/// ```
/// let result = get_positive(vec![-1, 2, -4, 5, 6]);
/// assert_eq!(result, vec![2, 5, 6]);
///
/// let result = get_positive(vec![5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]);
/// assert_eq!(result, vec![5, 3, 2, 3, 9, 123, 1]);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn get_positive(l: Vec<i32>) -> (ret: Vec<i32>) {
    let mut positive_numbers: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < l.len() {
        let x = l[i];
        if x > 0 {
            positive_numbers.push(x);
        }
        i += 1;
    }
    positive_numbers
}
}
