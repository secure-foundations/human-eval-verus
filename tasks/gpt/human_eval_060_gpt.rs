/// sum_to_n is a function that sums numbers from 1 to n.
///
/// # Examples
///
/// ```
/// assert_eq!(sum_to_n(30), 465);
/// assert_eq!(sum_to_n(100), 5050);
/// assert_eq!(sum_to_n(5), 15);
/// assert_eq!(sum_to_n(10), 55);
/// assert_eq!(sum_to_n(1), 1);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn sum_to_n(n: i32) -> (ret: i32) {
    let mut sum = 0;
    let mut i = 1;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}
}
