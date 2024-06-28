/// Given a non-empty array of integers `arr` and an integer `k`, return
/// the sum of the elements with at most two digits from the first `k` elements of `arr`.
///
/// # Examples
///
/// ```
/// # fn main() {
/// let arr = vec![111, 21, 3, 4000, 5, 6, 7, 8, 9];
/// let k = 4;
/// let output = add_elements(&arr, k);
/// assert_eq!(output, 24); // sum of 21 + 3
/// # }
/// ```
///
/// # Constraints
///
/// - 1 <= arr.len() <= 100
/// - 1 <= k <= arr.len()

use vstd::prelude::*;
fn main() {}

verus!{
fn add_elements(arr: Vec<i32>, k: usize) -> (ret: i32) {
    let mut sum: i32 = 0;
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < arr.len() && count < k {
        let x = arr[i];
        if (x >= 0 && x < 100) || (x <= 0 && x > -100) {
            sum += x;
            count += 1;
        }
        i += 1;
    }

    sum
}
}
