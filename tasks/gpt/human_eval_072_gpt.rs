/// Determines if the object `q` will fly.
///
/// The object `q` will fly if it's balanced (it is a palindromic list) and the sum of its elements
/// is less than or equal to the maximum possible weight `w`.
///
/// # Examples
///
/// ```
/// assert_eq!(will_it_fly(vec![1, 2], 5), false);
/// // 1+2 is less than the maximum possible weight, but it's unbalanced.
///
/// assert_eq!(will_it_fly(vec![3, 2, 3], 1), false);
/// // it's balanced, but 3+2+3 is more than the maximum possible weight.
///
/// assert_eq!(will_it_fly(vec![3, 2, 3], 9), true);
/// // 3+2+3 is less than the maximum possible weight, and it's balanced.
///
/// assert_eq!(will_it_fly(vec![3], 5), true);
/// // 3 is less than the maximum possible weight, and it's balanced.
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn will_it_fly(q: Vec<i32>, w: i32) -> (result: bool) {
    let mut is_palindrome = true;
    let mut sum = 0;
    let len = q.len();
    
    for i in 0..len {
        sum += q[i];
        if q[i] != q[len - 1 - i] {
            is_palindrome = false;
            break;
        }
    }
    
    is_palindrome && sum <= w
}
}
