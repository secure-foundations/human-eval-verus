/// Given a non-empty list of integers `lst`, add the even elements that are at odd indices.
///
/// # Examples
///
/// ```
/// let result = add(vec![4, 2, 6, 7]);
/// assert_eq!(result, 2);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{

fn positive_modulo(a: i32, b: i32) -> (ret: i32) {
    let mut result = a;
    while result < 0 {
        result += b;
    }
    while result >= b {
        result -= b;
    }
    result
}

fn add(lst: Vec<i32>) -> (ret: i32) {
    let mut sum = 0;
    let mut i: i32 = 0;
    while (i as usize) < lst.len() {
        // Cast usize to i32 is safe here because array indices are non-negative
        if positive_modulo(i, 2) == 1 && positive_modulo(lst[i as usize], 2) == 0 {
            sum += lst[i as usize];
        }
        i += 1;
    }
    sum
}
}
