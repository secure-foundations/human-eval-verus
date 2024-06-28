/// Return maximum element in the list.
///
/// # Examples
///
/// ```
/// assert_eq!(max_element(&[1, 2, 3]), Some(3));
/// assert_eq!(max_element(&[5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]), Some(123));
/// ```
use vstd::prelude::*;
fn main() {}

verus!{
fn max_element(l: Vec<i32>) -> (ret: Option<i32>) {
    if l.len() == 0 {
        return None;
    }

    let mut max = l[0];
    let mut i = 1;
    while i < l.len() {
        if l[i] > max {
            max = l[i];
        }
        i += 1;
    }
    Some(max)
}
}
