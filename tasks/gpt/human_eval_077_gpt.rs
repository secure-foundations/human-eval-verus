/// Write a function that takes an integer `a` and returns `true`
/// if this integer is a cube of some integer number.
/// Note: you may assume the input is always valid.
/// 
/// # Examples
/// ```
/// assert_eq!(iscube(1), true);
/// assert_eq!(iscube(2), false);
/// assert_eq!(iscube(-1), true);
/// assert_eq!(iscube(64), true);
/// assert_eq!(iscube(0), true);
/// assert_eq!(iscube(180), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn iscube(a: i32) -> (result: bool) {
    let mut n: i32 = 0;
    while n * n * n < a {
        n += 1;
    }
    n * n * n == a
}
}
