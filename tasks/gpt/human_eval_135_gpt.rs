/// Create a function which returns the largest index of an element which
/// is not greater than or equal to the element immediately preceding it. If
/// no such element exists then return -1. The given array will not contain
/// duplicate values.
///
/// Examples:
/// can_arrange([1,2,4,3,5]) = 3
/// can_arrange([1,2,3]) = -1

use vstd::prelude::*;
fn main() {}

verus!{
fn can_arrange(arr: Vec<i32>) -> (ret: i32) {
    let mut i = arr.len() as i32 - 1;
    while i > 0 {
        if arr[i as usize] < arr[(i - 1) as usize] {
            return i;
        }
        i -= 1;
    }
    -1
}
}
