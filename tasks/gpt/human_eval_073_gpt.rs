/// Given an array arr of integers, find the minimum number of elements that
/// need to be changed to make the array palindromic. A palindromic array is an array that
/// is read the same backwards and forwards. In one change, you can change one element to any other element.
///
/// For example:
/// smallest_change(vec![1,2,3,5,4,7,9,6]) == 4
/// smallest_change(vec![1, 2, 3, 4, 3, 2, 2]) == 1
/// smallest_change(vec![1, 2, 3, 2, 1]) == 0

use vstd::prelude::*;
fn main() {}

verus!{
fn smallest_change(arr: Vec<i32>) -> (changes: i32) {
    
    let mut changes = 0;
    let mut left = 0;
    let mut right = arr.len() as i32 - 1; // Cast to i32 to match the type of left and right

    while left < right {
        if arr[left as usize] != arr[right as usize] { // Cast to usize for indexing
            changes += 1;
        }
        left += 1;
        right -= 1;
    }

    changes
}
}
