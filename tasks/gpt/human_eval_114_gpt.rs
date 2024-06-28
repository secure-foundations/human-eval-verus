/// Given an array of integers nums, find the minimum sum of any non-empty sub-array
/// of nums.
///
/// # Examples
///
/// ```
/// assert_eq!(min_sub_array_sum(&[2, 3, 4, 1, 2, 4]), 1);
/// assert_eq!(min_sub_array_sum(&[-1, -2, -3]), -6);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn min_sub_array_sum(nums: Vec<i32>) -> (ret: i32) {
    
    let mut min_sum = nums[0];
    let mut current_sum = nums[0];

    let mut i = 1;
    while i < nums.len() {
        let num = nums[i];
        current_sum = if current_sum < 0 { current_sum } else { 0 } + num;
        min_sum = if min_sum < current_sum { min_sum } else { current_sum };
        i += 1;
    }

    min_sum
}
}
