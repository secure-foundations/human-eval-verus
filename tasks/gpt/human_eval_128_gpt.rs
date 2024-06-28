/// You are given an array arr of integers and you need to return
/// sum of magnitudes of integers multiplied by product of all signs
/// of each number in the array, represented by 1, -1 or 0.
/// Note: return None for empty arr.
///
/// Example:
/// assert_eq!(prod_signs(vec![1, 2, 2, -4]), Some(-9));
/// assert_eq!(prod_signs(vec![0, 1]), Some(0));
/// assert_eq!(prod_signs(vec![]), None);

use vstd::prelude::*;
fn main() {}

verus!{
fn prod_signs(arr: Vec<i32>) -> (ret: Option<i32>) {
    
    // Instead of using `is_empty`, we can check the length directly.
    if arr.len() == 0 {
        return None;
    }

    let mut sign_product = 1;
    let mut magnitude_sum = 0;
    let mut i = 0;

    while i < arr.len() {
        let num = arr[i];
        sign_product *= if num < 0 { -1 } else { 1 }; // Instead of num.signum()
        magnitude_sum += if num < 0 { -num } else { num }; // Instead of num.abs()
        i += 1;
    }

    Some(magnitude_sum * sign_product)
}
}
