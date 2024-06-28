/// Check if in given list of numbers, are any two numbers closer to each other than
/// given threshold.
///
/// # Examples
///
/// ```
/// # use your_crate::has_close_elements;
/// assert_eq!(has_close_elements(&[1.0, 2.0, 3.0], 0.5), false);
/// assert_eq!(has_close_elements(&[1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3), true);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn has_close_elements(numbers: Vec<i32>, threshold: i32) -> (result: bool) {
    let mut i = 0;
    while i < numbers.len() {
        let num = numbers[i];
        let mut j = i + 1;
        while j < numbers.len() {
            let other_num = numbers[j];
            if num > other_num && num - other_num < threshold {
                return true;
            }
            if num <= other_num && other_num - num < threshold {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
}
