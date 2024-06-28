/// From a given list of integers, generate a list of rolling maximum element found until given moment
/// in the sequence.
///
/// # Examples
///
/// ```
/// let result = rolling_max(vec![1, 2, 3, 2, 3, 4, 2]);
/// assert_eq!(result, vec![1, 2, 3, 3, 3, 4, 4]);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>) {
    let mut max_so_far = -2147483648; // Directly using the literal value for i32::MIN
    let mut result = Vec::with_capacity(numbers.len());

    let mut i = 0;
    while i < numbers.len() {
        let number = numbers[i];
        if number > max_so_far {
            max_so_far = number;
        }
        result.push(max_so_far);
        i += 1;
    }

    result
}
}
