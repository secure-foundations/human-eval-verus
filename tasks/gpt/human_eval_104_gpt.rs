/// Given a list of positive integers `x`, return a sorted list of all
/// elements that haven't any even digit.
///
/// Note: Returned list should be sorted in increasing order.
///
/// # Examples
///
/// ```
/// let result = unique_digits(vec![15, 33, 1422, 1]);
/// assert_eq!(result, vec![1, 15, 33]);
///
/// let result = unique_digits(vec![152, 323, 1422, 10]);
/// assert_eq!(result, Vec::<i32>::new());
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn unique_digits(x: Vec<u32>) -> (ret: Vec<u32>)
{
    let mut result: Vec<u32> = Vec::new();
    
    let mut i = 0;
    while i < x.len() {
        let mut num = x[i];
        let mut is_unique = true;
        while num > 0 {
            let digit = num % 10;
            if digit == 0 || digit % 2 == 0 {
                is_unique = false;
                break;
            }
            num /= 10;
        }
        if is_unique {
            result.push(x[i]);
        }
        i += 1;
    }

    // Implementing bubble sort without using the swap method
    let mut n = result.len();
    while n > 0 {
        let mut new_n = 0;
        let mut i = 1;
        while i < n {
            if result[i - 1] > result[i] {
                // Manual swap logic using a temporary variable
                let temp = result[i - 1];
                result.remove(i - 1);
                result.insert(i, temp);
                new_n = i;
            }
            i += 1;
        }
        n = new_n;
    }
    
    result
}
}
