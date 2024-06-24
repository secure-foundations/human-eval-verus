/// For a given list of input numbers, calculate Mean Absolute Deviation
/// around the mean of this dataset.
/// Mean Absolute Deviation is the average absolute difference between each
/// element and a centerpoint (mean in this case):
/// MAD = average | x - x_mean |
///
/// # Examples
///
/// ```
/// let values = vec![1.0, 2.0, 3.0, 4.0];
/// let mad = mean_absolute_deviation(&values);
/// assert_eq!(mad, 1.0);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn mean_absolute_deviation(numbers: Vec<i64>) -> (ret:i64) {
    
    if numbers.len() == 0 {
        return 0;
    }
    let mut sum: i64 = 0;
    let mut count: usize = 0;
    let mut i = 0;
    while i < numbers.len() {
        sum += numbers[i];
        count += 1;
        i += 1;
    }
    // Convert sum to unsigned for division
    let mean: i64 = (sum as u64 / count as u64) as i64;
    
    let mut sum_abs_deviation: i64 = 0;
    i = 0;
    while i < numbers.len() {
        let deviation = if numbers[i] > mean { numbers[i] - mean } else { mean - numbers[i] };
        sum_abs_deviation += deviation;
        i += 1;
    }
    // Convert sum_abs_deviation to unsigned for division
    (sum_abs_deviation as u64 / count as u64) as i64
}
}
