/// Insert a number `delimiter` between every two consecutive elements of input vector `numbers`
///
/// # Examples
///
/// ```
/// # fn main() {
/// assert_eq!(intersperse(vec![], 4), vec![]);
/// assert_eq!(intersperse(vec![1, 2, 3], 4), vec![1, 4, 2, 4, 3]);
/// # }
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn intersperse(numbers: Vec<i32>, delimiter: i32) -> (result: Vec<i32>) {
    
    let mut result = Vec::new();
    let len = numbers.len();
    let mut index = 0;
    while index < len {
        result.push(numbers[index]);
        if index < len - 1 {
            result.push(delimiter);
        }
        index += 1;
    }
    result
}
}
