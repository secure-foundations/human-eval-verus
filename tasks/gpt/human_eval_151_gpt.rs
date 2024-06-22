/// Given a list of numbers, return the sum of squares of the numbers
/// in the list that are odd. Ignore numbers that are negative or not integers.
///
/// # Examples
///
/// ```
/// assert_eq!(double_the_difference(vec![1, 3, 2, 0]), 10);
/// assert_eq!(double_the_difference(vec![-1, -2, 0]), 0);
/// assert_eq!(double_the_difference(vec![9, -2]), 81);
/// assert_eq!(double_the_difference(vec![0]), 0);
/// 
/// If the input list is empty, return 0.
/// ```
use vstd::prelude::*;
fn main() {}

verus!{
fn double_the_difference(lst: Vec<i32>) -> (ret: i32) {
    let mut sum: i32 = 0;
    let mut index = 0;
    while index < lst.len() {
        let x = lst[index];
        if x > 0 && (x & 1) == 1 { // Using bitwise AND to check if x is odd
            sum += x * x;
        }
        index += 1;
    }
    sum
}
}