/// Write a function count_nums which takes an array of integers and returns
/// the number of elements which has a sum of digits > 0.
/// If a number is negative, then its first signed digit will be negative:
/// e.g. -123 has signed digits -1, 2, and 3.

use vstd::prelude::*;
fn main() {}

verus!{

fn digit_sum(x: i32) -> i32 {
    let mut sum = 0;
    let mut n = if x < 0 { -x as u32 } else { x as u32 }; // Convert to unsigned
    while n > 0 {
        sum += (n % 10) as i32; // Perform modulo as unsigned, then convert to signed
        n /= 10;
    }
    if x < 0 { -sum - 2 } else { sum } // Adjust for negative inputs
}

fn count_nums(arr: Vec<i32>) -> (count: usize) {
    let mut count = 0;
    let mut i = 0;
    while i < arr.len() {
        let sum = digit_sum(arr[i]);
        if sum > 0 {
            count += 1;
        }
        i += 1;
    }
    count
}

}
