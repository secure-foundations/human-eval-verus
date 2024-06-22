/// Write a function that takes an array of numbers as input and returns 
/// the number of elements in the array that are greater than 10 and both 
/// first and last digits of a number are odd (1, 3, 5, 7, 9).
/// For example:
/// special_filter(&[15, -73, 14, -15]) => 1 
/// special_filter(&[33, -2, -3, 45, 21, 109]) => 2

use vstd::prelude::*;
fn main() {}

verus!{

fn special_filter(nums: Vec<i32>) -> (ret: usize)
{
    let mut count = 0;
    let mut i = 0;
    while i < nums.len()
    {
        let num = nums[i];
        if num > 10 && is_odd_first_and_last_digit(num)
        {
            count += 1;
        }
        i += 1;
    }
    count
}

fn is_odd_first_and_last_digit(num: i32) -> (ret: bool)
{
    // Convert to unsigned to perform the division and modulo operations
    let num_u = num as u32;
    let last_digit = num_u % 10;
    let mut first_digit = num_u;
    while first_digit >= 10 {
        first_digit /= 10;
    }
    is_odd_digit(first_digit as i32) && is_odd_digit(last_digit as i32)
}

fn is_odd_digit(digit: i32) -> (ret: bool)
{
    match digit {
        1 | 3 | 5 | 7 | 9 => true,
        _ => false,
    }
}
}
