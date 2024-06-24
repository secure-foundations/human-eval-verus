/// You are given a list of integers.
/// You need to find the largest prime value and return the sum of its digits.
///
/// Examples:
/// For lst = [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] the output should be 10
/// For lst = [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] the output should be 25
/// For lst = [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] the output should be 13
/// For lst = [0,724,32,71,99,32,6,0,5,91,83,0,5,6] the output should be 11
/// For lst = [0,81,12,3,1,21] the output should be 3
/// For lst = [0,8,1,2,1,7] the output should be 7

use vstd::prelude::*;
fn main() {}

verus!{

fn is_prime(n: i32) -> (ret: bool) {
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    // Convert to unsigned to perform modulo operations
    let n_unsigned = n as u32;
    if n_unsigned % 2 == 0 || n_unsigned % 3 == 0 {
        return false;
    }
    let mut i = 5u32;
    while (i as i32) * (i as i32) <= n {
        if n_unsigned % i == 0 || n_unsigned % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}

fn sum_of_digits(mut n: i32) -> (ret: i32) {
    let mut sum = 0;
    while n > 0 {
        // Convert to unsigned to perform modulo operation
        sum += (n as u32 % 10) as i32;
        // Convert to unsigned to perform division operation
        n = (n as u32 / 10) as i32;
    }
    sum
}

fn skjkasdkd(lst: Vec<i32>) -> (ret: i32) {
    let mut max_prime = 0;
    let mut found_prime = false;

    let mut i = 0;
    while i < lst.len() {
        let x = lst[i];
        if is_prime(x) {
            if !found_prime || x > max_prime {
                max_prime = x;
                found_prime = true;
            }
        }
        i += 1;
    }

    if found_prime {
        sum_of_digits(max_prime)
    } else {
        0
    }
}
}
