/// For a given number n, find the largest number that divides n evenly, smaller than n

use vstd::prelude::*;

fn main() {}

verus!{
fn largest_divisor(n: i32) -> (ret: i32) {
    let mut i = n - 1;
    while i >= 2 {
        let mut temp_n = n;
        // Repeatedly subtract `i` from `temp_n` until `temp_n` is less than `i`
        while temp_n >= i {
            temp_n = temp_n - i;
        }
        // If after subtraction the remainder is 0, `i` is a divisor
        if temp_n == 0 {
            return i;
        }
        i -= 1;
    }
    1
}
}
