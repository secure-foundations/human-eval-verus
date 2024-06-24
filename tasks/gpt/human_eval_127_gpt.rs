
use vstd::prelude::*;
fn main() {}

verus!{

fn intersection(interval1: (i32, i32), interval2: (i32, i32)) -> (result: bool) {
    
    let start = if interval1.0 > interval2.0 { interval1.0 } else { interval2.0 };
    let end = if interval1.1 < interval2.1 { interval1.1 } else { interval2.1 };
    if start > end {
        return false;
    }
    let length = end - start + 1;
    is_prime(length)
}

fn is_prime(n: i32) -> (result: bool) {
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    if n & 1 == 0 { // Check if n is even using bitwise AND
        return false;
    }
    let mut i = 5;
    while i * i <= n {
        // Since we cannot use the modulo operator, we perform a manual check
        if manual_mod(n, i) == 0 || manual_mod(n, i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}

fn manual_mod(n: i32, divisor: i32) -> (result: i32) {
    let mut remainder = n;
    while remainder >= divisor {
        remainder -= divisor;
    }
    remainder
}
}
