/// Given an integer, return a tuple that has the number of even and odd digits respectively.
///
/// # Examples
///
/// ```
/// assert_eq!(even_odd_count(-12), (1, 1));
/// assert_eq!(even_odd_count(123), (1, 2));
/// ```

use vstd::prelude::*;
fn main() {}

verus!{

struct EvenOddCount {
    even_count: i32,
    odd_count: i32,
}

fn even_odd_count(num: i32) -> EvenOddCount {
    
    let mut num = if num < 0 { -num } else { num } as u32; // Convert to unsigned
    let mut even_count = 0;
    let mut odd_count = 0;

    while num > 0 {
        if num % 2 == 0 {
            even_count += 1;
        } else {
            odd_count += 1;
        }
        num /= 10;
    }

    EvenOddCount {
        even_count: even_count,
        odd_count: odd_count,
    }
}
}
