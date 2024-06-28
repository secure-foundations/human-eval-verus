/// Return the number of times the digit 7 appears in integers less than `n` which are divisible by 11 or 13.

use vstd::prelude::*;
fn main() {}

verus!{
fn fizz_buzz(n: i32) -> (count: i32) {
    let mut count = 0;
    let mut i = 1;
    while i < n {
        // Cast i to u32 before modulo operation
        if (i as u32) % 11 == 0 || (i as u32) % 13 == 0 {
            // Convert the result of count_sevens (which is usize) to i32
            count += count_sevens(i) as i32;
        }
        i += 1;
    }
    count
}

fn count_sevens(mut num: i32) -> (count: usize) {
    let mut count = 0;
    while num > 0 {
        // Cast num to u32 before modulo operation
        if (num as u32) % 10 == 7 {
            count += 1;
        }
        // Cast num to u32 before division operation
        num = (num as u32 / 10) as i32;
    }
    count
}
}
