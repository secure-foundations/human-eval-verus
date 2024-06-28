/// Task
/// Write a function that takes a string as input and returns the sum of the upper characters only'
/// ASCII codes.
///
/// Examples:
///     digit_sum("") => 0
///     digit_sum("abAB") => 131
///     digit_sum("abcCd") => 67
///     digit_sum("helloE") => 69
///     digit_sum("woArBld") => 131
///     digit_sum("aAaaaXa") => 153

use vstd::prelude::*;
fn main() {}

verus!{
fn digit_sum(s: &[u8]) -> (ret: u32)
{
    let mut sum: u32 = 0;
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        // Check if c is an uppercase ASCII letter using ASCII values directly
        if c >= 65 && c <= 90 { // ASCII values for 'A' and 'Z'
            sum += (c - 65) as u32 + 10; // Convert 'A'..'Z' to 10..35
        }
        i += 1;
    }
    sum
}
}
