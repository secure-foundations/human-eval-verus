/// Given two positive integers a and b, return the even digits between a
/// and b, in ascending order.
///
/// For example:
/// generate_integers(2, 8) => [2, 4, 6, 8]
/// generate_integers(8, 2) => [2, 4, 6, 8]
/// generate_integers(10, 14) => []

use vstd::prelude::*;
fn main() {}

verus!{
fn generate_integers(a: u32, b: u32) -> (ret: Vec<u32>) 
{
    let start: u32;
    let end: u32;
    if a < b {
        start = a;
        end = b;
    } else {
        start = b;
        end = a;
    }
    
    let mut result: Vec<u32> = Vec::new();
    let mut x = start;
    while x <= end {
        if x % 2 == 0 {
            result.push(x);
        }
        x += 1;
    }
    result
}
}