/// Your task is to write a function that returns true if a number x is a simple
/// power of n and false in other cases.
/// x is a simple power of n if n**int=x
/// For example:
/// is_simple_power(1, 4) => true
/// is_simple_power(2, 2) => true
/// is_simple_power(8, 2) => true
/// is_simple_power(3, 2) => false
/// is_simple_power(3, 1) => false
/// is_simple_power(5, 3) => false

use vstd::prelude::*;
fn main() {}

verus!{
fn is_simple_power(x: i32, n: i32) -> (result: bool) {
    
    if n <= 1 {
        return x == n;
    }

    let mut power = n;
    while power <= x {
        if power == x {
            return true;
        }
        match power.checked_mul(n) {
            Some(next_power) => power = next_power,
            None => break,
        }
    }

    false
}
}
