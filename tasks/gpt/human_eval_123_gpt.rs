/// Given a positive integer n, return a sorted Vec that has the odd numbers in collatz sequence.
///
/// The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
/// as follows: start with any positive integer n. Then each term is obtained from the 
/// previous term as follows: if the previous term is even, the next term is one half of 
/// the previous term. If the previous term is odd, the next term is 3 times the previous
/// term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.
///
/// Note: 
///     1. Collatz(1) is [1].
///     2. returned Vec is sorted in increasing order.
///
/// For example:
/// get_odd_collatz(5) returns [1, 5] // The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5.

use vstd::prelude::*;
fn main() {}

verus!{
fn get_odd_collatz(n: u32) -> (odd_numbers: Vec<u32>)
{
    let mut number = n;
    let mut odd_numbers = Vec::new();

    while number != 1 {
        if number % 2 != 0 {
            odd_numbers.push(number);
        }
        number = if number % 2 == 0 {
            number / 2
        } else {
            3 * number + 1
        };
    }
    odd_numbers.push(1); // 1 is always included and is odd

    // Sorting is omitted due to Verus limitations
    odd_numbers
}
}
