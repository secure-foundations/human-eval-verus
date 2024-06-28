/// Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in 
/// the last couple centuries. However, what people don't know is Tribonacci sequence.
/// Tribonacci sequence is defined by the recurrence:
/// tri(1) = 3
/// tri(n) = 1 + n / 2, if n is even.
/// tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd.
/// For example:
/// tri(2) = 1 + (2 / 2) = 2
/// tri(4) = 3
/// tri(3) = tri(2) + tri(1) + tri(4)
///        = 2 + 3 + 3 = 8 
/// You are given a non-negative integer number n, you have to a return a list of the 
/// first n + 1 numbers of the Tribonacci sequence.
/// Examples:
/// tri(3) = [1, 3, 2, 8]

use vstd::prelude::*;
fn main() {}

verus!{
fn tri(n: u32) -> (sequence: Vec<u32>) {
    
    let mut sequence = Vec::new();
    sequence.push(1);
    sequence.push(3);
    sequence.push(2);
    
    if n < 3 {
        while sequence.len() > (n + 1) as usize {
            sequence.pop();
        }
        return sequence;
    }
    
    let mut i = 3;
    while i <= n {
        let next_val = if i % 2 == 0 {
            1 + i / 2
        } else {
            sequence[(i - 1) as usize] + sequence[(i - 2) as usize] + sequence[(i - 3) as usize]
        };
        sequence.push(next_val);
        i += 1;
    }
    sequence
}
}
