/// Implement a function that takes a non-negative integer and returns a Vec of the first n
/// integers that are prime numbers and less than n.
/// 
/// # Examples
/// 
/// ```
/// assert_eq!(count_up_to(5), vec![2, 3]);
/// assert_eq!(count_up_to(11), vec![2, 3, 5, 7]);
/// assert_eq!(count_up_to(0), vec![]);
/// assert_eq!(count_up_to(20), vec![2, 3, 5, 7, 11, 13, 17, 19]);
/// assert_eq!(count_up_to(1), vec![]);
/// assert_eq!(count_up_to(18), vec![2, 3, 5, 7, 11, 13, 17]);
/// ```
/// 
/// # Arguments
/// 
/// * `n` - A non-negative integer

use vstd::prelude::*;
fn main() {}

verus!{
fn count_up_to(n: u32) -> (primes: Vec<u32>) {
    
    let mut primes = Vec::new();

    let mut i = 2;
    while i < n {
        let mut is_prime = true;
        let mut j = 2;
        while j <= integer_sqrt(i) {
            if i % j == 0 {
                is_prime = false;
                break;
            }
            j += 1;
        }
        if is_prime {
            primes.push(i);
        }
        i += 1;
    }

    primes
}

fn integer_sqrt(num: u32) -> u32 {
    let mut root = 0;
    let mut bit = 1 << 30; // The second-to-top bit is set: 1 << 30 for 32 bits
    let mut num_mut = num; // Use a mutable local variable

    // "bit" starts at the highest power of four <= the argument.
    while bit > num_mut {
        bit >>= 2;
    }

    while bit != 0 {
        if num_mut >= root + bit {
            num_mut -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    root
}
}
