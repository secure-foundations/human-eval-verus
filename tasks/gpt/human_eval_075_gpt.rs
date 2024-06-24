/// Write a function that returns true if the given number is the multiplication of 3 prime numbers
/// and false otherwise.
/// Knowing that (a) is less then 100. 
/// Example:
/// is_multiply_prime(30) == true
/// 30 = 2 * 3 * 5

use vstd::prelude::*;
fn main() {}

verus!{
fn is_multiply_prime(a: u32) -> (result: bool) {
    
    if a < 6 {
        return false; // The smallest product of 3 primes is 2*2*3 = 12
    }

    let mut count = 0;
    let mut num = a;

    let mut i = 2;
    while i < 100 {
        while num % i == 0 {
            count += 1;
            num /= i;
            if count > 3 {
                return false; // More than 3 prime factors
            }
        }
        i += 1;
    }

    count == 3 // Must have exactly 3 prime factors
}
}
