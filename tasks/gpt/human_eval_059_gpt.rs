/// Return the largest prime factor of n. Assume n > 1 and is not a prime.

use vstd::prelude::*;
fn main() {}

verus!{
fn largest_prime_factor(n: u64) -> (largest: u64) {
    
    let mut largest = 0;
    let mut number = n;
    let mut factor = 2;

    while factor * factor <= number {
        while number % factor == 0 {
            number /= factor;
            largest = factor;
        }
        factor += 1;
    }

    if number > 1 {
        largest = number;
    }

    largest
}
}
