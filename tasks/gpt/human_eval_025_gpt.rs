/// Return list of prime factors of given integer in the order from smallest to largest.
/// Each of the factors should be listed number of times corresponding to how many times it appears in factorization.
/// Input number should be equal to the product of all factors.
///
/// # Examples
///
/// ```
/// assert_eq!(factorize(8), vec![2, 2, 2]);
/// assert_eq!(factorize(25), vec![5, 5]);
/// assert_eq!(factorize(70), vec![2, 5, 7]);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn factorize(n: u32) -> (factors: Vec<u32>) {
    
    let mut factors = Vec::new();
    let mut number = n;
    let mut divisor = 2;

    while number > 1 {
        while number % divisor == 0 {
            factors.push(divisor);
            number /= divisor;
        }
        divisor += 1;
    }

    factors
}
}
