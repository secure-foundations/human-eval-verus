/// prime_fib returns n-th number that is a Fibonacci number and it's also prime.
///
/// # Examples
///
/// ```
/// let result = prime_fib(1);
/// assert_eq!(result, 2);
///
/// let result = prime_fib(2);
/// assert_eq!(result, 3);
///
/// let result = prime_fib(3);
/// assert_eq!(result, 5);
///
/// let result = prime_fib(4);
/// assert_eq!(result, 13);
///
/// let result = prime_fib(5);
/// assert_eq!(result, 89);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{

fn prime_fib(n: u32) -> (ret: u32) {
    
    let mut prime_fibs = Vec::new();
    let mut fib_prev = 0;
    let mut fib_curr = 1;

    while prime_fibs.len() < n as usize {
        let fib_next = fib_prev + fib_curr;
        fib_prev = fib_curr;
        fib_curr = fib_next;

        if is_prime(fib_curr) {
            prime_fibs.push(fib_curr);
        }
    }

    prime_fibs[(n - 1) as usize]
}

fn is_prime(num: u32) -> (ret: bool) {
    if num <= 1 {
        return false;
    }
    if num <= 3 {
        return true;
    }
    if num % 2 == 0 || num % 3 == 0 {
        return false;
    }
    let mut i = 5;
    while i * i <= num {
        if num % i == 0 || num % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}
}
