/// Return true if a given number is prime, and false otherwise.
///
/// # Examples
///
/// ```
/// assert_eq!(is_prime(6), false);
/// assert_eq!(is_prime(101), true);
/// assert_eq!(is_prime(11), true);
/// assert_eq!(is_prime(13441), true);
/// assert_eq!(is_prime(61), true);
/// assert_eq!(is_prime(4), false);
/// assert_eq!(is_prime(1), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn is_prime(n: u64) -> (result: bool) {
    
    if n <= 1 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }
    let mut i = 5u64;
    while i * i <= n {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i += 6;
    }
    true
}
}
