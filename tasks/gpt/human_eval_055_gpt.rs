/// Return n-th Fibonacci number.
///
/// # Examples
///
/// ```
/// assert_eq!(fib(10), 55);
/// assert_eq!(fib(1), 1);
/// assert_eq!(fib(8), 21);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn fib(n: u32) -> (ret: u32) {
    
    match n {
        0 => 0,
        1 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}
}