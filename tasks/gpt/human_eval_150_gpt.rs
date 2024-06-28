/// A simple program which should return the value of x if n is 
/// a prime number and should return the value of y otherwise.
///
/// # Examples
/// ```
/// // for x_or_y(7, 34, 12) == 34
/// // for x_or_y(15, 8, 5) == 5
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn x_or_y(n: u32, x: u32, y: u32) -> (ret: u32) {
    
    if n <= 1 {
        return y;
    }
    if n == 2 {
        return x;
    }
    if n % 2 == 0 {
        return y;
    }
    let mut i = 3;
    while i * i <= n {
        if n % i == 0 {
            return y;
        }
        i += 2;
    }
    x
}
}
