/// The Fib4 number sequence is a sequence similar to the Fibonacci sequence that's defined as follows:
/// fib4(0) -> 0
/// fib4(1) -> 0
/// fib4(2) -> 2
/// fib4(3) -> 0
/// fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
/// Please write a function to efficiently compute the n-th element of the fib4 number sequence. Do not use recursion.

use vstd::prelude::*;
fn main() {}

verus!{
fn fib4(n: u32) -> (ret: u32) {
    
    match n {
        0 => 0,
        1 => 0,
        2 => 2,
        3 => 0,
        _ => {
            let mut a = 0;
            let mut b = 0;
            let mut c = 2;
            let mut d = 0;
            let mut e;
            let mut i = 4;
            while i <= n {
                e = a + b + c + d;
                a = b;
                b = c;
                c = d;
                d = e;
                i += 1;
            }
            d
        }
    }
}
}