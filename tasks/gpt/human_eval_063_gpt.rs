/// The FibFib number sequence is a sequence similar to the Fibonacci sequence that's defined as follows:
/// fibfib(0) == 0
/// fibfib(1) == 0
/// fibfib(2) == 1
/// fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3).
/// Please write a function to efficiently compute the n-th element of the fibfib number sequence.

use vstd::prelude::*;
fn main() {}

verus!{
fn fibfib(n: u32) -> (ret: u32) {
    
    match n {
        0 => 0,
        1 => 0,
        2 => 1,
        _ => {
            let mut a = 0;
            let mut b = 0;
            let mut c = 1;
            let mut d;
            let mut i = 3;
            while i <= n {
                d = a + b + c;
                a = b;
                b = c;
                c = d;
                i += 1;
            }
            c
        }
    }
}
}