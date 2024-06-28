/// Implement the function f that takes n as a parameter,
/// and returns a Vec of size n, such that the value of the element at index i is the factorial of i if i is even
/// or the sum of numbers from 1 to i otherwise.
/// i starts from 1.
/// the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
/// Example:
/// f(5) == [1, 2, 6, 24, 15]

use vstd::prelude::*;
fn main() {}

verus!{
fn f(n: usize) -> (result: Vec<u64>) {
    
    let mut result = Vec::with_capacity(n);
    let mut i = 1;
    while i <= n {
        if i % 2 == 0 {
            // Even index, calculate factorial
            let mut factorial = 1;
            let mut j = 1;
            while j <= i {
                factorial *= j as u64;
                j += 1;
            }
            result.push(factorial);
        } else {
            // Odd index, calculate sum
            let mut sum = 0;
            let mut x = 1;
            while x <= i {
                sum += x as u64;
                x += 1;
            }
            result.push(sum);
        }
        i += 1;
    }
    result
}
}