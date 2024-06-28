/// Given a positive integer n, return a tuple that has the number of even and odd
/// integer palindromes that fall within the range(1, n), inclusive.
///
/// Example 1:
///
///     Input: 3
///     Output: (1, 2)
///     Explanation:
///     Integer palindrome are 1, 2, 3. one of them is even, and two of them are odd.
///
/// Example 2:
///
///     Input: 12
///     Output: (4, 6)
///     Explanation:
///     Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, and 6 of them are odd.
///
/// Note:
///     1. 1 <= n <= 10^3
///     2. returned tuple has the number of even and odd integer palindromes respectively.

use vstd::prelude::*;
fn main() {}

verus!{

fn even_count_palindrome(n: u32) -> (even_count: u32) {
    let mut even_count = 0;
    let mut i = 1;

    while i <= n {
        if is_palindrome(i) {
            if i % 2 == 0 {
                even_count += 1;
            }
        }
        i += 1;
    }

    even_count
}

fn odd_count_palindrome(n: u32) -> (odd_count: u32) {
    let mut odd_count = 0;
    let mut i = 1;

    while i <= n {
        if is_palindrome(i) {
            if i % 2 != 0 {
                odd_count += 1;
            }
        }
        i += 1;
    }

    odd_count
}

fn is_palindrome(mut num: u32) -> (result: bool) {
    let original = num;
    let mut reversed = 0;

    while num > 0 {
        reversed = reversed * 10 + num % 10;
        num /= 10;
    }

    original == reversed
}
}
