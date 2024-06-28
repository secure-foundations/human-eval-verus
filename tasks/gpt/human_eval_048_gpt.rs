/// Checks if given string is a palindrome
///
/// # Examples
///
/// ```
/// assert_eq!(is_palindrome(""), true);
/// assert_eq!(is_palindrome("aba"), true);
/// assert_eq!(is_palindrome("aaaaa"), true);
/// assert_eq!(is_palindrome("zbcd"), false);
/// ```

use vstd::prelude::*;

fn main() {}

verus!{
    fn is_palindrome(chars: &Vec<char>) -> (result: bool) {
        let mut i = 0;
        let mut j = chars.len();
        if j == 0 {
            return true;
        }
        j -= 1;
        while i < j {
            if chars[i] != chars[j] {
                return false;
            }
            i += 1;
            if i == j {
                break;
            }
            j -= 1;
        }
        true
    }
}
