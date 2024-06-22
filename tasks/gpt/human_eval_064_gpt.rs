/// Write a function vowels_count which takes a string representing
/// a word as input and returns the number of vowels in the string.
/// Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
/// vowel, but only when it is at the end of the given word.
///
/// Example:
/// ```
/// assert_eq!(vowels_count("abcde"), 2);
/// assert_eq!(vowels_count("ACEDY"), 3);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn vowels_count(chars: &Vec<char>) -> (count: usize) {
    
    let mut count = 0;
    let length = chars.len();

    let mut i = 0;
    while i < length {
        let c = chars[i];
        let lower_c = match c {
            'A'..='Z' => (c as u8 - 'A' as u8 + 'a' as u8) as char,
            'a'..='z' => c,
            _ => c,
        };
        match lower_c {
            'a' | 'e' | 'i' | 'o' | 'u' => count += 1,
            'y' if i == length - 1 => count += 1,
            _ => {}
        }
        i += 1;
    }

    count
}
}
