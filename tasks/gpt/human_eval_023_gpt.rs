/// Return length of given string
///
/// # Examples
///
/// ```
/// assert_eq!(strlen(""), 0);
/// assert_eq!(strlen("abc"), 3);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn strlen(string: Vec<char>) -> (ret: usize) {
    let mut count: usize = 0;
    
    let mut i = 0;
    while i < string.len() {
        count += 1;
        i += 1;
    }
    
    count
}
}
