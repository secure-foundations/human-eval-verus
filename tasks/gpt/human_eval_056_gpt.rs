/// brackets is a string of "<" and ">".
/// return True if every opening bracket has a corresponding closing bracket.
///
/// # Examples
///
/// ```
/// assert_eq!(correct_bracketing("<"), false);
/// assert_eq!(correct_bracketing("<>"), true);
/// assert_eq!(correct_bracketing("<<><>>"), true);
/// assert_eq!(correct_bracketing("><<>"), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn correct_bracketing(brackets: Vec<char>) -> (result: bool) {
    
    let mut count = 0;
    let mut i = 0;
    while i < brackets.len() {
        match brackets[i] {
            '<' => count += 1,
            '>' => {
                if count == 0 {
                    return false;
                }
                count -= 1;
            }
            _ => {}
        }
        i += 1;
    }
    count == 0
}
}
