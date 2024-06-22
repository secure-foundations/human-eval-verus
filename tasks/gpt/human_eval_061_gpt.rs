/// brackets is a string of "(" and ")".
/// return True if every opening bracket has a corresponding closing bracket.
///
/// # Examples
///
/// ```
/// assert_eq!(correct_bracketing("("), false);
/// assert_eq!(correct_bracketing("()"), true);
/// assert_eq!(correct_bracketing("(()())"), true);
/// assert_eq!(correct_bracketing(")(()"), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn correct_bracketing(brackets: Vec<char>) -> (result: bool) {
    
    let mut balance = 0;
    let mut i = 0;
    while i < brackets.len() {
        match brackets[i] {
            '(' => balance += 1,
            ')' => {
                if balance == 0 {
                    return false;
                }
                balance -= 1;
            }
            _ => {}
        }
        i += 1;
    }
    balance == 0
}
}
