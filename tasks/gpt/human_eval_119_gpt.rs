/// You are given a list of two strings, both strings consist of open
/// parentheses '(' or close parentheses ')' only.
/// Your job is to check if it is possible to concatenate the two strings in
/// some order, that the resulting string will be good.
/// A string S is considered to be good if and only if all parentheses in S
/// are balanced. For example: the string '(())()' is good, while the string
/// '())' is not.
/// Return 'Yes' if there's a way to make a good string, and return 'No' otherwise.
///
/// Examples:
/// match_parens(vec!["()(", ")"]) == "Yes"
/// match_parens(vec![")", ")"]) == "No"

use vstd::prelude::*;
fn main() {}

verus!{
fn match_parens(lst: Vec<Vec<char>>) -> (bool) {
    
    let mut balance = 0;
    let mut i = 0;
    let mut j;
    while i < lst.len() {
        let s = &lst[i];
        j = 0;
        while j < s.len() {
            let c = s[j];
            if c == '(' {
                balance += 1;
            } else if c == ')' {
                balance -= 1;
            }
            if balance < 0 {
                break;
            }
            j += 1;
        }
        if balance < 0 {
            break;
        }
        i += 1;
    }

    if balance == 0 {
        true
    } else {
        // Check if swapping the strings can make it balanced
        balance = 0;
        i = lst.len();
        while i > 0 {
            i -= 1;
            let s = &lst[i];
            j = 0;
            while j < s.len() {
                let c = s[j];
                if c == '(' {
                    balance += 1;
                } else if c == ')' {
                    balance -= 1;
                }
                if balance < 0 {
                    return false;
                }
                j += 1;
            }
        }
        balance == 0
    }
}
}
