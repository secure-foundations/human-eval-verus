/*
### ID
HumanEval/134
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

pub spec fn is_alphabetic(c: char) -> (result: bool);

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_alphabetic)]
pub fn ex_is_alphabetic(c: char) -> (result: bool)
    ensures
        result <==> (c.is_alphabetic()),
{
    c.is_alphabetic()
}

pub spec fn is_whitespace(c: char) -> (result: bool);

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_whitespace)]
pub fn ex_is_whitespace(c: char) -> (result: bool)
    ensures
        result <==> (c.is_whitespace()),
{
    c.is_whitespace()
}

fn check_if_last_char_is_a_letter(txt: &str) -> (result: bool)
    ensures
        result <==> (txt@.len() > 0 && txt@.last().is_alphabetic() && (txt@.len() == 1
            || txt@.index(txt@.len() - 2).is_whitespace())),
{
    let len = txt.unicode_len();
    if len == 0 {
        return false;
    }
    txt.get_char(len - 1).is_alphabetic() && (len == 1 || txt.get_char(len - 2).is_whitespace())
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def check_if_last_char_is_a_letter(txt):
    '''
    Create a function that returns True if the last character
    of a given string is an alphabetical character and is not
    a part of a word, and False otherwise.
    Note: "word" is a group of characters separated by space.

    Examples:
    check_if_last_char_is_a_letter("apple pie") ➞ False
    check_if_last_char_is_a_letter("apple pi e") ➞ True
    check_if_last_char_is_a_letter("apple pi e ") ➞ False
    check_if_last_char_is_a_letter("") ➞ False
    '''

*/

/*
### ENTRY POINT
check_if_last_char_is_a_letter
*/

/*
### CANONICAL SOLUTION

    check = txt.split(' ')[-1]
    return True if len(check) == 1 and (97 <= ord(check.lower()) <= 122) else False

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate("apple") == False
    assert candidate("apple pi e") == True
    assert candidate("eeeee") == False
    assert candidate("A") == True
    assert candidate("Pumpkin pie ") == False
    assert candidate("Pumpkin pie 1") == False
    assert candidate("") == False
    assert candidate("eeeee e ") == False
    assert candidate("apple pie") == False
    assert candidate("apple pi e ") == False

    # Check some edge cases that are easy to work out by hand.
    assert True


*/
