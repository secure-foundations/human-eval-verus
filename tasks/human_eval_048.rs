
/*
### ID
HumanEval/48
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)
    ensures
        result == forall |i: int| 0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i]
{
    let text_len: usize = text.unicode_len();
    for pos in 0..text_len / 2
        invariant
            text_len == text@.len(),
            forall |i: int| 0 <= i < pos ==> #[trigger] text@[i] == text@[text_len - 1 - i],
    {
        if text.get_char(pos) != text.get_char(text_len - 1 - pos) {
            return false;
        }
    }
    true
}

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def is_palindrome(text: str):
    """
    Checks if given string is a palindrome
    >>> is_palindrome('')
    True
    >>> is_palindrome('aba')
    True
    >>> is_palindrome('aaaaa')
    True
    >>> is_palindrome('zbcd')
    False
    """

*/

/*
### ENTRY POINT
is_palindrome
*/

/*
### CANONICAL SOLUTION
    for i in range(len(text)):
        if text[i] != text[len(text) - 1 - i]:
            return False
    return True

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate('') == True
    assert candidate('aba') == True
    assert candidate('aaaaa') == True
    assert candidate('zbcd') == False
    assert candidate('xywyx') == True
    assert candidate('xywyz') == False
    assert candidate('xywzx') == False


*/

