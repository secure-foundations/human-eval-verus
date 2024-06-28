/*
### ID
HumanEval/23
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn strlen(string: &Vec<char>) -> (length: usize)
    ensures
        length
            == string.len(),  // The length returned is equal to the length of the string
{
    string.len()
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def strlen(string: str) -> int:
    """ Return length of given string
    >>> strlen('')
    0
    >>> strlen('abc')
    3
    """

*/

/*
### ENTRY POINT
strlen
*/

/*
### CANONICAL SOLUTION
    return len(string)

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == 0
    assert candidate('x') == 1
    assert candidate('asdasnakj') == 9

*/
