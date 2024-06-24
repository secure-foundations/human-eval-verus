
/*
### ID
HumanEval/27
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

    // TODO: Put your solution (the specification, implementation, and proof) to the task here
 

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def flip_case(string: str) -> str:
    """ For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
    >>> flip_case('Hello')
    'hELLO'
    """

*/

/*
### ENTRY POINT
flip_case
*/

/*
### CANONICAL SOLUTION
    return string.swapcase()

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == ''
    assert candidate('Hello!') == 'hELLO!'
    assert candidate('These violent delights have violent ends') == 'tHESE VIOLENT DELIGHTS HAVE VIOLENT ENDS'

*/

