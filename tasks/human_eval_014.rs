
/*
### ID
HumanEval/14
*/

/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

 

} // verus!

fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def all_prefixes(string: str) -> List[str]:
    """ Return list of all prefixes from shortest to longest of the input string
    >>> all_prefixes('abc')
    ['a', 'ab', 'abc']
    """

*/

/*
### ENTRY POINT
all_prefixes
*/

/*
### CANONICAL SOLUTION
    result = []

    for i in range(len(string)):
        result.append(string[:i+1])
    return result

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('') == []
    assert candidate('asdfgh') == ['a', 'as', 'asd', 'asdf', 'asdfg', 'asdfgh']
    assert candidate('WWW') == ['W', 'WW', 'WWW']

*/

