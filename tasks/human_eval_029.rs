/*
### ID
HumanEval/29
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
from typing import List


def filter_by_prefix(strings: List[str], prefix: str) -> List[str]:
    """ Filter an input list of strings only for ones that start with a given prefix.
    >>> filter_by_prefix([], 'a')
    []
    >>> filter_by_prefix(['abc', 'bcd', 'cde', 'array'], 'a')
    ['abc', 'array']
    """

*/

/*
### ENTRY POINT
filter_by_prefix
*/

/*
### CANONICAL SOLUTION
    return [x for x in strings if x.startswith(prefix)]

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([], 'john') == []
    assert candidate(['xxx', 'asd', 'xxy', 'john doe', 'xxxAAA', 'xxx'], 'xxx') == ['xxx', 'xxxAAA', 'xxx']

*/
