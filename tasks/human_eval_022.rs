
/*
### ID
HumanEval/22
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
from typing import List, Any


def filter_integers(values: List[Any]) -> List[int]:
    """ Filter given list of any python values only for integers
    >>> filter_integers(['a', 3.14, 5])
    [5]
    >>> filter_integers([1, 2, 3, 'abc', {}, []])
    [1, 2, 3]
    """

*/

/*
### ENTRY POINT
filter_integers
*/

/*
### CANONICAL SOLUTION
    return [x for x in values if isinstance(x, int)]

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == []
    assert candidate([4, {}, [], 23.2, 9, 'adasd']) == [4, 9]
    assert candidate([3, 'c', 3, 3, 'a', 'b']) == [3, 3, 3]

*/

