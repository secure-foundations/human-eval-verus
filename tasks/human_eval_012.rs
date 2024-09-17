/*
### ID
HumanEval/12
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn longest(strings: &Vec<Vec<u8>>) -> (result: Option<&Vec<u8>>)
    ensures
        match result {
            None => strings.len() == 0,
            Some(s) => {
                forall|i: int|
                    #![auto]
                    0 <= i < strings.len() ==> s.len() >= strings[i].len() && exists|i: int|
                        #![auto]
                        (0 <= i < strings.len() && s == strings[i] && (forall|j: int|
                            #![auto]
                            0 <= j < i ==> strings[j].len() < s.len()))
            },
        },
{
    if strings.len() == 0 {
        return None;
    }
    let mut result: &Vec<u8> = &strings[0];
    let mut pos = 0;

    for i in 1..strings.len()
        invariant
            0 <= pos < i,
            result == &strings[pos as int],
            exists|i: int| 0 <= i < strings.len() && strings[i] == result,
            forall|j: int| #![auto] 0 <= j < i ==> strings[j].len() <= result.len(),
            forall|j: int| #![auto] 0 <= j < pos ==> strings[j].len() < result.len(),
    {
        if result.len() < strings[i].len() {
            result = &strings[i];
            pos = i;
        }
    }
    Some(result)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List, Optional


def longest(strings: List[str]) -> Optional[str]:
    """ Out of list of strings, return the longest one. Return the first one in case of multiple
    strings of the same length. Return None in case the input list is empty.
    >>> longest([])

    >>> longest(['a', 'b', 'c'])
    'a'
    >>> longest(['a', 'bb', 'ccc'])
    'ccc'
    """

*/

/*
### ENTRY POINT
longest
*/

/*
### CANONICAL SOLUTION
    if not strings:
        return None

    maxlen = max(len(x) for x in strings)
    for s in strings:
        if len(s) == maxlen:
            return s

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == None
    assert candidate(['x', 'y', 'z']) == 'x'
    assert candidate(['x', 'yyy', 'zzzz', 'www', 'kkkk', 'abc']) == 'zzzz'

*/
