/*
### ID
HumanEval/14
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)
    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
{
    let mut prefixes: Vec<Vec<u8>> = vec![];
    let mut prefix = vec![];
    assert(forall|i: int|
        #![auto]
        0 <= i < prefix.len() ==> prefix@.index(i) == prefix@.subrange(
            0,
            prefix.len() as int,
        ).index(i));

    assert(prefix@ == prefix@.subrange(0, 0));
    assert(forall|i: int|
        #![auto]
        0 <= i < prefix.len() ==> prefix@.index(i) == s@.subrange(0, prefix.len() as int).index(i));
    assert(prefix@ == s@.subrange(0, 0));
    for i in 0..s.len()
        invariant
            prefixes.len() == i,
            prefix.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
            prefix@ == s@.subrange(0, i as int),
            prefix@ == prefix@.subrange(0, i as int),
    {
        let ghost pre_prefix = prefix;
        prefix.push(s[i]);
        assert(pre_prefix@.subrange(0, i as int) == pre_prefix@ && prefix@.subrange(0, i as int)
            == pre_prefix@.subrange(0, i as int));
        assert(prefix@.subrange(0, i as int) == s@.subrange(0, i as int));
        assert(prefix[i as int] == s@.subrange(0, i + 1).index(i as int));

        assert(forall|j: int|
            #![auto]
            0 <= j < i + 1 ==> prefix@.index(j) == prefix@.subrange(0, (i + 1) as int).index(j));
        assert(prefix@ == prefix@.subrange(0, (i + 1) as int));
        assert(forall|j: int|
            #![auto]
            0 <= j < i + 1 ==> prefix@.index(j) == s@.subrange(0, (i + 1) as int).index(j));
        assert(prefix@ == s@.subrange(0, (i + 1) as int));

        prefixes.push(prefix.clone());
    }
    return prefixes;
}

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
