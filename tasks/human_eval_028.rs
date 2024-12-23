/*
### ID
HumanEval/28
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

pub closed spec fn concat_helper(strings: Seq<Seq<char>>, i: nat) -> Seq<char>
    recommends
        i <= strings.len(),
    decreases strings.len() - i,
{
    if (i >= strings.len()) {
        seq![]
    } else {
        strings[i as int] + concat_helper(strings, i + 1)
    }
}

pub open spec fn concatenate(strings: Seq<Seq<char>>) -> Seq<char> {
    concat_helper(strings, 0)
}

proof fn sanity_check() {
    assert(concatenate(seq![seq!['a'], seq!['b'], seq!['c']]) == seq!['a', 'b', 'c']) by (compute);
    assert(concatenate(Seq::empty()) == Seq::<char>::empty());
    assert(concatenate(seq![seq!['a', 'z'], seq!['b'], seq!['c', 'y']]) == seq![
        'a',
        'z',
        'b',
        'c',
        'y',
    ]) by (compute);
}

fn concatenate_impl(strings: Vec<Vec<char>>) -> (joined: Vec<char>)
    ensures
        joined@ == concatenate(strings.deep_view()),
{
    let mut i = 0;
    let mut joined = vec![];

    while (i < strings.len())
        invariant
            0 <= i <= strings.len(),
            concatenate(strings.deep_view()) == joined@ + concat_helper(
                strings.deep_view(),
                i as nat,
            ),
    {
        assert(concatenate(strings.deep_view()) == joined@ + strings[i as int]@ + concat_helper(
            strings.deep_view(),
            (i + 1) as nat,
        ));

        let mut copy_str = strings[i].clone();
        joined.append(&mut copy_str);
        i = i + 1;
    }
    return joined;
}

} // verus!
fn main() {
    let test1 = vec![vec!['a'], vec!['b'], vec!['c']];
    let test2: Vec<Vec<char>> = Vec::new();
    let test3 = vec![vec!['a', 'z'], vec!['b'], vec!['c', 'y']];

    print!("concatenation of {:?}:\n", test1);
    print!("{:?}\n", concatenate_impl(test1));
    print!("concatenation of {:?}:\n", test2);
    print!("{:?}\n", concatenate_impl(test2));
    print!("concatenation of {:?}:\n", test3);
    print!("{:?}\n", concatenate_impl(test3));
}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def concatenate(strings: List[str]) -> str:
    """ Concatenate list of strings into a single string
    >>> concatenate([])
    ''
    >>> concatenate(['a', 'b', 'c'])
    'abc'
    """

*/

/*
### ENTRY POINT
concatenate
*/

/*
### CANONICAL SOLUTION
    return ''.join(strings)

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == ''
    assert candidate(['x', 'y', 'z']) == 'xyz'
    assert candidate(['x', 'y', 'z', 'w', 'k']) == 'xyzwk'

*/
