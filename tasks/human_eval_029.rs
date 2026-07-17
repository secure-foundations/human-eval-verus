/*
### ID
HumanEval/29
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn to_seq(s: Vec<Vec<char>>) -> Seq<Seq<char>> {
    s@.map_values(|v: Vec<char>| v@)
}

fn filter_by_prefix(strings: Vec<Vec<char>>, prefix: Vec<char>) -> (res: Vec<Vec<char>>)
    ensures
        to_seq(res) == to_seq(strings).filter(|s: Seq<char>| prefix@.is_prefix_of(s)),
{
    let mut result = Vec::new();
    for i in 0..strings.len()
        invariant
            to_seq(result) == to_seq(strings).subrange(0, i as int).filter(
                |s: Seq<char>| prefix@.is_prefix_of(s),
            ),
    {
        assert(to_seq(strings).subrange(0, i + 1) == to_seq(strings).subrange(0, i as int).push(
            strings[i as int]@,
        ));
        proof {
            to_seq(strings).subrange(0, i as int).lemma_filter_push(
                strings[i as int]@,
                |s: Seq<char>| prefix@.is_prefix_of(s),
            );
        }
        if strings[i].len() >= prefix.len() {
            let mut flag = true;
            assert(strings[i as int]@.subrange(0, 0) == prefix@.subrange(0, 0));
            for j in 0..prefix.len()
                invariant
                    prefix@.is_prefix_of(strings[i as int]@) ==> to_seq(strings).subrange(
                        0,
                        i + 1,
                    ).filter(|s: Seq<char>| prefix@.is_prefix_of(s)) == to_seq(strings).subrange(
                        0,
                        i as int,
                    ).filter(|s: Seq<char>| prefix@.is_prefix_of(s)).push(strings[i as int]@),
                    !prefix@.is_prefix_of(strings[i as int]@) ==> to_seq(strings).subrange(
                        0,
                        i + 1,
                    ).filter(|s: Seq<char>| prefix@.is_prefix_of(s)) == to_seq(strings).subrange(
                        0,
                        i as int,
                    ).filter(|s: Seq<char>| prefix@.is_prefix_of(s)),
                    0 <= i < strings.len(),
                    strings[i as int].len() >= prefix.len(),
                    flag == (strings[i as int]@.subrange(0, j as int) == prefix@.subrange(
                        0,
                        j as int,
                    )),
            {
                if strings[i][j] != prefix[j] {
                    flag = false;
                    assert(strings[i as int]@.subrange(0, j + 1)[j as int] != prefix@.subrange(
                        0,
                        j + 1,
                    )[j as int]);
                } else {
                    if (flag) {
                        assert(strings[i as int]@.subrange(0, j + 1) == prefix@.subrange(0, j + 1));
                    } else {
                        assert(strings[i as int]@.subrange(0, j as int)
                            == strings[i as int]@.subrange(0, j + 1).subrange(0, j as int));
                        assert(prefix@.subrange(0, j as int) == prefix@.subrange(0, j + 1).subrange(
                            0,
                            j as int,
                        ));
                    }
                }
            }
            assert(prefix@.subrange(0, prefix.len() as int) == prefix@);
            if flag {
                result.push(strings[i].clone());
            }
        }
    }
    assert(to_seq(strings).subrange(0, strings.len() as int) == to_seq(strings));
    result
}

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
