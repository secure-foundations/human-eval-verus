/*
### ID
HumanEval/7
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn string_eq(s1: &str, s2: &str) -> (result: bool)
    ensures
        result <==> s1@ == s2@,
{
    let s1_len = s1.unicode_len();
    let s2_len = s2.unicode_len();
    if s1_len != s2_len {
        return false;
    }
    for i in 0..s1_len
        invariant
            s1@.subrange(0, i as int) =~= s2@.subrange(0, i as int),
            i <= s1_len == s2_len == s1@.len() == s2@.len(),
    {
        let c = s1.get_char(i);
        if c != s2.get_char(i) {
            return false;
        }
        assert(s1@.subrange(0, i + 1) == s1@.subrange(0, i as int).push(c));
        assert(s1@.subrange(0, i as int).push(c) == s2@.subrange(0, i as int).push(c));
        assert(s2@.subrange(0, i as int).push(c) == s2@.subrange(0, i + 1));
    }
    assert(s1@ == s1@.subrange(0, s1_len as int));
    assert(s2@ == s2@.subrange(0, s2_len as int));
    true
}

spec fn is_subseq_of<A>(s: Seq<A>, sub: Seq<A>) -> bool {
    exists|i: int| 0 <= i <= s.len() - sub.len() && s.subrange(i, #[trigger] (i + sub.len())) == sub
}

fn check_substring(s: &str, sub: &str) -> (result: bool)
    ensures
        result <==> is_subseq_of(s@, sub@),
{
    let s_len = s.unicode_len();
    let sub_len = sub.unicode_len();
    if (s_len < sub_len) {
        return false;
    }
    if sub_len == 0 {
        assert(s@.subrange(0, (0 + sub@.len()) as int) == sub@);
        return true;
    }
    for i in 0..s_len - sub_len + 1
        invariant
            forall|j: int| 0 <= j < i ==> s@.subrange(j, #[trigger] (j + sub@.len())) != sub@,
            i <= s_len - sub_len + 1,
            sub_len == sub@.len() <= s_len == s@.len(),
            sub_len > 0,
    {
        if string_eq(sub, s.substring_char(i, i + sub_len)) {
            assert(0 <= i <= s@.len() - sub@.len());
            assert(s@.subrange(i as int, i + sub@.len()) == sub@);
            return true;
        }
    }
    false
}

fn filter_by_sub<'a>(strings: &Vec<&'a str>, sub: &str) -> (res: Vec<&'a str>)
    ensures
        strings@.filter(|s: &str| is_subseq_of(s@, sub@)) == res@,
{
    let mut res = Vec::new();
    assert(res@ == Seq::<&str>::empty());
    let mut n = 0;
    for n in 0..strings.len()
        invariant
            strings@.subrange(0, n as int).filter(|s: &str| is_subseq_of(s@, sub@)) == res@,
            n <= strings.len(),
    {
        reveal(Seq::filter);
        assert(strings@.subrange(0, n as int + 1).drop_last() == strings@.subrange(0, n as int));
        if check_substring(strings[n], sub) {
            res.push(strings[n]);
        }
    }
    assert(strings@.subrange(0, strings@.len() as int) == strings@);
    res
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def filter_by_substring(strings: List[str], substring: str) -> List[str]:
    """ Filter an input list of strings only for ones that contain given substring
    >>> filter_by_substring([], 'a')
    []
    >>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
    ['abc', 'bacd', 'array']
    """

*/

/*
### ENTRY POINT
filter_by_substring
*/

/*
### CANONICAL SOLUTION
    return [x for x in strings if substring in x]

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
    assert candidate(['xxx', 'asd', 'aaaxxy', 'john doe', 'xxxAAA', 'xxx'], 'xx') == ['xxx', 'aaaxxy', 'xxxAAA', 'xxx']
    assert candidate(['grunt', 'trumpet', 'prune', 'gruesome'], 'run') == ['grunt', 'prune']

*/
