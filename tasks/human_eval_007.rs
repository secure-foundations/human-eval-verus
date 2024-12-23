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
//        exists|i: int|
//            0 <= i <= s@.len() - sub@.len() && s@.subrange(i, #[trigger] (i + sub@.len())) == sub@,

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
        strings@.filter(|s: &str| is_subseq_of(s@, sub@))
            == res@,
// forall|i: int|
//     0 <= i < strings@.len() &&
//     // strings@.filter (|s: &str| is_subseq_of(s@, sub@)) == res@
//     is_subseq_of(strings[i]@, sub@) ==> res@.contains(
//         #[trigger] (strings[i]),
//     ) && res@.contains(#[trigger] (strings[i])) ==> is_subseq_of(strings[i]@, sub@),

{
    let mut res = Vec::new();
    // assert (strings@.subrange(0, 0).filter (|s: &str| is_subseq_of(s@, sub@)) == res@);
    assert(res@ == Seq::<&str>::empty());
    let mut n = 0;
    // while n < strings.len()
    for n in 0..strings.len()
        invariant
    // n < strings.len(),
    // forall|i: int|
    //     0 <= i < n && is_subseq_of(strings[i]@, sub@) ==> res@.contains(
    //         #[trigger] (strings[i]),
    //     ),

            strings@.subrange(0, n as int).filter(|s: &str| is_subseq_of(s@, sub@)) == res@,
            n <= strings.len(),
    {
        reveal(Seq::filter);
        assert(strings@.subrange(0, n as int + 1).drop_last() == strings@.subrange(0, n as int));
        if check_substring(strings[n], sub) {
            // let ghost res_old = res@;
            // let ghost filtered_sub = strings@.subrange(0, n as int).filter (|s: &str| is_subseq_of(s@, sub@));
            // let ghost pred = |s: &str| is_subseq_of(s@, sub@);
            // let ghost last = ran.last();
            // assert (last@ == strings[n as int]@);
            // let ghost ra = ran.drop_last();
            // assert(ra.push(last) == ran);
            // assert (ra == strings@.subrange(0, n as int));
            // assert (pred(last));
            // let ghost ran_f = ran.filter(pred);
            // let ghost ra_f = ra.filter(pred);
            // assert(ra_f == res@);
            // assert(ra_f.push(last) == ran_f);
            // assert (ran.filter (|s: &str| is_subseq_of(s@, sub@)).last()@ == ran.last()@);
            res.push(strings[n]);
            // assert (ran_f == res@);
            // assert(res@.last() == strings[n as int]);
            // assert (strings[n as int] == strings@.subrange(0, n as int + 1).last());
            // assert (res_old == filtered_sub);
            // assert (strings[n as int] == strings@.subrange(0, n as int + 1).filter (|s: &str| is_subseq_of(s@, sub@)).last());
            // assert (strings@.subrange(0, (n as int) + 1).filter (|s: &str| is_subseq_of(s@, sub@)) == strings@.subrange(0, n as int).filter (|s: &str| is_subseq_of(s@, sub@)).push(strings[n as int]));
            // assert(strings[n as int]@ == strings@.subrange(0, n + 1).filter(|s: &str| is_subseq_of(s@, sub@)).last()@);
            // assert(res@.drop_last() == res_old);
        }
    }
    assert(strings@.subrange(0, strings@.len() as int) == strings@);
    // assert (strings@.subrange(0, n as int).filter (|s: &str| is_subseq_of(s@, sub@)) == res@);
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
