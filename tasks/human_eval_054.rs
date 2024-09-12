/*
### ID
HumanEval/54
*/
/*
### VERUS BEGIN
*/
use std::collections::BTreeSet;
use std::collections::HashSet;
use vstd::prelude::*;

verus! {

// fn str_to_set(s: &str) -> HashSet<char> {
//     s.chars().collect()
// }
fn same_chars(left: &str, right: &str) -> (res: bool)
    ensures
        res <==> left@.to_set() =~= right@.to_set(),
{
    left.chars().collect::<HashSet<_>>().eq(&right.chars().collect::<HashSet<_>>())
}

#[verifier::external_fn_specification]
proof fn lemma_set_eq(left: BTreeSet<i32>, right: BTreeSet<i32>)
    ensures
        left.eq(right) ==> left@ =~= right@,
{
    admit();
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def same_chars(s0: str, s1: str):
    """
    Check if two words have the same characters.
    >>> same_chars('eabcdzzzz', 'dddzzzzzzzddeddabc')
    True
    >>> same_chars('abcd', 'dddddddabc')
    True
    >>> same_chars('dddddddabc', 'abcd')
    True
    >>> same_chars('eabcd', 'dddddddabc')
    False
    >>> same_chars('abcd', 'dddddddabce')
    False
    >>> same_chars('eabcdzzzz', 'dddzzzzzzzddddabc')
    False
    """

*/

/*
### ENTRY POINT
same_chars
*/

/*
### CANONICAL SOLUTION
    return set(s0) == set(s1)

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate('eabcdzzzz', 'dddzzzzzzzddeddabc') == True
    assert candidate('abcd', 'dddddddabc') == True
    assert candidate('dddddddabc', 'abcd') == True
    assert candidate('eabcd', 'dddddddabc') == False
    assert candidate('abcd', 'dddddddabcf') == False
    assert candidate('eabcdzzzz', 'dddzzzzzzzddddabc') == False
    assert candidate('aabb', 'aaccc') == False


*/
