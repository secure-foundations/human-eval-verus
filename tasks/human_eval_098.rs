/*
### ID
HumanEval/98
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::set::group_set_axioms;

verus! {

broadcast use group_set_axioms;

spec fn spec_is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}

fn is_upper_vowel(c: char) -> (is: bool)
    ensures
        is <==> spec_is_upper_vowel(c),
{
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}

#[verifier::loop_isolation(false)]
fn count_upper(s: &[char]) -> (cnt: usize)
    ensures
        cnt == Set::new(|i: int| 0 <= i < s.len() && i % 2 == 0 && spec_is_upper_vowel(s[i])).len(),
{
    let ghost mut found = set![];
    let mut cnt = 0;
    for i in 0..s.len()
        invariant
            found.len() <= i,
            found.finite(),
            cnt == found.len(),
            found =~= Set::new(|j: int| 0 <= j < i && j % 2 == 0 && spec_is_upper_vowel(s[j])),
    {
        if i % 2 == 0 && is_upper_vowel(s[i]) {
            cnt = cnt + 1;
            proof {
                assert(!(0 <= i < i && i % 2 == 0 && spec_is_upper_vowel(s[i as int]))) by {
                    assert(!(0 <= i < i));
                };
                assert(found.insert(i as int).len() == found.len() + 1) by {
                    assert(!found.contains(i as int));
                }
                found = found.insert(i as int);
            }
        }
    }
    cnt
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def count_upper(s):
    """
    Given a string s, count the number of uppercase vowels in even indices.

    For example:
    count_upper('aBCdEf') returns 1
    count_upper('abcdefg') returns 0
    count_upper('dBBE') returns 0
    """

*/

/*
### ENTRY POINT
count_upper
*/

/*
### CANONICAL SOLUTION
    count = 0
    for i in range(0,len(s),2):
        if s[i] in "AEIOU":
            count += 1
    return count

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate('aBCdEf')  == 1
    assert candidate('abcdefg') == 0
    assert candidate('dBBE') == 0
    assert candidate('B')  == 0
    assert candidate('U')  == 1
    assert candidate('') == 0
    assert candidate('EEEE') == 2

    # Check some edge cases that are easy to work out by hand.
    assert True


*/
