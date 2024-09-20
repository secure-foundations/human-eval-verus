/*
### ID
HumanEval/161
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn isalpha_spec(c: int) -> bool {
    65 <= c <= 90 || 97 <= c <= 122
}

fn isalpha(c: u8) -> (is: bool)
    ensures
        is <==> isalpha_spec(c as int),
{
    (65 <= c && c <= 90) || (97 <= c && c <= 122)
}

spec fn flip_case_spec(c: int) -> int
    recommends
        isalpha_spec(c),
{
    if 97 <= c <= 122 {
        c - 97 + 65
    } else {
        c - 65 + 97
    }
}

fn flip_case(c: u8) -> (flipped: u8)
    requires
        isalpha_spec(c as int),
    ensures
        isalpha_spec(flipped as int),
        flipped == flip_case_spec(c as int),
{
    if 97 <= c && c <= 122 {
        c - 97 + 65
    } else {
        c - 65 + 97
    }
}

fn reverse(s: Vec<u8>) -> (rev: Vec<u8>)
    ensures
        s.len() == rev.len(),
        forall|i: int| 0 <= i < s.len() ==> rev[i] == s[s.len() - 1 - i],
{
    let mut rev = vec![];
    for i in 0..s.len()
        invariant
            rev.len() == i,
            forall|k: int| 0 <= k < i ==> rev[k] == s[s.len() - 1 - k],
    {
        rev.push(s[s.len() - i - 1]);
    }
    rev
}

fn solve(s: &Vec<u8>) -> (t: Vec<u8>)
    ensures
        s.len() == t.len(),
        (forall|i: int| #![auto] 0 <= i < s.len() ==> !isalpha_spec(s[i] as int)) ==> (forall|
            i: int,
        |
            0 <= i < t.len() ==> t[i] == s[s.len() - 1 - i]),
        (exists|i: int| #![auto] 0 <= i < s.len() && isalpha_spec(s[i] as int)) ==> (forall|i: int|
            #![auto]
            0 <= i < t.len() ==> t[i] == (if isalpha_spec(s[i] as int) {
                flip_case_spec(s[i] as int)
            } else {
                s[i] as int
            })),
{
    let mut flag = false;
    let mut t = vec![];
    for i in 0..s.len()
        invariant
            t.len() == i,
            flag <==> exists|j: int| #![auto] 0 <= j < i && isalpha_spec(s[j] as int),
            forall|j: int|
                #![auto]
                0 <= j < i ==> (t[j] == if isalpha_spec(s[j] as int) {
                    flip_case_spec(s[j] as int)
                } else {
                    s[j] as int
                }),
    {
        if isalpha(s[i]) {
            t.push(flip_case(s[i]));
            flag = true;
        } else {
            t.push(s[i]);
        }
    }
    if !flag {
        t = reverse(t);
    }
    t
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def solve(s):
    """You are given a string s.
    if s[i] is a letter, reverse its case from lower to upper or vise versa,
    otherwise keep it as it is.
    If the string contains no letters, reverse the string.
    The function should return the resulted string.
    Examples
    solve("1234") = "4321"
    solve("ab") = "AB"
    solve("#a@C") = "#A@c"
    """

*/

/*
### ENTRY POINT
solve
*/

/*
### CANONICAL SOLUTION
    flg = 0
    idx = 0
    new_str = list(s)
    for i in s:
        if i.isalpha():
            new_str[idx] = i.swapcase()
            flg = 1
        idx += 1
    s = ""
    for i in new_str:
        s += i
    if flg == 0:
        return s[len(s)::-1]
    return s

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate("AsDf") == "aSdF"
    assert candidate("1234") == "4321"
    assert candidate("ab") == "AB"
    assert candidate("#a@C") == "#A@c"
    assert candidate("#AsdfW^45") == "#aSDFw^45"
    assert candidate("#6@2") == "2@6#"

    # Check some edge cases that are easy to work out by hand.
    assert candidate("#$a^D") == "#$A^d"
    assert candidate("#ccc") == "#CCC"

    # Don't remove this line:

*/
