/*
### ID
HumanEval/80
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn three_distinct_spec(s: Seq<char>, i: int) -> bool
    recommends
        0 < i && i + 1 < s.len(),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}

fn three_distinct(s: &Vec<char>, i: usize) -> (is: bool)
    requires
        0 < i && i + 1 < s.len(),
    ensures
        is <==> three_distinct_spec(s@, i as int),
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i] != s[i + 1])
}

spec fn happy_spec(s: Seq<char>) -> bool {
    s.len() >= 3 && (forall|i: int| 0 < i && i + 1 < s.len() ==> three_distinct_spec(s, i))
}

#[verifier::loop_isolation(false)]
fn is_happy(s: &Vec<char>) -> (happy: bool)
    ensures
        happy <==> happy_spec(s@),
{
    if s.len() < 3 {
        return false;
    }
    for i in 1..(s.len() - 1)
        invariant
            forall|j: int| 0 < j < i ==> three_distinct_spec(s@, j),
    {
        if !three_distinct(s, i) {
            return false;
        }
    }
    return true;
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def is_happy(s):
    """You are given a string s.
    Your task is to check if the string is happy or not.
    A string is happy if its length is at least 3 and every 3 consecutive letters are distinct
    For example:
    is_happy(a) => False
    is_happy(aa) => False
    is_happy(abcd) => True
    is_happy(aabb) => False
    is_happy(adb) => True
    is_happy(xyy) => False
    """

*/

/*
### ENTRY POINT
is_happy
*/

/*
### CANONICAL SOLUTION
    if len(s) < 3:
      return False

    for i in range(len(s) - 2):

      if s[i] == s[i+1] or s[i+1] == s[i+2] or s[i] == s[i+2]:
        return False
    return True

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate("a") == False , "a"
    assert candidate("aa") == False , "aa"
    assert candidate("abcd") == True , "abcd"
    assert candidate("aabb") == False , "aabb"
    assert candidate("adb") == True , "adb"
    assert candidate("xyy") == False , "xyy"
    assert candidate("iopaxpoi") == True , "iopaxpoi"
    assert candidate("iopaxioi") == False , "iopaxioi"

*/
