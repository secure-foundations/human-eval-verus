/*
### ID
HumanEval/66
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

// TODO: Put your solution (the specification, implementation, and proof) to the task here

fn toLower(c: char) -> (ret: char)
    // requires
    //     c.is_ascii(),
    ensures 'A' <= c <= 'Z' ==> ret as u32 == add(c as u32, 32u32),
            c < 'A' || c > 'Z' ==> ret == c
{
    if ('A' <= c && c <= 'Z') {
        char::from_u32(c as u32 + 32).unwrap()
    } else {
        c
    }
}

// pub fn upper_sum_rec(s: &str) -> u64 
//     ensures upper_sum_rec(s) >= 0
// {
//     if s.len() == 0 {
//         0
//     } else {
//         let remaining = upper_sum_rec(&s[1..]);
//         to_int(s.chars().next().unwrap()) as u64 + remaining
//     }
// }

// pub proof fn upper_sum_rec_prop(s: &str)
//     requires s.len() > 0,
//     ensures upper_sum_rec(s) == upper_sum_rec(&s[..s.len()-1]) + to_int(s.chars().nth(s.len()-1).unwrap()) as u64
// {
//     if s.len() > 1 {
//         assert(s[1..][..s[1..].len() - 1] == s[1..s.len() - 1]);
//     }
// }

// pub fn to_int(c: char) -> u8
//     ensures 'A' <= c <= 'Z' ==> to_int(c) == c as u8,
//             c < 'A' || c > 'Z' ==> to_int(c) == 0
// {
//     if 'A' <= c && c <= 'Z' { c as u8 } else { 0 }
// }

// pub fn upper_sum(s: &str) -> (res: u64)
//     ensures res == upper_sum_rec(s)
// {
//     let mut res = 0;
//     let mut i = 0;
//     while i < s.len()
//         invariant
//             0 <= i && i <= s.len(),
//             res == upper_sum_rec(&s[..i])
//     {
//         res = res + to_int(s.chars().nth(i).unwrap()) as u64;
//         proof {
//             assert(upper_sum_rec(&s[..i+1]) == upper_sum_rec(&s[..i]) + to_int(s.chars().nth(i).unwrap()) as u64);
//             assert(s[..i+1][..i] == s[..i]);
//             upper_sum_rec_prop(&s[..i+1]);
//         }
//         i = i + 1;
//     }
//     proof {
//         assert(s == &s[..s.len()]);
//     }
//     res
// }
} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def digitSum(s):
    """Task
    Write a function that takes a string as input and returns the sum of the upper characters only'
    ASCII codes.

    Examples:
        digitSum("") => 0
        digitSum("abAB") => 131
        digitSum("abcCd") => 67
        digitSum("helloE") => 69
        digitSum("woArBld") => 131
        digitSum("aAaaaXa") => 153
    """

*/

/*
### ENTRY POINT
digitSum
*/

/*
### CANONICAL SOLUTION
    if s == "": return 0
    return sum(ord(char) if char.isupper() else 0 for char in s)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate("") == 0, "Error"
    assert candidate("abAB") == 131, "Error"
    assert candidate("abcCd") == 67, "Error"
    assert candidate("helloE") == 69, "Error"
    assert candidate("woArBld") == 131, "Error"
    assert candidate("aAaaaXa") == 153, "Error"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate(" How are yOu?") == 151, "Error"
    assert candidate("You arE Very Smart") == 327, "Error"


*/
