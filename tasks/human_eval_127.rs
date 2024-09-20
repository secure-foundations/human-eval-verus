/*
### ID
HumanEval/127
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn spec_min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

fn min(a: i32, b: i32) -> (m: i32)
    ensures
        m == a || m == b,
        m <= a && m <= b,
        m == spec_min(a as int, b as int),
{
    if a < b {
        a
    } else {
        b
    }
}

spec fn spec_max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

fn max(a: i32, b: i32) -> (m: i32)
    ensures
        m == a || m == b,
        m >= a && m >= b,
        m == spec_max(a as int, b as int),
{
    if a > b {
        a
    } else {
        b
    }
}

spec fn spec_prime_helper(num: int, limit: int) -> bool {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}

spec fn spec_prime(num: int) -> bool {
    num >= 2 && spec_prime_helper(num, num)
}

fn is_prime_2(num: u32) -> (result: bool)
    requires
        num >= 2,
    ensures
        result <==> spec_prime(num as int),
{
    let mut i = 2;
    let mut result = true;
    while i < num
        invariant
            2 <= i <= num,
            result <==> spec_prime_helper(num as int, i as int),
    {
        if num % i == 0 {
            result = false;
        }
        i += 1;
    }
    result
}

fn is_prime(num: i32) -> (is: bool)
    requires
        num >= 0,
    ensures
        is <==> (num >= 2 && spec_prime(num as int)),
{
    num >= 2 && is_prime_2(num as u32)
}

fn intersection(a: (i32, i32), b: (i32, i32)) -> (result: &'static str)
    requires
        a.0 <= a.1 && b.0 <= b.1,
        a.1 - a.0 + 1 <= i32::MAX && b.1 - b.0 + 1 <= i32::MAX,
    ensures
        result == "YES" || result == "NO",
        result == "YES" <==> ((spec_max(a.0 as int, b.0 as int) <= spec_min(a.1 as int, b.1 as int))
            && spec_prime(
            (spec_min(a.1 as int, b.1 as int) - spec_max(a.0 as int, b.0 as int) + 1) as int,
        )),
{
    let sect_start = max(a.0, b.0);
    let sect_end = min(a.1, b.1);

    if sect_start < sect_end && is_prime(sect_end - sect_start + 1) {
        "YES"
    } else {
        "NO"
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def intersection(interval1, interval2):
    """You are given two intervals,
    where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
    The given intervals are closed which means that the interval (start, end)
    includes both start and end.
    For each given interval, it is assumed that its start is less or equal its end.
    Your task is to determine whether the length of intersection of these two
    intervals is a prime number.
    Example, the intersection of the intervals (1, 3), (2, 4) is (2, 3)
    which its length is 1, which not a prime number.
    If the length of the intersection is a prime number, return "YES",
    otherwise, return "NO".
    If the two intervals don't intersect, return "NO".


    [input/output] samples:
    intersection((1, 2), (2, 3)) ==> "NO"
    intersection((-1, 1), (0, 4)) ==> "NO"
    intersection((-3, -1), (-5, 5)) ==> "YES"
    """

*/

/*
### ENTRY POINT
intersection
*/

/*
### CANONICAL SOLUTION
    def is_prime(num):
        if num == 1 or num == 0:
            return False
        if num == 2:
            return True
        for i in range(2, num):
            if num%i == 0:
                return False
        return True

    l = max(interval1[0], interval2[0])
    r = min(interval1[1], interval2[1])
    length = r - l
    if length > 0 and is_prime(length):
        return "YES"
    return "NO"

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate((1, 2), (2, 3)) == "NO"
    assert candidate((-1, 1), (0, 4)) == "NO"
    assert candidate((-3, -1), (-5, 5)) == "YES"
    assert candidate((-2, 2), (-4, 0)) == "YES"

    # Check some edge cases that are easy to work out by hand.
    assert candidate((-11, 2), (-1, -1)) == "NO"
    assert candidate((1, 2), (3, 5)) == "NO"
    assert candidate((1, 2), (1, 2)) == "NO"
    assert candidate((-2, -2), (-3, -2)) == "NO"


*/
