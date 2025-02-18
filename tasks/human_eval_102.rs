/*
### ID
HumanEval/102
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

fn choose_num(x: u32, y: u32) -> (ret: i32)
    requires
        x <= i32::MAX && y <= i32::MAX,
    ensures
        ret != -1 ==> {
            x <= ret <= y && ret % 2 == 0 && (forall|i: int|
                #![trigger i % 2]
                (x <= i <= y && i % 2 == 0) ==> i <= ret)
        },
        (ret == -1) <==> forall|i: int| #![trigger i % 2] x <= i <= y ==> i % 2 == 1,
{
    if x > y || (x == y && y % 2 == 1) {
        return -1;
    }
    (if y % 2 == 0 {
        y
    } else {
        y - 1
    }) as i32
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def choose_num(x, y):
    """This function takes two positive numbers x and y and returns the
    biggest even integer number that is in the range [x, y] inclusive. If
    there's no such number, then the function should return -1.

    For example:
    choose_num(12, 15) = 14
    choose_num(13, 12) = -1
    """

*/

/*
### ENTRY POINT
choose_num
*/

/*
### CANONICAL SOLUTION
    if x > y:
        return -1
    if y % 2 == 0:
        return y
    if x == y:
        return -1
    return y - 1

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(12, 15) == 14
    assert candidate(13, 12) == -1
    assert candidate(33, 12354) == 12354
    assert candidate(5234, 5233) == -1
    assert candidate(6, 29) == 28
    assert candidate(27, 10) == -1

    # Check some edge cases that are easy to work out by hand.
    assert candidate(7, 7) == -1
    assert candidate(546, 546) == 546


*/
