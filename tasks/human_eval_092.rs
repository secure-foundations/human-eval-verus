/*
### ID
HumanEval/92
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn any_int_spec(x: int, y: int, z: int) -> bool {
    (x == y + z) || (y == x + z) || (z == x + y)
}

fn any_int(x: i32, y: i32, z: i32) -> (result: bool)
    ensures result <==> any_int_spec(x as int, y as int, z as int),

{
    // explicit range checks allow us to drop range requires statements 
    // on our signature
    let check1 =
        if y > 0 && z > 0 && y > i32::MAX - z {
            false
        }
        else if y < 0 && z < 0 && y < i32::MIN - z {
            false
        }
        else {
            y + z == x
        };

    let check2 =
        if x > 0 && z > 0 && x > i32::MAX - z {
            false
        }
        else if x < 0 && z < 0 && x < i32::MIN - z {
            false
        }
        else {
            x + z == y
        };

    let check3 =
        if x > 0 && y > 0 && x > i32::MAX - y {
            false
        }
        else if x < 0 && y < 0 && x < i32::MIN - y {
            false
        }
        else {
            x + y == z
        };

    check1 || check2 || check3

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def any_int(x, y, z):
    '''
    Create a function that takes 3 numbers.
    Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers.
    Returns false in any other cases.

    Examples
    any_int(5, 2, 7) ➞ True

    any_int(3, 2, 2) ➞ False

    any_int(3, -2, 1) ➞ True

    any_int(3.6, -2.2, 2) ➞ False



    '''

*/

/*
### ENTRY POINT
any_int
*/

/*
### CANONICAL SOLUTION

    if isinstance(x,int) and isinstance(y,int) and isinstance(z,int):
        if (x+y==z) or (x+z==y) or (y+z==x):
            return True
        return False
    return False

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(2, 3, 1)==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate(2.5, 2, 3)==False, "This prints if this assert fails 2 (good for debugging!)"
    assert candidate(1.5, 5, 3.5)==False, "This prints if this assert fails 3 (good for debugging!)"
    assert candidate(2, 6, 2)==False, "This prints if this assert fails 4 (good for debugging!)"
    assert candidate(4, 2, 2)==True, "This prints if this assert fails 5 (good for debugging!)"
    assert candidate(2.2, 2.2, 2.2)==False, "This prints if this assert fails 6 (good for debugging!)"
    assert candidate(-4, 6, 2)==True, "This prints if this assert fails 7 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(2,1,1)==True, "This prints if this assert fails 8 (also good for debugging!)"
    assert candidate(3,4,7)==True, "This prints if this assert fails 9 (also good for debugging!)"
    assert candidate(3.0,4,7)==False, "This prints if this assert fails 10 (also good for debugging!)"


*/
