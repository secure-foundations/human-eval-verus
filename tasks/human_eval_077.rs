/*
### ID
HumanEval/77
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::mul::*;
use vstd::math::abs;
use vstd::prelude::*;

verus! {

proof fn lemma_cube_increases_helper(i: int)
    ensures
        i >= 0 ==> (i * i * i) <= (i + 1) * (i + 1) * (i + 1),
{
    broadcast use group_mul_properties;

    if (i > 0) {
        assert((i + 1) * (i + 1) * (i + 1) == i * i * i + 3 * i * i + 3 * i + 1);
        assert(i * i * i + 3 * i * i + 3 * i + 1 > i * i * i);
    }
}

proof fn lemma_cube_increases_params(i: int, j: int)
    ensures
        0 <= i <= j ==> (i * i * i) <= (j * j * j),
    decreases j - i,
{
    // base case
    if (i == j) {
    }
    // inductive case
     else if (i < j) {
        lemma_cube_increases_params(i, j - 1);
        lemma_cube_increases_helper(j - 1);

    }
}

proof fn lemma_cube_increases()
    ensures
        forall|i: int, j: int| 0 <= i <= j ==> #[trigger] (i * i * i) <= #[trigger] (j * j * j),
{
    assert forall|i: int, j: int|
        0 <= i <= j ==> #[trigger] (i * i * i) <= #[trigger] (j * j * j) by {
        lemma_cube_increases_params(i, j);
    }
}

fn checked_cube(x: i32) -> (ret: Option<i32>)
    requires
        x >= 0,
    ensures
        ret.is_some() ==> ret.unwrap() == x * x * x,
        ret.is_none() ==> x * x * x > i32::MAX,
{
    //x == 0 done separately to invoke lemma_mul_increases which requires x > 0
    if x == 0 {
        return Some(0);
    }
    let sqr = x.checked_mul(x);
    if sqr.is_some() {
        let cube = sqr.unwrap().checked_mul(x);
        if cube.is_some() {
            let ans = cube.unwrap();
            assert(ans == x * x * x);
            Some(ans)
        } else {
            assert(x * x * x > i32::MAX);
            None
        }
    } else {
        assert(x > 0);
        assert(x * x > i32::MAX);
        proof {
            lemma_mul_increases(x as int, x * x);
        }
        assert(x * x * x >= x * x);
        None
    }
}

#[verifier::external_fn_specification]
pub fn ex_abs(x: i32) -> (ret: i32)
    requires
        x != i32::MIN,  // avoid overflow: -(i32::MIN) == (i32::MAX) + 1

    ensures
        ret == abs(x as int),
{
    x.abs()
}

fn is_cube(x: i32) -> (ret: bool)
    requires
        x != i32::MIN,  // avoid overflow: -(i32::MIN) == (i32::MAX) + 1

    ensures
        ret <==> exists|i: int| 0 <= i && abs(x as int) == #[trigger] (i * i * i),
{
    let x_abs = x.abs();

    // dealing with cases where the the cube is not greater than the number
    if x_abs == 0 {
        assert(abs(x as int) == 0 * 0 * 0);
        return true;
    } else if (x_abs == 1) {
        assert(abs(x as int) == 1 * 1 * 1);
        return true;
    }
    assert(-1 > x || x > 1);
    let mut i = 2;
    while i < x_abs
        invariant
            forall|j: int| 2 <= j < i ==> abs(x as int) != #[trigger] (j * j * j),
            2 <= i <= abs(x as int) == x_abs,
    {
        let prod = checked_cube(i);
        if prod.is_some() && prod.unwrap() == x.abs() {
            return true;
        }
        i += 1;
    }
    assert(forall|j: int| 2 <= j ==> abs(x as int) != #[trigger] (j * j * j)) by {
        assert(forall|j: int| 2 <= j < i ==> abs(x as int) != #[trigger] (j * j * j));

        assert(forall|j: int| i <= j ==> abs(x as int) < #[trigger] (j * j * j)) by {
            assert(abs(x as int) < #[trigger] (i * i * i)) by {
                broadcast use group_mul_properties;

                assert(i <= i * i <= i * i * i);
            }
            lemma_cube_increases();
            assert(forall|j: int| i <= j ==> (i * i * i) <= #[trigger] (j * j * j));
        }
    }
    false
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def iscube(a):
    '''
    Write a function that takes an integer a and returns True
    if this ingeger is a cube of some integer number.
    Note: you may assume the input is always valid.
    Examples:
    iscube(1) ==> True
    iscube(2) ==> False
    iscube(-1) ==> True
    iscube(64) ==> True
    iscube(0) ==> True
    iscube(180) ==> False
    '''

*/

/*
### ENTRY POINT
iscube
*/

/*
### CANONICAL SOLUTION
    a = abs(a)
    return int(round(a ** (1. / 3))) ** 3 == a

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(1) == True, "First test error: " + str(candidate(1))
    assert candidate(2) == False, "Second test error: " + str(candidate(2))
    assert candidate(-1) == True, "Third test error: " + str(candidate(-1))
    assert candidate(64) == True, "Fourth test error: " + str(candidate(64))
    assert candidate(180) == False, "Fifth test error: " + str(candidate(180))
    assert candidate(1000) == True, "Sixth test error: " + str(candidate(1000))


    # Check some edge cases that are easy to work out by hand.
    assert candidate(0) == True, "1st edge test error: " + str(candidate(0))
    assert candidate(1729) == False, "2nd edge test error: " + str(candidate(1728))


*/
