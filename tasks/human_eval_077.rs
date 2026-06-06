/*
### ID
HumanEval/77
*/
/*
### VERUS BEGIN
*/
use vstd::{invariant, prelude::*};

verus! {

spec fn cube(x: nat) -> nat {
    x * x * x
}

proof fn lemma_2642245_cubed_can_be_represented_in_u64()
    ensures
        cube(2642245) < u64::MAX,
        cube(2642246) > u64::MAX,
{
    assert(cube(2642245) < u64::MAX) by (compute_only);
}

proof fn lemma_cube_is_monotomic(x1: nat, x2: nat)
    requires
        x1 <= x2,
    ensures
        cube(x1) <= cube(x2),
{
    assert(cube(x1) <= cube(x2)) by (nonlinear_arith)
        requires
            0 <= x1 <= x2,
    {};
}

proof fn lemma_i_cube_not_overlows(i: u64)
    requires
        i <= 2642245,
    ensures
        i * i <= u64::MAX,
        i * i * i <= u64::MAX,
{
    assert((i * i * i) < u64::MAX) by {
        assert(i <= 2642245);
        assert(cube(2642245) < u64::MAX) by {
            lemma_2642245_cubed_can_be_represented_in_u64();
        }
        lemma_cube_is_monotomic(i as nat, 2642245);
    };
    assert((i * i) < u64::MAX) by (nonlinear_arith)
        requires
            0 <= i,
            i * i * i < u64::MAX,
    {};
}

proof fn lemma_no_cube_after_2642245(i: u64, n: u64)
    requires
        i >= 2642245,
    ensures
        forall|x: u64| x > i ==> cube(x as nat) > n,
{
    assert(forall|x: u64| x > i ==> cube(x as nat) > n) by {
        assert forall|p: u64| #![auto] i < p implies cube(p as nat) > n by {
            n <= u64::MAX;
            lemma_cube_is_monotomic(2642246, p as nat);
            lemma_2642245_cubed_can_be_represented_in_u64();
            assert(cube(2642246) >= u64::MAX);
            assert(cube(p as nat) > n);

        };
    };
}

proof fn lemma_no_cube_exists_after_an_i_that_is_already_bigger(i: u64, n: u64)
    requires
        cube(i as nat) > n,
    ensures
        forall|x: u64| x >= i ==> cube(x as nat) > n,
{
    assert(forall|x: u64| x >= i ==> cube(x as nat) > n) by {
        assert forall|p: u64| #![auto] i <= p implies cube(p as nat) > n by {
            n <= u64::MAX;
            lemma_cube_is_monotomic(i as nat, p as nat);
        };
    };
}

proof fn lemma_no_cube_exists_before_an_i_that_is_already_smaller(i: u64, n: u64)
    requires
        cube(i as nat) < n,
    ensures
        forall|x: u64| x <= i ==> cube(x as nat) < n,
{
    assert(forall|x: u64| x <= i ==> cube(x as nat) < n) by {
        assert forall|p: u64| #![auto] i >= p implies cube(p as nat) < n by {
            n <= u64::MAX;
            lemma_cube_is_monotomic(p as nat, i as nat);
        };
    };
}

fn iscube(n: u64) -> (out: bool)
    requires
        n < u64::MAX,
    ensures
        out == exists|x: u64| (cube(x as nat) == n as nat),
{
    let mut left = 0;
    let mut right = 2642245;

    proof {
        assert(forall|x: u64| x > right ==> cube(x as nat) > n) by {
            lemma_no_cube_after_2642245(right, n);
        }
    }

    while (left <= right)
        invariant
            0 <= left <= right <= 2642245,
            forall|x: u64| x < left ==> cube(x as nat) < n,
            forall|x: u64| x > right ==> cube(x as nat) > n,
        decreases right - left,
    {
        let i = (right + left) / 2;
        proof {
            lemma_i_cube_not_overlows(i);
        }
        ;
        assert(i * i * i == cube(i as nat));
        let v: u64 = i * i * i;
        if (v == n) {
            assert(exists|x: u64| (cube(x as nat) == n as nat));
            return true;
        } else if (left == right) {
            proof {
                assert(forall|x: u64| x < left ==> cube(x as nat) != n as nat);
                assert(forall|x: u64| x > right ==> cube(x as nat) != n as nat);
                assert(cube(left as nat) != n as nat);
            }
            return false;
        } else if (v > n) {
            proof {
                lemma_no_cube_exists_after_an_i_that_is_already_bigger(i, n);
            }
            right = i;
        } else if (v < n) {
            proof {
                lemma_no_cube_exists_before_an_i_that_is_already_smaller(i, n);
            }
            left = i + 1;
        }
    }

    return false;
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
