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

// TODO: Put your solution (the specification, implementation, and proof) to the task here
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

proof fn lemma_i_bigger_2642245_no_cube(i: u64, n: u64)
    requires
        i >= 2642245,
        forall|x: u64| x <= i ==> cube(x as nat) != n,
    ensures
        !(exists|x: u64| (cube(x as nat) == n as nat)),
{
    assert(!(exists|x: u64| (cube(x as nat) == n as nat))) by {
        assert(forall|x: u64| x <= i ==> cube(x as nat) != n);
        assert forall|p: u64| #![auto] i < p implies cube(p as nat) != n by {
            n <= u64::MAX;
            lemma_cube_is_monotomic(2642246, p as nat);
            lemma_2642245_cubed_can_be_represented_in_u64();
            assert(cube(2642246) >= u64::MAX);
            assert(cube(p as nat) > n);

        };
    };
}

proof fn lemma_not_exist_any_cube_bigger_than_i(i: u64, n: u64)
    requires
        cube(i as nat) > n,
        forall|x: u64| x <= i ==> cube(x as nat) != n,
    ensures
        !(exists|x: u64| (cube(x as nat) == n as nat)),
{
    assert(!(exists|x: u64| (cube(x as nat) == n as nat))) by {
        assert(forall|x: u64| x <= i ==> cube(x as nat) != n);
        assert forall|p: u64| #![auto] i < p implies cube(p as nat) != n by {
            n <= u64::MAX;
            lemma_cube_is_monotomic(i as nat, p as nat);
        };
    };
}

fn iscube(n: u64) -> (out: bool)
    requires
        n < u64::MAX,
    ensures
        out == exists|x: u64| (cube(x as nat) == n as nat),
{
    if (n == 0) {
        assert(cube(0 as nat) == n as nat);
        return true;
    }
    if (n == 1) {
        assert(cube(1 as nat) == n as nat);
        return true;
    }
    for i in 0..(n + 1)
        invariant
            i <= 2642245,
            forall|x: u64| x < i ==> cube(x as nat) != n,
    {
        proof {
            lemma_i_cube_not_overlows(i);
        }
        ;
        assert(i * i * i == cube(i as nat));

        let v: u64 = i * i * i;
        if (v == n) {
            assert(exists|x: u64| (cube(x as nat) == n as nat));
            return true;
        }
        if (v > n) {
            assert(!exists|x: u64| (cube(x as nat) == n as nat)) by {
                lemma_not_exist_any_cube_bigger_than_i(i, n);
            };
            return false;
        }
        if (i >= 2642245) {
            assert(!(exists|x: u64| (cube(x as nat) == n as nat))) by {
                lemma_i_bigger_2642245_no_cube(i, n);
            }
            return false;
        }
    }

    // This is infact unreachable
    assert(!(exists|x: u64| (cube(x as nat) == n as nat))) by {
        if (n > 2642245) {
            assert(forall|x: u64| x < 2642245 ==> cube(x as nat) != n);
            lemma_i_bigger_2642245_no_cube(2642245, n);
        } else {
            assert(forall|x: u64| x <= n ==> cube(x as nat) != n);
            let nnat = n as nat;
            assert(cube(nnat) > nnat) by (nonlinear_arith)
                requires
                    nnat >= 2,
            {}
            lemma_not_exist_any_cube_bigger_than_i(n, n);
            assert(!(exists|x: u64| (cube(x as nat) == n as nat)));
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
