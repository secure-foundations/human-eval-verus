/*
### ID
HumanEval/13
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

// TODO: Put your solution (the specification, implementation, and proof) to the task here
verus! {

// This function is part of the specification
pub open spec fn mul(a: nat, b: nat) -> nat {
    builtin::mul(a, b)
}

// This function is also part of the specification
pub open spec fn divides(factor: nat, candidate: nat) -> bool {
    exists|k: nat| #[trigger] mul(factor, k) == candidate
}

// This function is also part of the specification
spec fn gcd(a: nat, b: nat) -> nat
    decreases a, b,
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a > b {
        gcd(b, a % b)
    } else {
        gcd(a, b % a)
    }
}

fn compute_gcd(a: u64, b: u64) -> (g: u64)
    ensures
        g == gcd(a as nat, b as nat),
{
    let mut a1 = a;
    let mut b1 = b;
    loop
        invariant
            gcd(a1 as nat, b1 as nat) == gcd(a as nat, b as nat),
    {
        if a1 == 0 {
            return b1;
        } else if b1 == 0 {
            return a1;
        } else if a1 > b1 {
            let m = a1 % b1;
            a1 = b1;
            b1 = m;
        } else {
            b1 = b1 % a1;
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_div(a: nat, b: nat, d: nat)
    requires
        divides(d, a) && divides(d, b) && a >= b && a != 0 && b != 0,
    ensures
        divides(d, a % b),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
    assert(a % b == a - b * (a / b));
    assert(divides(d, a));
    assert(divides(d, b * (a / b))) by {
        let k = choose|k: nat| mul(d, k) == b;
        let k1 = k * (a / b);
        broadcast use vstd::arithmetic::mul::group_mul_properties;

        assert(mul(d, k1) == b * (a / b));
    };
    assert(divides(d, a % b)) by {
        let k1 = choose|k: nat| mul(d, k) == a;
        let k2 = choose|k: nat| mul(d, k) == b * (a / b);
        assert(a >= b * (a / b));
        assert(k1 >= k2) by {
            // note: is there a better way to proof by contradiction?
            if (k1 < k2) {
                // note: using broadcast fails here
                vstd::arithmetic::mul::lemma_mul_strict_inequality(k1 as int, k2 as int, d as int);
            }
        }
        let k = k1 - k2;
        assert(mul(d, k as nat) == mul(d, k1) - mul(d, k2)) by {
            // note: using broadcast fails here
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(d as int, k1 as int, k2 as int);
        };
    };
}

#[verifier::spinoff_prover]
proof fn lemma_div_converse(a: nat, b: nat, d: nat)
    requires
        divides(d, b) && divides(d, a % b) && a >= b && a != 0 && b != 0,
    ensures
        divides(d, a),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, b as int);
    // assert(a % b == a - b * (a / b));
    assert(divides(d, b));
    assert(divides(d, b * (a / b))) by {
        let k = choose|k: nat| mul(d, k) == b;
        let k1 = k * (a / b);
        broadcast use vstd::arithmetic::mul::group_mul_properties;

        assert(mul(d, k1) == b * (a / b));
    };
    assert(divides(d, a)) by {
        let k1 = choose|k: nat| mul(d, k) == a % b;
        let k2 = choose|k: nat| mul(d, k) == b * (a / b);
        let k = k1 + k2;
        assert(mul(d, k) == mul(d, k1) + mul(d, k2)) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(d as int, k1 as int, k2 as int);
        };
    }
}

// Helper function to prove gcd is a divisor of a and b
proof fn gcd_divides(a: nat, b: nat)
    ensures
        divides(gcd(a, b), a),
        divides(gcd(a, b), b),
    decreases a, b,
{
    if a == 0 {
        assert(gcd(a, b) == b);
        assert(divides(b, a)) by {
            assert(mul(b, 0) == 0);
        };
        assert(divides(b, b)) by {
            assert(mul(b, 1) == b);
        };
    } else if b == 0 {
        assert(divides(a, a)) by {
            assert(mul(a, 1) == a);
        };
        assert(divides(a, b)) by {
            assert(mul(a, 0) == 0);
        };
    } else if a > b {
        let m = a % b;
        gcd_divides(b, m);
        assert(divides(gcd(a, b), a)) by {
            lemma_div_converse(a, b, gcd(b, m));
        };
    } else {
        let m = b % a;
        gcd_divides(a, m);
        assert(divides(gcd(a, b), b)) by {
            lemma_div_converse(b, a, gcd(a, m));
        }

    }
}

// Helper function to prove if d divides a and d divides b, then d divides gcd(a, b)
proof fn all_common_divisors_divides_gcd(a: nat, b: nat)
    ensures
        forall|d: nat| divides(d, a) && divides(d, b) ==> #[trigger] divides(d, gcd(a, b)),
    decreases a, b,
{
    assert forall|d: nat| divides(d, a) && divides(d, b) implies #[trigger] divides(
        d,
        gcd(a, b),
    ) by {
        if a == 0 {
            assert(divides(d, gcd(a, b)));
        } else if b == 0 {
            assert(divides(d, gcd(a, b)));
        } else if a > b {
            let m = a % b;
            all_common_divisors_divides_gcd(b, m);
            assert(divides(d, m)) by {
                lemma_div(a, b, d);
            };
            assert(gcd(a, b) == gcd(b, m));
            assert(divides(d, gcd(a, b)));
        } else {
            let m = b % a;
            all_common_divisors_divides_gcd(a, m);
            assert(divides(d, m)) by {
                lemma_div(b, a, d);
            };
            assert(gcd(a, b) == gcd(a, m));
            assert(divides(d, gcd(a, b)));
        }
    }
}

// We prove the recursive definition of computing gcd actually satisfies the
// number theoretic properties og gcd, namely it's a common divisor of a and b
// and it is the greatest positive common divisor in the preorder relation of divisibility
proof fn gcd_is_gcd(a: nat, b: nat)
    ensures
        divides(gcd(a, b), a),
        divides(gcd(a, b), b),
        forall|d: nat| divides(d, a) && divides(d, b) ==> #[trigger] divides(d, gcd(a, b)),
{
    gcd_divides(a, b);
    all_common_divisors_divides_gcd(a, b);
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT


def greatest_common_divisor(a: int, b: int) -> int:
    """ Return a greatest common divisor of two integers a and b
    >>> greatest_common_divisor(3, 5)
    1
    >>> greatest_common_divisor(25, 15)
    5
    """

*/

/*
### ENTRY POINT
greatest_common_divisor
*/

/*
### CANONICAL SOLUTION
    while b:
        a, b = b, a % b
    return a

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3, 7) == 1
    assert candidate(10, 15) == 5
    assert candidate(49, 14) == 7
    assert candidate(144, 60) == 12

*/
