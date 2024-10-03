/*
### ID
HumanEval/25
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::prelude::*;

verus! {

pub closed spec fn is_prime(n: nat) -> bool {
    forall|i: nat| 1 < i < n ==> #[trigger] (n % i) != 0
}

// canonical definition of prime factoriztion
pub closed spec fn is_prime_factorization(n: nat, factorization: Seq<nat>) -> bool {
    // all factors are prime
    &&& forall|i: int|
        0 <= i < factorization.len() ==> #[trigger] is_prime(
            factorization[i] as nat,
        )
    // product of factors is n
    &&& factorization.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat)
        == n
    // factors are listed in ascending order
    &&& forall|i: nat, j: nat|
        (1 < i <= j < factorization.len()) ==> (#[trigger] factorization[i as int]
            <= #[trigger] factorization[j as int])
}

// these two pull out lemmas are the same except for types
// would prefer to have one polymorphic function, but won't go through
// See https://github.com/verus-lang/verus/issues/1287
proof fn lemma_fold_right_pull_out_nat(seq: Seq<nat>, k: nat)
    ensures
        seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == (seq.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1,
        ) * k) as nat,
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        calc! {
            (==)
            seq.fold_right(|x, acc: nat| (acc * x) as nat, k); {
                lemma_fold_right_pull_out_nat(seq.drop_last(), (k * seq.last()) as nat)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (k
                * seq.last()) as nat) as nat; {
                lemma_mul_is_commutative(k as int, seq.last() as int)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (seq.last()
                * k) as nat) as nat; {
                lemma_mul_is_associative(
                    seq.drop_last().fold_right(|x: nat, acc: nat| (acc * x) as nat, 1nat) as int,
                    seq.last() as int,
                    k as int,
                );
            }  // {lemma_mul_is_associative(seq.drop_last().fold_right(|x, acc : nat| (acc * x) as nat, 1) as int, seq.last() as int, k as int)}
            (((seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * seq.last()) as nat)
                * k) as nat; { lemma_fold_right_pull_out_nat(seq.drop_last(), seq.last() as nat) }
            (seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) * k) as nat;
        }
    }
}

proof fn lemma_fold_right_pull_out_hybrid(seq: Seq<u8>, k: nat)
    ensures
        seq.fold_right(|x, acc: nat| (acc * x) as nat, k) == (seq.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1,
        ) * k) as nat,
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        calc! {
            (==)
            seq.fold_right(|x, acc: nat| (acc * x) as nat, k); {
                lemma_fold_right_pull_out_hybrid(seq.drop_last(), (k * seq.last()) as nat)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (k
                * seq.last()) as nat) as nat; {
                lemma_mul_is_commutative(k as int, seq.last() as int)
            }
            (seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * (seq.last()
                * k) as nat) as nat; {
                lemma_mul_is_associative(
                    seq.drop_last().fold_right(|x: u8, acc: nat| (acc * x) as nat, 1nat) as int,
                    seq.last() as int,
                    k as int,
                );
            }
            (((seq.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1) * seq.last()) as nat)
                * k) as nat; { lemma_fold_right_pull_out_hybrid(seq.drop_last(), seq.last() as nat)
            }
            (seq.fold_right(|x, acc: nat| (acc * x) as nat, 1) * k) as nat;
        }
    }
}

proof fn lemma_unfold_right_fold(factors: Seq<u8>, old_factors: Seq<u8>, k: u8, m: u8)
    requires
        old_factors.push(m) == factors,
        k % m == 0,
        m != 0,
    ensures
        factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k / m) as nat))
            == old_factors.fold_right(|x, acc: nat| (acc * x) as nat, ((k as nat))),
{
    assert((old_factors.push(m)).drop_last() == old_factors);
    assert(((k as int) / (m as int)) * (m as int) + (k as int) % (m as int) == (k as int)) by {
        lemma_fundamental_div_mod(k as int, m as int)
    };
}

proof fn lemma_unfold_right_fold_new(factors: Seq<u8>, old_factors: Seq<u8>, m: u8)
    requires
        old_factors.push(m as u8) == factors,
        m != 0,
    ensures
        factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == old_factors.fold_right(
            |x, acc: nat| (acc * x) as nat,
            1nat,
        ) * (m as nat),
{
    assert((old_factors.push(m as u8)).drop_last() == old_factors);
    assert(factors.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == old_factors.fold_right(
        |x, acc: nat| (acc * x) as nat,
        1,
    ) * (m as nat)) by { lemma_fold_right_pull_out_hybrid(old_factors, m as nat) }
}

proof fn lemma_multiple_mod_is_zero(m: int, n: int, k: int)
    requires
        n % k == 0,
        k % m == 0,
        k > 0,
        m > 0,
    ensures
        n % (k / m) == 0,
{
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k, m) };
    assert(n == (n / k) * k) by { lemma_fundamental_div_mod(n, k) };

    assert(n == ((n / k) * m) * (k / m)) by {
        broadcast use group_mul_properties;

    };
    assert(n % (k / m) == 0) by { lemma_mod_multiples_basic((n / k) * m, k / m) };
}

proof fn lemma_multiple_mod_is_zero_new(m: int, n: int, k: int)
    requires
        n % k == 0,
        k % m == 0,
        k > 0,
        m > 0,
        n > 0,
    ensures
        m * (n / k) == n / (k / m),
{
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k, m) };
    let a = choose|a: int| (#[trigger] (a * m) == k && (a == k / m));

    assert(n == (n / k) * k) by { lemma_fundamental_div_mod(n, k) };
    let b = choose|b: int| (#[trigger] (b * k) == n && b == n / k);

    assert((a * m) * b == n) by { lemma_mul_is_commutative(b, a * m) }
    assert(a * (m * b) == n) by { lemma_mul_is_associative(a, m, b) };
    assert((m * b) == n / a) by { lemma_div_multiples_vanish(m * b, a) };
}

proof fn lemma_factor_mod_is_zero(k: int, m: int, j: int)
    requires
        k % j != 0,
        k % m == 0,
        1 <= j < m,
    ensures
        (k / m) % j != 0,
{
    assert_by_contradiction!((k/m) % j != 0,
            { /* proof */
                assert (k == (k/m) * m) by {lemma_fundamental_div_mod(k, m)};
                let a = choose|a:int| (#[trigger] (a * m) == k);

                assert ((k/m) == ((k/m)/j) * j) by {lemma_fundamental_div_mod(k/m, j)};
                let b = choose|b:int| (#[trigger] (b * j) == k/m);

                calc! {
                    (==)
                    k % j; {broadcast use group_mul_properties;}
                    ((b * m) * j) % j; {broadcast use lemma_mod_multiples_basic;}
                    0;
                }
            });

}

proof fn lemma_mod_zero_twice(k: int, m: int, i: int)
    requires
        k % m == 0,
        m % i == 0,
        m > 0,
        i > 0,
    ensures
        k % i == 0,
{
    assert(k == (k / m) * m) by { lemma_fundamental_div_mod(k as int, m as int) };
    let a = choose|a: int| (#[trigger] (a * m) == k);

    assert(m == (m / i) * i) by { lemma_fundamental_div_mod(m as int, i as int) };
    let b = choose|b: int| (#[trigger] (b * i) == m);

    assert(k == (a * b) * i) by { lemma_mul_is_associative(a, b, i) };
    assert(k % i == 0) by { lemma_mod_multiples_vanish(a * b, 0, i) };

}

proof fn lemma_first_divisor_is_prime(k: nat, m: nat)
    requires
        k % m == 0,
        forall|j: nat| 1 < j < m ==> #[trigger] (k % j) != 0,
        m >= 2,
    ensures
        is_prime(m),
{
    assert_by_contradiction!(is_prime(m),
            {
                let i = choose|i:nat| (1 < i < m && #[trigger] (m % i) == 0);
                assert (k % i == 0) by {lemma_mod_zero_twice(k as int, m as int, i as int)};
            })
}

proof fn lemma_drop_last_map_commute(seq: Seq<u8>)
    requires
        seq.len() >= 1,
    ensures
        seq.map(|_idx, j: u8| j as nat).drop_last() == seq.drop_last().map(|_idx, j: u8| j as nat),
{
    assert(seq.map(|_idx, j: u8| j as nat).drop_last() == seq.drop_last().map(
        |_idx, j: u8| j as nat,
    ));
}

proof fn lemma_fold_right_equivalent_for_nat_u8(factorization: Seq<u8>)
    requires
        factorization.fold_right(|x, acc: u8| (acc * x) as u8, 1u8) <= u8::MAX as u8,
        forall|i: int| 0 <= i < factorization.len() ==> factorization[i] > 0,
    ensures
        factorization.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == factorization.map(
            |_idx, j: u8| j as nat,
        ).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat),
    decreases factorization.len(),
{
    if (factorization.len() == 0) {
    } else {
        let factorization_ = factorization.drop_last();
        let last = factorization.last();

        calc! {
            (==)
            factorization.map(|_idx, j: u8| j as nat).fold_right(|x, acc: nat| acc * x, 1nat); {
                lemma_drop_last_map_commute(factorization)
            }
            factorization.drop_last().map(|_idx, j: u8| j as nat).fold_right(
                |x, acc: nat| acc * x,
                (factorization.last() as nat),
            ); {
                lemma_fold_right_pull_out_nat(
                    factorization.drop_last().map(|_idx, j: u8| j as nat),
                    (factorization.last() as nat),
                )
            }
            factorization.drop_last().map(|_idx, j: u8| j as nat).fold_right(
                |x, acc: nat| acc * x,
                1nat,
            ) * (factorization.last() as nat); {
                lemma_fold_right_equivalent_for_nat_u8(factorization.drop_last())
            }
            factorization.drop_last().fold_right(|x, acc: nat| (acc * x) as nat, 1nat) * (
            factorization.last() as nat); {
                lemma_fold_right_pull_out_hybrid(
                    factorization.drop_last(),
                    (factorization.last() as nat),
                )
            }
            factorization.drop_last().fold_right(
                |x, acc: nat| (acc * x) as nat,
                (factorization.last() as nat),
            );
        }
    }
}

pub fn factorize(n: u8) -> (factorization: Vec<u8>)
    requires
        1 <= n <= u8::MAX,
    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
{
    let mut factorization = vec![];
    let mut k = n;
    let mut m = 2u16;
    let ghost n_nat = n as nat;
    while (m <= n as u16)
        invariant
            1 < m < n + 2,
            n <= u8::MAX,
            0 < k <= n,
            forall|j: u8| 1 < j < m ==> #[trigger] (k % j) != 0,
            factorization@.fold_right(|x: u8, acc: nat| (acc * x) as nat, 1nat) == n as nat / (
            k as nat),
            forall|i: nat|
                0 <= i < factorization.len() ==> #[trigger] is_prime(
                    factorization[i as int] as nat,
                ),
            forall|i: int| 0 <= i < factorization.len() ==> factorization[i] > 0,
            n % k == 0,
            forall|i: nat, j: nat|
                (1 < i <= j < factorization.len()) ==> ((#[trigger] factorization[i as int] as nat)
                    <= (#[trigger] factorization[j as int] as nat) <= m),
    {
        if (k as u16 % m == 0) {
            assert(is_prime(m as nat)) by { lemma_first_divisor_is_prime(k as nat, m as nat) };
            let ghost old_factors = factorization;
            let l = factorization.len();
            factorization.insert(l, m as u8);

            assert(old_factors@.push(m as u8) == factorization@);

            assert(factorization@.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == ((m as nat)
                * (n as nat / (k as nat))) as nat) by {
                lemma_unfold_right_fold_new(factorization@, old_factors@, m as u8)
            };

            assert(n % (k / m as u8) == 0) by {
                lemma_multiple_mod_is_zero(m as int, n as int, k as int);
            };

            assert(factorization@.fold_right(|x, acc: nat| (acc * x) as nat, 1nat) == ((n as nat / (
            (k / m as u8) as nat))) as nat) by {
                lemma_multiple_mod_is_zero_new(m as int, n as int, k as int)
            };

            assert forall|j: u8| (1 < j < m && (k % j != 0)) implies #[trigger] ((k / m as u8) % j)
                != 0 by { lemma_factor_mod_is_zero(k as int, m as int, j as int) };
            assert((k as int) == ((k as int) / (m as int)) * (m as int)) by {
                lemma_fundamental_div_mod(k as int, m as int)
            };

            k = k / m as u8;
        } else {
            m = m + 1;
        }
    }
    proof {
        assert_by_contradiction!(k == 1, {
                assert (k % k == 0);
            });
    }

    assert(factorization@.map(|_idx, j: u8| j as nat).fold_right(
        |x: nat, acc: nat| (acc * x as nat),
        1nat,
    ) == n) by { lemma_fold_right_equivalent_for_nat_u8(factorization@) };
    return factorization;
}

} // verus!
fn main() {
    print!("{:?}", factorize(254));
}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def factorize(n: int) -> List[int]:
    """ Return list of prime factors of given integer in the order from smallest to largest.
    Each of the factors should be listed number of times corresponding to how many times it appeares in factorization.
    Input number should be equal to the product of all factors
    >>> factorize(8)
    [2, 2, 2]
    >>> factorize(25)
    [5, 5]
    >>> factorize(70)
    [2, 5, 7]
    """

*/

/*
### ENTRY POINT
factorize
*/

/*
### CANONICAL SOLUTION
    import math
    fact = []
    i = 2
    while i <= int(math.sqrt(n) + 1):
        if n % i == 0:
            fact.append(i)
            n //= i
        else:
            i += 1

    if n > 1:
        fact.append(n)
    return fact

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(2) == [2]
    assert candidate(4) == [2, 2]
    assert candidate(8) == [2, 2, 2]
    assert candidate(3 * 19) == [3, 19]
    assert candidate(3 * 19 * 3 * 19) == [3, 3, 19, 19]
    assert candidate(3 * 19 * 3 * 19 * 3 * 19) == [3, 3, 3, 19, 19, 19]
    assert candidate(3 * 19 * 19 * 19) == [3, 19, 19, 19]
    assert candidate(3 * 2 * 3) == [2, 3, 3]

*/
