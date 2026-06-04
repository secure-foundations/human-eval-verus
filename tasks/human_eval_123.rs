/*
### ID
HumanEval/123
*/
/*
### VERUS BEGIN
*/
use vstd::arithmetic::power::pow;
use vstd::calc;
use vstd::multiset::{lemma_update_same, Multiset};
use vstd::prelude::*;
use vstd::relations::sorted_by;
use vstd::seq_lib::{lemma_multiset_commutative, to_multiset_remove};

verus! {

broadcast use vstd::seq_lib::group_seq_properties;

/// Specification for finding a list of the odd elements of n's Collatz Sequence
pub open spec fn get_odd_collatz_spec(n: u64, fuel: int) -> Seq<u64>
    decreases fuel,
{
    if fuel <= 0 {
        Seq::empty()
    } else if n == 1 {
        seq![1]
    } else if n % 2 == 1 {
        seq![n] + get_odd_collatz_spec((3 * n + 1) as u64, fuel - 1)
    } else {
        get_odd_collatz_spec((n / 2) as u64, fuel - 1)
    }
}

/// Specification for finding the sum of the first n terms of the geometric progression of 3
/// Ex: geo_prog(3) = 3^0 + 3^1 + 3^2
pub open spec fn geo_prog(n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        pow(3, (n - 1) as nat) + geo_prog((n - 1) as nat)
    }
}

/// Specification for whether a u64 sequence is sorted
/// Credit: Task #120 by @ricostynha1
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) <= s.index(j)
}

/// Proves that swapping two elements in a sequence ensures that the multiset of the result is
/// equivalent to the multiset of the original sequence
/// Credit: Task #120 by @ricostynha1
proof fn swap_preserves_multiset(s1: Seq<u64>, s2: Seq<u64>, i: int, j: int)
    requires
        0 <= i < j < s1.len() == s2.len(),
        forall|x: int| 0 <= x < s1.len() && x != i && x != j ==> s1.index(x) == s2.index(x),
        s1.index(i) == s2.index(j),
        s1.index(j) == s2.index(i),
    ensures
        s1.to_multiset() == s2.to_multiset(),
{
    calc! {
        (==)
        s1.to_multiset(); {
            lemma_multiset_commutative(s1.take(j + 1), s1.skip(j + 1));
            assert(s1 =~= s1.take(j + 1) + s1.skip(j + 1));
        }
        s1.take(j + 1).to_multiset().add(s1.skip(j + 1).to_multiset()); {
            assert(s1.take(j + 1).to_multiset() =~= s2.take(j + 1).to_multiset()) by {
                assert(s1.take(i) == s2.take(i));
                assert(s1.subrange(i + 1, j) =~= (s2.subrange(i + 1, j)));
                swap_preserves_multiset_helper(s1, i, j);
                swap_preserves_multiset_helper(s2, i, j);
            }
            assert(s1.skip(j + 1).to_multiset() =~= s2.skip(j + 1).to_multiset()) by {
                assert(s1.skip(j + 1) =~= s2.skip(j + 1));
            }
        }
        s2.take(j + 1).to_multiset().add(s2.skip(j + 1).to_multiset()); {
            lemma_multiset_commutative(s2.take(j + 1), s2.skip(j + 1));
            assert(s2 =~= s2.take(j + 1) + s2.skip(j + 1));
        }
        s2.to_multiset();
    }
}

/// Helper for swap_preserves_multiset above
/// Credit: Task #120 by @ricostynha1
proof fn swap_preserves_multiset_helper(s: Seq<u64>, i: int, j: int)
    requires
        0 <= i < j < s.len(),
    ensures
        (s.take(j + 1)).to_multiset() =~= s.take(i).to_multiset().add(
            s.subrange(i + 1, j).to_multiset(),
        ).insert(s.index(j)).insert(s.index(i)),
{
    let fst = s.take(i);
    let snd = s.subrange(i + 1, j);

    assert((s.take(j + 1)).to_multiset() =~= fst.to_multiset().insert(s.index(i)).add(
        snd.to_multiset().insert(s.index(j)),
    )) by {
        assert(s.take(i + 1).to_multiset() =~= fst.to_multiset().insert(s.index(i))) by {
            fst.to_multiset_ensures();
            assert(fst.push(s.index(i)) =~= s.take(i + 1));
        }
        assert(s.subrange(i + 1, j + 1).to_multiset() =~= snd.to_multiset().insert(s.index(j))) by {
            snd.to_multiset_ensures();
            assert(snd.push(s.index(j)) =~= s.subrange(i + 1, j + 1));
        }
        lemma_multiset_commutative(s.take(i + 1), s.subrange(i + 1, j + 1));
        assert(s.take(i + 1) + s.subrange(i + 1, j + 1) =~= s.take(j + 1));
    }
}

/// Returns a sorted version of a u64 Vec
/// Credit: Task #120 by @ricostynha1
fn sort_seq(s: &Vec<u64>) -> (ret: Vec<u64>)
    ensures
        sorted(ret@),
        ret@.len() == s@.len(),
        s@.to_multiset() == ret@.to_multiset(),
{
    let mut sorted = s.clone();
    let mut i: usize = 0;
    while i < sorted.len()
        invariant
            i <= sorted.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> sorted@.index(j) <= sorted@.index(k),
            s@.to_multiset() == sorted@.to_multiset(),
            forall|j: int, k: int|
                0 <= j < i <= k < sorted@.len() ==> sorted@.index(j) <= sorted@.index(k),
            sorted@.len() == s@.len(),
        decreases sorted.len() - i,
    {
        let mut min_index: usize = i;
        let mut j: usize = i + 1;
        while j < sorted.len()
            invariant
                i <= min_index < j <= sorted.len(),
                forall|k: int| i <= k < j ==> sorted@.index(min_index as int) <= sorted@.index(k),
            decreases sorted.len() - j,
        {
            if sorted[j] < sorted[min_index] {
                min_index = j;
            }
            j += 1;
        }
        if min_index != i {
            let ghost old_sorted = sorted@;
            let curr_val = sorted[i];
            let min_val = sorted[min_index];
            sorted.set(i, min_val);

            sorted.set(min_index, curr_val);
            proof {
                swap_preserves_multiset(old_sorted, sorted@, i as int, min_index as int);
                assert(old_sorted.to_multiset() =~= sorted@.to_multiset());
            }
        }
        i += 1;
    }
    sorted
}

/// Proves the concrete values of pow and geo_prog in order to
/// optimize Verus performance in get_odd_collatz
proof fn pows_concrete()
    ensures
        pow(3, 0) == 1,
        pow(3, 1) == 3,
        pow(3, 2) == 9,
        pow(3, 3) == 27,
        pow(3, 4) == 81,
        pow(3, 5) == 243,
        pow(3, 6) == 729,
        pow(3, 7) == 2187,
        pow(3, 8) == 6561,
        pow(3, 9) == 19683,
        pow(3, 10) == 59049,
        pow(3, 11) == 177147,
        pow(3, 12) == 531441,
        pow(3, 13) == 1594323,
        pow(3, 14) == 4782969,
        pow(3, 15) == 14348907,
        pow(3, 16) == 43046721,
        pow(3, 17) == 129140163,
        pow(3, 18) == 387420489,
        pow(3, 19) == 1162261467,
        pow(3, 20) == 3486784401,
        geo_prog(0) == 0,
        geo_prog(1) == 1,
        geo_prog(2) == 4,
        geo_prog(3) == 13,
        geo_prog(4) == 40,
        geo_prog(5) == 121,
        geo_prog(6) == 364,
        geo_prog(7) == 1093,
        geo_prog(8) == 3280,
        geo_prog(9) == 9841,
        geo_prog(10) == 29524,
        geo_prog(11) == 88573,
        geo_prog(12) == 265720,
        geo_prog(13) == 797161,
        geo_prog(14) == 2391484,
        geo_prog(15) == 7174453,
        geo_prog(16) == 21523360,
        geo_prog(17) == 64570081,
        geo_prog(18) == 193710244,
        geo_prog(19) == 581130733,
        geo_prog(20) == 1743392200,
{
    reveal(pow);
    reveal_with_fuel(pow, 21);
    reveal_with_fuel(geo_prog, 21);
}

const MAX_FUEL: u32 = 20;

/// Implementation of get_odd_collatz
/// With the conservative assuption that x grows at every iteration, x can
/// exceed u64::MAX after 20 iterations which is why MAX_FUEL is set to 20
fn get_odd_collatz(n: u32) -> (result: Vec<u64>)
    ensures
        sorted_by(result@, |x: u64, y: u64| x <= y),
        result@.to_multiset() == get_odd_collatz_spec(n as u64, MAX_FUEL as int).to_multiset(),
        result@.len() == get_odd_collatz_spec(n as u64, MAX_FUEL as int).len(),
{
    let mut odd_collatz = Vec::new();
    let mut x = n as u64;
    let mut fuel = MAX_FUEL;
    proof {
        pows_concrete();
    }
    while fuel > 0
        invariant
            0 <= fuel <= MAX_FUEL,
            odd_collatz@ + get_odd_collatz_spec(x, fuel as int) == get_odd_collatz_spec(
                n as u64,
                MAX_FUEL as int,
            ),
            0 <= x <= (u32::MAX) * pow(3, (MAX_FUEL - fuel) as nat) + geo_prog(
                (MAX_FUEL - fuel) as nat,
            ) <= u64::MAX,
        decreases fuel,
    {
        if x == 1 {
            odd_collatz.push(1);
            fuel = 1;
        } else if x % 2 == 0 {
            x = x / 2;
        } else {
            odd_collatz.push(x);
            assert(3 * x + 1 <= u64::MAX) by {
                pows_concrete();
            }
            x = 3 * x + 1;
        }
        fuel -= 1;
        assert(x <= (u32::MAX) * pow(3, (MAX_FUEL - fuel) as nat) + geo_prog(
            (MAX_FUEL - fuel) as nat,
        ) <= u64::MAX) by {
            pows_concrete();
        }
    }
    sort_seq(&odd_collatz)
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def get_odd_collatz(n):
    """
    Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

    The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
    as follows: start with any positive integer n. Then each term is obtained from the
    previous term as follows: if the previous term is even, the next term is one half of
    the previous term. If the previous term is odd, the next term is 3 times the previous
    term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

    Note:
        1. Collatz(1) is [1].
        2. returned list sorted in increasing order.

    For example:
    get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5.
    """

*/

/*
### ENTRY POINT
get_odd_collatz
*/

/*
### CANONICAL SOLUTION
    if n%2==0:
        odd_collatz = []
    else:
        odd_collatz = [n]
    while n > 1:
        if n % 2 == 0:
            n = n/2
        else:
            n = n*3 + 1

        if n%2 == 1:
            odd_collatz.append(int(n))

    return sorted(odd_collatz)

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate(14) == [1, 5, 7, 11, 13, 17]
    assert candidate(5) == [1, 5]
    assert candidate(12) == [1, 3, 5], "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1) == [1], "This prints if this assert fails 2 (also good for debugging!)"


*/
