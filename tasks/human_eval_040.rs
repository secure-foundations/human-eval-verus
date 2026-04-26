/*
### ID
HumanEval/40
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn triples_sum_to_zero_spec(v: Seq<int>) -> bool {
    exists|i: int, j: int, k: int| 0 <= i < j < k < v.len() && (v[i] + v[j] + v[k] == 0)
}

fn triples_sum_to_zero(s: Vec<i32>) -> (out: bool)
    ensures
        out == triples_sum_to_zero_spec(s@.map_values(|x: i32| x as int)),
{
    if s.len() < 3 {
        return false;
    }
    let mut i = 0;
    while (i < s.len() - 2)
        invariant
            0 <= i <= s.len() - 2,
            forall|i0: int, j0: int, k0: int|
                0 <= i0 < i && i0 < j0 < k0 < s.len() ==> s[i0] + s[j0] + s[k0] != 0,
        decreases s.len() - i,
    {
        let mut j = i + 1;
        while j < s.len() - 1
            invariant
                0 <= i <= s.len() - 2,
                0 <= i < j <= s.len() - 1,
                forall|i0: int, j0: int, k0: int|
                    0 <= i0 < i && i0 < j0 < k0 < s.len() ==> s[i0] + s[j0] + s[k0] != 0,
                forall|j0: int, k0: int|
                    i < j0 < j && j0 < k0 < s.len() ==> s[i as int] + s[j0] + s[k0] != 0,
            decreases s.len() - j,
        {
            let mut k = j + 1;
            while k < s.len()
                invariant
                    0 <= i <= s.len() - 2,
                    0 <= i < j <= s.len() - 1,
                    0 <= i < j < k <= s.len(),
                    forall|i0: int, j0: int, k0: int|
                        0 <= i0 < i && i0 < j0 < k0 < s.len() ==> s[i0] + s[j0] + s[k0] != 0,
                    forall|j0: int, k0: int|
                        i < j0 < j && j0 < k0 < s.len() ==> s[i as int] + s[j0] + s[k0] != 0,
                    forall|k0: int| j < k0 < k ==> s[i as int] + s[j as int] + s[k0] != 0,
                decreases s.len() - k,
            {
                let si_p_j = s[i].checked_add(s[j]);
                if ((s[i] as i64) + (s[j] as i64) + (s[k] as i64) == 0) {
                    assert(0 <= i < j < k < s.len());
                    assert(s[i as int] + s[j as int] + s[k as int] == 0);

                    proof {
                        let ghost sv = s@.map_values(|x: i32| x as int);
                        // Needed to convince verifier that mapings and s comparation are related
                        assert(sv[i as int] == s[i as int] as int);
                        assert(sv[j as int] == s[j as int] as int);
                        assert(sv[k as int] == s[k as int] as int);
                    }
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return false;
}

fn static_assert() {
    let x1 = triples_sum_to_zero(vec![1, 3, 5, 0]);
    assert(x1 == false);

    let v = vec![1, 3, -2, 1];
    let x2 = triples_sum_to_zero(v);
    proof {
        let seq = v@.map_values(|x: i32| x as int);
        assert(seq[0] + seq[2] + seq[3] == 0);
        assert(triples_sum_to_zero_spec(seq));
    }
    assert(x2 == true);

    let x3 = triples_sum_to_zero(vec![1, 2, 3, 7]);
    assert(x3 == false);

    let v = vec![2, 4, -5, 3, 9, 7];
    let x4 = triples_sum_to_zero(vec![2, 4, -5, 3, 9, 7]);
    proof {
        let seq = v@.map_values(|x: i32| x as int);
        assert(seq[0] + seq[2] + seq[3] == 0);
        assert(triples_sum_to_zero_spec(seq));
    }
    assert(x4 == true);

    let x5 = triples_sum_to_zero(vec![1]);
    assert(x5 == false);
}

} // verus!
fn main() {
    // RUNTIME ASSERTIONS
    assert_eq!(triples_sum_to_zero(vec![1, 3, 5, 0]), false);
    assert_eq!(triples_sum_to_zero(vec![1, 3, -2, 1]), true);
    assert_eq!(triples_sum_to_zero(vec![1, 2, 3, 7]), false);
    assert_eq!(triples_sum_to_zero(vec![2, 4, -5, 3, 9, 7]), true);
    assert_eq!(triples_sum_to_zero(vec![1]), false);

    println!("All tests passed!");
}

/*
### VERUS END
*/

/*
### PROMPT


def triples_sum_to_zero(l: list):
    """
    triples_sum_to_zero takes a list of integers as an input.
    it returns True if there are three distinct elements in the list that
    sum to zero, and False otherwise.

    >>> triples_sum_to_zero([1, 3, 5, 0])
    False
    >>> triples_sum_to_zero([1, 3, -2, 1])
    True
    >>> triples_sum_to_zero([1, 2, 3, 7])
    False
    >>> triples_sum_to_zero([2, 4, -5, 3, 9, 7])
    True
    >>> triples_sum_to_zero([1])
    False
    """

*/

/*
### ENTRY POINT
triples_sum_to_zero
*/

/*
### CANONICAL SOLUTION
    for i in range(len(l)):
        for j in range(i + 1, len(l)):
            for k in range(j + 1, len(l)):
                if l[i] + l[j] + l[k] == 0:
                    return True
    return False

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate([1, 3, 5, 0]) == False
    assert candidate([1, 3, 5, -1]) == False
    assert candidate([1, 3, -2, 1]) == True
    assert candidate([1, 2, 3, 7]) == False
    assert candidate([1, 2, 5, 7]) == False
    assert candidate([2, 4, -5, 3, 9, 7]) == True
    assert candidate([1]) == False
    assert candidate([1, 3, 5, -100]) == False
    assert candidate([100, 3, 5, -100]) == False


*/
