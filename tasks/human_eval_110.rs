/*
### ID
HumanEval/110
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;

verus! {

spec fn swap(lst1: Seq<int>, lst2: Seq<int>, id: (int, int)) -> (Seq<int>, Seq<int>)
    recommends
        0 <= id.0 < lst1.len(),
        0 <= id.1 < lst2.len(),
{
    let o1 = lst1[id.0];
    let o2 = lst2[id.1];
    (lst1.update(id.0, o2), lst2.update(id.1, o1))
}

proof fn same_swap_no_change_seq(lst1: Seq<int>, lst2: Seq<int>, swaps: Seq<(int, int)>)
    requires
        swaps.len() == 2,
        0 <= swaps[0].0 < lst1.len(),
        0 <= swaps[0].1 < lst2.len(),
        swaps[0] == swaps[1],
    ensures
        (lst1, lst2) == apply_swaps(lst1, lst2, swaps),
{
    reveal_with_fuel(apply_swaps, 3);
}

spec fn all_elements_are_even(lst: Seq<int>) -> bool {
    forall|i: int| 0 <= i < lst.len() ==> lst[i] % 2 == 0
}

proof fn elements_all_even_implies_counts(lst: Seq<int>)
    requires
        lst.len() > 0,
    ensures
        all_elements_are_even(lst) == (count_even(lst) > 0 && count_odd(lst) == 0),
    decreases lst.len(),
{
    reveal_with_fuel(count_even, 2);
    reveal_with_fuel(count_odd, 2);
    if (lst.len() == 1) {
        assert(all_elements_are_even(lst) == (count_even(lst) > 0 && count_odd(lst) == 0));
    } else {
        let first = seq![lst.first()];
        let last = lst.drop_first();
        count_odd_concat(first, last);
        count_even_concat(first, last);
        assert(lst == first + last);
        elements_all_even_implies_counts(lst.drop_first());
        assert(all_elements_are_even(lst) == (count_even(lst) > 0 && count_odd(lst) == 0));
    }
}

spec fn apply_swaps(lst1: Seq<int>, lst2: Seq<int>, swaps: Seq<(int, int)>) -> (Seq<int>, Seq<int>)
    decreases swaps.len(),
{
    if swaps.len() == 0 {
        (lst1, lst2)
    } else {
        if (0 <= swaps[0].0 < lst1.len() && 0 <= swaps[0].1 < lst2.len()) {
            let res = swap(lst1, lst2, swaps[0]);
            apply_swaps(res.0, res.1, swaps.drop_first())
        } else {
            (lst1, lst2)
        }
    }
}

spec fn swaps_sequence_transforms_lst1_into_an_even_list(
    lst1: Seq<int>,
    lst2: Seq<int>,
    swaps: Seq<(int, int)>,
) -> bool {
    let res = apply_swaps(lst1, lst2, swaps);
    all_elements_are_even(res.0)
}

spec fn exists_a_swap_that_transforms_lst1_into_an_even_list(
    lst1: Seq<int>,
    lst2: Seq<int>,
) -> bool {
    exists|s: Seq<(int, int)>| swaps_sequence_transforms_lst1_into_an_even_list(lst1, lst2, s)
}

spec fn count_odd(s: Seq<int>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_odd(s.drop_last()) + if s.last() % 2 != 0 {
            1 as nat
        } else {
            0 as nat
        }
    }
}

proof fn count_odd_concat(s: Seq<int>, s_rest: Seq<int>)
    ensures
        count_odd(s + s_rest) == count_odd(s) + count_odd(s_rest),
    decreases s_rest,
{
    reveal_with_fuel(count_odd, 2);
    if (s_rest.len() == 0) {
    } else {
        assert((s + s_rest).drop_last() == s + s_rest.drop_last());
        count_odd_concat(s, s_rest.drop_last());
    }
}

spec fn count_even(s: Seq<int>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_even(s.drop_last()) + if s.last() % 2 == 0 {
            1 as nat
        } else {
            0 as nat
        }
    }
}

proof fn count_even_concat(s: Seq<int>, s_rest: Seq<int>)
    ensures
        count_even(s + s_rest) == count_even(s) + count_even(s_rest),
    decreases s_rest,
{
    reveal_with_fuel(count_even, 2);
    if (s_rest.len() == 0) {
    } else {
        assert((s + s_rest).drop_last() == s + s_rest.drop_last());
        count_even_concat(s, s_rest.drop_last());
    }
}

proof fn count_greater_implies_swap_existence(lst1: Seq<int>, lst2: Seq<int>)
    requires
        lst1.len() > 0,
        lst2.len() > 0,
    ensures
        (count_even(lst2) >= count_odd(lst1))
            == exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2),
{
    if count_even(lst2) >= count_odd(lst1) {
        enough_evens_implies_swap_existence(lst1, lst2);
    }
    if (exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2)) {
        swap_existence_implies_enough_evens(lst1, lst2);
    }
}

proof fn lemma_seq_len_count(lst: Seq<int>)
    ensures
        count_even(lst) + count_odd(lst) == lst.len(),
    decreases lst.len(),
{
    reveal_with_fuel(count_even, 2);
    reveal_with_fuel(count_odd, 2);
    if lst.len() > 0 {
        lemma_seq_len_count(lst.drop_last());
    }
}

proof fn lemma_apply_swaps_conservation(lst1: Seq<int>, lst2: Seq<int>, swaps: Seq<(int, int)>)
    ensures
        apply_swaps(lst1, lst2, swaps).0.len() == lst1.len(),
        apply_swaps(lst1, lst2, swaps).1.len() == lst2.len(),
        count_odd(apply_swaps(lst1, lst2, swaps).0) + count_odd(apply_swaps(lst1, lst2, swaps).1)
            == count_odd(lst1) + count_odd(lst2),
    decreases swaps.len(),
{
    if swaps.len() > 0 {
        if 0 <= swaps[0].0 < lst1.len() && 0 <= swaps[0].1 < lst2.len() {
            let res = swap(lst1, lst2, swaps[0]);
            swap_influence_on_counts(lst1, lst2, swaps[0].0, swaps[0].1);

            assert(res.0.len() == lst1.len());
            assert(res.1.len() == lst2.len());

            lemma_apply_swaps_conservation(res.0, res.1, swaps.drop_first());
        }
    }
}

proof fn swap_existence_implies_enough_evens(lst1: Seq<int>, lst2: Seq<int>)
    requires
        exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2),
    ensures
        count_even(lst2) >= count_odd(lst1),
{
    if (count_even(lst2) < count_odd(lst1)) {
        reveal_with_fuel(count_odd, 2);
        let v = choose|s: Seq<(int, int)>|
            swaps_sequence_transforms_lst1_into_an_even_list(lst1, lst2, s);

        let res = apply_swaps(lst1, lst2, v);
        lemma_apply_swaps_conservation(lst1, lst2, v);
        lemma_seq_len_count(res.1);
        lemma_seq_len_count(lst2);

        if res.0.len() > 0 {
            // res.0 is fully eaven
            elements_all_even_implies_counts(res.0);
        }
        // Algebraic break of this contradiction prove:
        // cout_odd(res1) + count_odd(res2) == count_odd(lst1) + count_odd(lst2)
        // count_odd(res1) = 0  (because the result is a even list)
        // count_odd(res2) <= |res2| = |lst2|
        // |lst2| = cout_odd(lst2) + count_even(lst2)
        // Joining these
        // count_odd(lst1) + count_odd(lst2) == count_odd(rest2) <= |lst2| == count_odd(lst2) + cout_even(lst2)
        // count_odd(lst1) <= count_even(lst2)
        // Reaching a contradiction

        assert(count_odd(lst1) <= count_even(lst2));
        assert(false);
    }
}

proof fn exists_even_index(lst: Seq<int>)
    requires
        count_even(lst) > 0,
    ensures
        exists|j: int| 0 <= j < lst.len() && lst[j] % 2 == 0,
    decreases lst.len(),
{
    if lst.len() == 0 {
    } else {
        if (lst[0] % 2 == 0) {
        } else {
            reveal_with_fuel(count_even, 2);
            let l_rest = lst.drop_first();
            count_even_concat(seq![lst[0]], l_rest);
            assert(lst == seq![lst[0]] + l_rest);
            exists_even_index(l_rest);
        }
    }
}

proof fn exists_odd_index(lst: Seq<int>)
    requires
        count_odd(lst) > 0,
    ensures
        exists|j: int| 0 <= j < lst.len() && lst[j] % 2 == 1,
    decreases lst.len(),
{
    if lst.len() == 0 {
    } else {
        if (lst[0] % 2 == 1) {
        } else {
            reveal_with_fuel(count_odd, 2);
            let l_rest = lst.drop_first();
            count_odd_concat(seq![lst[0]], l_rest);
            assert(lst == seq![lst[0]] + l_rest);
            exists_odd_index(l_rest);
        }
    }
}

proof fn swap_influence_on_counts(lst1: Seq<int>, lst2: Seq<int>, i: int, j: int)
    requires
        0 <= i < lst1.len(),
        0 <= j < lst2.len(),
    ensures
        count_odd(swap(lst1, lst2, (i, j)).0) == count_odd(lst1) - count_odd(seq![lst1[i]])
            + count_odd(seq![lst2[j]]),
        count_even(swap(lst1, lst2, (i, j)).0) == count_even(lst1) - count_even(seq![lst1[i]])
            + count_even(seq![lst2[j]]),
        count_odd(swap(lst1, lst2, (i, j)).1) == count_odd(lst2) + count_odd(seq![lst1[i]])
            - count_odd(seq![lst2[j]]),
        count_even(swap(lst1, lst2, (i, j)).1) == count_even(lst2) + count_even(seq![lst1[i]])
            - count_even(seq![lst2[j]]),
{
    reveal_with_fuel(count_odd, 2);

    let lst1_beg = lst1.subrange(0, i);
    let lst1_med = seq![lst1[i]];
    let lst1_end = lst1.subrange(i + 1, lst1.len() as int);
    assert(lst1 == lst1_beg + lst1_med + lst1_end);
    count_odd_concat(lst1_beg, lst1_med);
    count_odd_concat(lst1_beg + lst1_med, lst1_end);
    count_even_concat(lst1_beg, lst1_med);
    count_even_concat(lst1_beg + lst1_med, lst1_end);

    let lst2_beg = lst2.subrange(0, j);
    let lst2_med = seq![lst2[j]];
    let lst2_end = lst2.subrange(j + 1, lst2.len() as int);
    assert(lst2 == lst2_beg + lst2_med + lst2_end);
    count_odd_concat(lst2_beg, lst2_med);
    count_odd_concat(lst2_beg + lst2_med, lst2_end);
    count_even_concat(lst2_beg, lst2_med);
    count_even_concat(lst2_beg + lst2_med, lst2_end);

    let lswap_0 = swap(lst1, lst2, (i, j)).0;
    let lswap_0_beg = swap(lst1, lst2, (i, j)).0.subrange(0, i);
    let lswap_0_med = seq![swap(lst1, lst2, (i, j)).0[i]];
    let lswap_0_end = swap(lst1, lst2, (i, j)).0.subrange(i + 1, lst1.len() as int);
    assert(lswap_0 == lswap_0_beg + lswap_0_med + lswap_0_end);
    count_odd_concat(lswap_0_beg, lswap_0_med);
    count_odd_concat(lswap_0_beg + lswap_0_med, lswap_0_end);
    count_even_concat(lswap_0_beg, lswap_0_med);
    count_even_concat(lswap_0_beg + lswap_0_med, lswap_0_end);
    assert(swap(lst1, lst2, (i, j)).0.subrange(0, i) == lst1.subrange(0, i));
    assert(seq![swap(lst1, lst2, (i, j)).0[i]] == seq![lst2[j]]);
    assert(swap(lst1, lst2, (i, j)).0.subrange(i + 1, lst1.len() as int) == lst1.subrange(
        i + 1,
        lst1.len() as int,
    ));

    let lswap_1 = swap(lst1, lst2, (i, j)).1;
    let lswap_1_beg = swap(lst1, lst2, (i, j)).1.subrange(0, j);
    let lswap_1_med = seq![swap(lst1, lst2, (i, j)).1[j]];
    let lswap_1_end = swap(lst1, lst2, (i, j)).1.subrange(j + 1, lst2.len() as int);
    assert(lswap_1 == lswap_1_beg + lswap_1_med + lswap_1_end);
    count_odd_concat(lswap_1_beg, lswap_1_med);
    count_odd_concat(lswap_1_beg + lswap_1_med, lswap_1_end);
    count_even_concat(lswap_1_beg, lswap_1_med);
    count_even_concat(lswap_1_beg + lswap_1_med, lswap_1_end);
    assert(swap(lst1, lst2, (i, j)).1.subrange(0, j) == lst2.subrange(0, j));
    assert(seq![swap(lst1, lst2, (i, j)).1[j]] == seq![lst1[i]]);
    assert(swap(lst1, lst2, (i, j)).1.subrange(j + 1, lst2.len() as int) == lst2.subrange(
        j + 1,
        lst2.len() as int,
    ));

}

proof fn enough_evens_implies_swap_existence(lst1: Seq<int>, lst2: Seq<int>)
    requires
        lst1.len() > 0,
        lst2.len() > 0,
        count_even(lst2) >= count_odd(lst1),
    ensures
        exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2),
    decreases count_odd(lst1),
{
    if (count_even(lst1) > 0 && count_odd(lst1) == 0) {
        // If already on the goal a simple same swap gets me same even list
        let res = swaps_sequence_transforms_lst1_into_an_even_list(
            lst1,
            lst2,
            seq![(0, 0), (0, 0)],
        );
        same_swap_no_change_seq(lst1, lst2, seq![(0, 0), (0, 0)]);
        elements_all_even_implies_counts(lst1);
        assert(exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2));
    } else {
        reveal_with_fuel(count_odd, 2);
        reveal_with_fuel(count_even, 2);

        exists_odd_index(lst1);
        exists_even_index(lst2);
        let idx1 = choose|j: int| 0 <= j < lst1.len() && lst1[j] % 2 == 1;

        let idx2 = choose|j: int| 0 <= j < lst2.len() && lst2[j] % 2 == 0;

        let (s1, s2) = swap(lst1, lst2, (idx1, idx2));

        swap_influence_on_counts(lst1, lst2, idx1, idx2);
        assert(count_odd(s1) == count_odd(lst1) - count_odd(seq![lst1[idx1]]) + count_odd(
            seq![lst2[idx2]],
        ));
        assert(count_odd(s1) == count_odd(lst1) - 1);

        assert(count_even(s2) == count_even(lst2) + count_even(seq![lst1[idx1]]) - count_even(
            seq![lst2[idx2]],
        ));
        assert(count_even(s2) == count_even(lst2) - 1);
        enough_evens_implies_swap_existence(s1, s2);

        let v = choose|s: Seq<(int, int)>|
            swaps_sequence_transforms_lst1_into_an_even_list(s1, s2, s);
        let f = seq![(idx1, idx2)] + v;
        assert(swaps_sequence_transforms_lst1_into_an_even_list(lst1, lst2, f) == true) by {
            reveal_with_fuel(apply_swaps, 2);
            assert(f.drop_first() == v);
            assert(apply_swaps(lst1, lst2, f) == apply_swaps(s1, s2, v));
            assert(swaps_sequence_transforms_lst1_into_an_even_list(s1, s2, v));
        }
        assert(exists_a_swap_that_transforms_lst1_into_an_even_list(lst1, lst2));
    }
}

fn exchange(lst1: Vec<i32>, lst2: Vec<i32>) -> (out: bool)
    requires
        lst1.len() <= i32::MAX,
        lst2.len() <= i32::MAX,
        lst1.len() > 0,
        lst2.len() > 0,
    ensures
        out == exists_a_swap_that_transforms_lst1_into_an_even_list(
            lst1@.map_values(|x| x as int),
            lst2@.map_values(|x| x as int),
        ),
{
    let mut odd_count = 0;
    let mut even_count = 0;

    for i in 0..lst1.len()
        invariant
            odd_count <= i <= lst1.len() <= i32::MAX,
            odd_count == count_odd(lst1@.subrange(0, i as int).map_values(|x| x as int)),
    {
        if lst1[i] % 2 != 0 {
            odd_count += 1;
        }
        proof {
            reveal_with_fuel(count_odd, 2);
            let l_p_1 = lst1@.subrange(0, (i + 1) as int).map_values(|x| x as int);
            let l_1 = lst1@.subrange(0, i as int).map_values(|x| x as int);
            let last = seq![lst1[i as int] as int];
            assert(l_p_1 == l_1 + last);
            count_odd_concat(l_1, last);
        }
    }

    for i in 0..lst2.len()
        invariant
            even_count <= i <= lst2.len() <= i32::MAX,
            even_count == count_even(lst2@.subrange(0, i as int).map_values(|x| x as int)),
    {
        if lst2[i] % 2 == 0 {
            even_count += 1;
        }
        proof {
            reveal_with_fuel(count_even, 2);
            let l_p_1 = lst2@.subrange(0, (i + 1) as int).map_values(|x| x as int);
            let l_1 = lst2@.subrange(0, i as int).map_values(|x| x as int);
            let last = seq![lst2[i as int] as int];
            assert(l_p_1 == l_1 + last);
            count_even_concat(l_1, last);
        }
    }

    proof {
        assert(lst2@.subrange(0, lst2.len() as int) == lst2@);
        assert(lst1@.subrange(0, lst1.len() as int) == lst1@);
    }

    if even_count >= odd_count {
        proof {
            assert(count_even(lst2@.map_values(|x| x as int)) >= count_odd(
                lst1@.map_values(|x| x as int),
            ));
            count_greater_implies_swap_existence(
                lst1@.map_values(|x| x as int),
                lst2@.map_values(|x| x as int),
            );
        }
        true
    } else {
        proof {
            assert(!(count_even(lst2@.map_values(|x| x as int)) >= count_odd(
                lst1@.map_values(|x| x as int),
            )));
            count_greater_implies_swap_existence(
                lst1@.map_values(|x| x as int),
                lst2@.map_values(|x| x as int),
            );
        }
        false
    }
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT

def exchange(lst1, lst2):
    """In this problem, you will implement a function that takes two lists of numbers,
    and determines whether it is possible to perform an exchange of elements
    between them to make lst1 a list of only even numbers.
    There is no limit on the number of exchanged elements between lst1 and lst2.
    If it is possible to exchange elements between the lst1 and lst2 to make
    all the elements of lst1 to be even, return "YES".
    Otherwise, return "NO".
    For example:
    exchange([1, 2, 3, 4], [1, 2, 3, 4]) => "YES"
    exchange([1, 2, 3, 4], [1, 5, 3, 4]) => "NO"
    It is assumed that the input lists will be non-empty.
    """

*/

/*
### ENTRY POINT
exchange
*/

/*
### CANONICAL SOLUTION
    odd = 0
    even = 0
    for i in lst1:
        if i%2 == 1:
            odd += 1
    for i in lst2:
        if i%2 == 0:
            even += 1
    if even >= odd:
        return "YES"
    return "NO"


*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([1, 2, 3, 4], [1, 2, 3, 4]) == "YES"
    assert candidate([1, 2, 3, 4], [1, 5, 3, 4]) == "NO"
    assert candidate([1, 2, 3, 4], [2, 1, 4, 3]) == "YES"
    assert candidate([5, 7, 3], [2, 6, 4]) == "YES"
    assert candidate([5, 7, 3], [2, 6, 3]) == "NO"
    assert candidate([3, 2, 6, 1, 8, 9], [3, 5, 5, 1, 1, 1]) == "NO"

    # Check some edge cases that are easy to work out by hand.
    assert candidate([100, 200], [200, 200]) == "YES"
*/
