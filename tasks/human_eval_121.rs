
// 121

/*
### ID
HumanEval/121
*/
/*
### VERUS BEGIN
*/


// TODO: Put your solution (the specification, implementation, and proof) to the task here


use vstd::prelude::*;

verus! {
    spec fn odd_even_pos_sum_from(s: Seq<int>, start_idx: nat) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            if start_idx % 2 == 0 && s[0] % 2 == 1 {
                s[0] + odd_even_pos_sum_from(s.drop_first(), start_idx + 1)
            } else {
                odd_even_pos_sum_from(s.drop_first(), start_idx + 1)
            }
        }
    }

    // Auxiliary lemma to be able to use the recursive definition on a while interactive way
    proof fn lemma_extend_sum(prefix: Seq<int>, next: Seq<int>, start_idx: nat)
        requires
            next.len() == 1,
        ensures
            odd_even_pos_sum_from(prefix + next, start_idx)
                ==
            odd_even_pos_sum_from(prefix, start_idx)
                +
            if ((start_idx + prefix.len()) % 2 == 0 && next[0] % 2 == 1) {
                next[0]
            } else {
                0
            }
        decreases prefix.len()
    {
        if prefix.len() == 0 {
            reveal_with_fuel(odd_even_pos_sum_from, 2);
        } else {
            let tail = prefix.drop_first();
            lemma_extend_sum(tail, next, start_idx + 1);
            reveal_with_fuel(odd_even_pos_sum_from, 2);
            assert((prefix + next).drop_first() == tail + next);
        }
    }

    fn solution(lst: Vec<i32>) -> (out: i64)
        requires lst.len() <= i32::MAX
        ensures
            out as int == odd_even_pos_sum_from(lst@.map_values(|x| x as int), 0),
    {
        let mut acc: i64 = 0;
        let mut idx: usize = 0;

        while idx < lst.len()
            invariant
                lst.len() <= i32::MAX,
                0 <= idx <= lst.len(),
                acc <= (idx as int) * (i32::MAX as int),
                acc >= (idx as int) * (i32::MIN as int),
                acc as int ==
                    odd_even_pos_sum_from(
                        lst@.subrange(0, idx as int).map_values(|x| x as int),
                        0
                    ),
            decreases lst.len() - idx
        {
            if idx % 2 == 0 && lst[idx] % 2 != 0 {
                acc = acc + (lst[idx] as i64);
            }

            proof {
                let prefix =
                    lst@.subrange(0, idx as int).map_values(|x| x as int);
                let next =
                    lst@.subrange(idx as int, idx + 1).map_values(|x| x as int);

                assert(next.len() == 1);
                assert(
                    lst@.subrange(0, idx + 1).map_values(|x| x as int)
                        ==
                    prefix + next
                );

                lemma_extend_sum(prefix, next, 0);
            }
            idx = idx + 1;
        }

        assert(
            lst@.map_values(|x| x as int)
                ==
            lst@.subrange(0, idx as int).map_values(|x| x as int)
        );
        acc
    }

    fn static_assert() -> ()
    {
        reveal_with_fuel(odd_even_pos_sum_from, 6);
        let x = solution(vec![5, 8, 7, 1]);
        assert(x == 12);
        
        let x = solution(vec![3, 3, 3, 3, 3]);
        assert(x == 9);

        let x = solution(vec![30, 13, 24, 321]);
        assert(x == 0);

        let x = solution(vec![5, 9]);
        assert(x == 5);

        let x = solution(vec![2, 4, 8]);
        assert(x == 0);

        let x = solution(vec![30, 13, 23, 32]);
        assert(x == 23);

        let x = solution(vec![3, 13, 2, 9]);
        assert(x == 3);
    }
} // verus!

fn main() {
    assert_eq!(solution(vec![5, 8, 7, 1]), 12);
    assert_eq!(solution(vec![3, 3, 3, 3, 3]), 9);
    assert_eq!(solution(vec![30, 13, 24, 321]), 0);
    assert_eq!(solution(vec![5, 9]), 5);
    assert_eq!(solution(vec![2, 4, 8]), 0);
    assert_eq!(solution(vec![30, 13, 23, 32]), 23);
    assert_eq!(solution(vec![3, 13, 2, 9]), 3);
    println!("All tests passed!");
}


/*
### VERUS END
*/

/*
### PROMPT

def solution(lst):
    """Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.


    Examples
    solution([5, 8, 7, 1]) ==> 12
    solution([3, 3, 3, 3, 3]) ==> 9
    solution([30, 13, 24, 321]) ==>0
    """

*/

/*
### ENTRY POINT
solution
*/

/*
### CANONICAL SOLUTION
    return sum([x for idx, x in enumerate(lst) if idx%2==0 and x%2==1])

*/

/*
### TEST
def check(candidate):

    # Check some simple cases
    assert candidate([5, 8, 7, 1])    == 12
    assert candidate([3, 3, 3, 3, 3]) == 9
    assert candidate([30, 13, 24, 321]) == 0
    assert candidate([5, 9]) == 5
    assert candidate([2, 4, 8]) == 0
    assert candidate([30, 13, 23, 32]) == 23
    assert candidate([3, 13, 2, 9]) == 3

    # Check some edge cases that are easy to work out by hand.


*/
