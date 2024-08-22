/*
### ID
HumanEval/4
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_div_is_ordered, lemma_div_is_ordered_by_denominator, lemma_div_multiples_vanish, lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse};
use vstd::arithmetic::mul::{lemma_mul_inequality, lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way, lemma_mul_unary_negation};

verus! {

// NOTE: We use i32 rather than float because of lack of support for float in Verus.

/// Trusted specification functions

// Specification for what it means to sum a sequence of numbers
pub open spec fn sum(numbers: Seq<int>) -> int {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

// Specification for what it means to compute the mean of a sequence of numbers
pub open spec fn mean(values: Seq<int>) -> int
    recommends
        values.len() > 0
{
    sum(values) / (values.len() as int)
}

// Specification for what it means to compute the absolute value of a number
pub open spec fn abs(n: int) -> int
{
    if n >= 0 { n } else { -n }
}

// Specification for what it means to compute the mean absolute deviation of a sequence of numbers
pub open spec fn spec_mean_absolute_deviation(numbers: Seq<int>) -> int
    recommends
        numbers.len() > 0
{
    let avg = mean(numbers);
    sum(numbers.map(|_index, n: int| abs(n - avg))) / (numbers.len() as int)
}

/// Lemmas used in proving correctness

// This lemma establishes that if every element of a sequence of
// numbers `numbers` is between `min` and `max` inclusive, then their
// sum is between `numbers.len() * min` and `numbers.len() * max`
// inclusive.
proof fn lemma_sum_bound(numbers: Seq<int>, min: int, max: int)
    requires
        forall|i| 0 <= i < numbers.len() ==> min <= #[trigger] numbers[i] <= max,
    ensures
        numbers.len() * min <= sum(numbers) <= numbers.len() * max,
    decreases numbers.len(),
{
    if numbers.len() != 0 {
        lemma_sum_bound(numbers.drop_last(), min, max);
        lemma_mul_is_distributive_add_other_way(min, numbers.len() - 1, 1);
        lemma_mul_is_distributive_add_other_way(max, numbers.len() - 1, 1);
    }
}


// This lemma establishes that if every element of a sequence of
// numbers `numbers` is between `min` and `max` inclusive, and if
// certain other conditions apply, then their sum divided by
// `denominator` is between `min` and `max` inclusive. Those
// conditions are that `denominator >= numbers.len()`, `denominator >
// 0`, `min <= 0`, and `max >= 0`.
proof fn lemma_sum_ratio_bound(numbers: Seq<int>, denominator: int, min: int, max: int)
    requires
        forall|i| 0 <= i < numbers.len() ==> min <= #[trigger] numbers[i] <= max,
        denominator >= numbers.len(),
        denominator > 0,
        min <= 0,
        max >= 0,
    ensures
        min <= sum(numbers) / denominator <= max,
{
    lemma_sum_bound(numbers, min, max);
    assert(denominator * min <= numbers.len() * min) by {
        lemma_mul_unary_negation(denominator, -min);
        lemma_mul_unary_negation(numbers.len() as int, -min);
        lemma_mul_inequality(numbers.len() as int, denominator, -min);
    }
    assert(numbers.len() * max <= denominator * max) by {
        lemma_mul_inequality(numbers.len() as int, denominator, max);
    }
    lemma_div_multiples_vanish(min, denominator);
    lemma_div_multiples_vanish(max, denominator);
    lemma_div_is_ordered(denominator * min, sum(numbers), denominator);
    lemma_div_is_ordered(sum(numbers), denominator * max, denominator);
}

// This lemma shows that the sum of the first `i + 1` elements of
// a sequence `s` is equal to the sum of the first `i` elements plus
// the `i`th element.
proof fn lemma_how_to_update_running_sum(s: Seq<int>, i: int)
    requires
        0 <= i < s.len()
    ensures
        sum(s.take(i + 1)) == sum(s.take(i)) + s[i]
{
    let q1 = s.take(i);
    let q2 = s.take(i + 1);
    assert(q2.last() == s[i]);
    assert(q2.drop_last() == q1);
}

// This lemma describes an algorithm for computing `(x + y) / d` and
// `(x + y) % d` given five inputs `d`, `x / d`, `x % d`, `y / d`, and
// `y % d`.
proof fn lemma_how_to_add_then_divide(x: int, y: int, d: int)
    requires
        d > 0,
    ensures
        if (x % d) + (y % d) >= d {
            &&& (x + y) / d == (x / d) + (y / d) + 1
            &&& (x + y) % d == (x % d) + (y % d) - d
        } else {
            &&& (x + y) / d == (x / d) + (y / d)
            &&& (x + y) % d == (x % d) + (y % d)
        }
{
    lemma_fundamental_div_mod(x, d);
    lemma_fundamental_div_mod(y, d);
    lemma_mul_is_distributive_add(d, x / d, y / d);
    if (x % d) + (y % d) >= d {
        lemma_mul_is_distributive_add(d, (x / d) + (y / d), 1);
        lemma_fundamental_div_mod_converse(x + y, d, (x / d) + (y / d) + 1, (x % d) + (y % d) - d);
    }
    else {
        lemma_fundamental_div_mod_converse(x + y, d, (x / d) + (y / d), (x % d) + (y % d));
    }
}

// This function describes consequences of dividing by 2 or more.
// Specifically, it says that if `x > 0`, then `x / d < x`. And if `x
// < 0` then `x / d < 0`.
proof fn lemma_effect_of_dividing_by_two_or_more(x: int, d: int)
    requires
        d >= 2,
    ensures
        x > 0 ==> x / d < x,
        x < 0 ==> x / d < 0,
{
    lemma_fundamental_div_mod(x, d);
    if x > 0 {
        lemma_div_is_ordered_by_denominator(x, 2, d);
    }
}

/// Subroutines used by target function

// This function divides an `i32` by a `u32` and returns the quotient
// and remainder. You need this because Verus doesn't support using
// the `/` and `%` operator on negative numbers. And even if it did,
// the Rust versions of `/` of `%` produce "wrong" results for
// negative numbers. That is, Rust rounds towards zero rather than
// computing mathematical quotient and remainder.
fn divide_i32_by_u32(x: i32, d: u32) -> (qr: (i32, u32))
    requires
        d > 0,
    ensures
        ({
            let (q, r) = qr;
            q == x as int / d as int && r == x as int % d as int
        }),
{
    // The easy case is when `x` is non-negative.
    if x >= 0 {
        return ((x as u32 / d) as i32, x as u32 % d);
    }

    // When `x` is negative, compute `-x` as a `u32`. This is a bit
    // tricky because of the special case `i32::MIN`.
    let neg_x: u32;
    if x == i32::MIN {
        if d == 1 {
            // If `x == i32::MIN` and `d == 1`, the algorithm below
            // won't work, so we special-case it here.
            return (x, 0);
        }
        else {
            // For the special case `x == i32::MIN`, we can't negate
            // it (because `-i32::MIN` isn't a valid `i32`). But we
            // can just directly assign the constant value of
            // `-i32::MIN` to a `u32`.
            neg_x = 0x80000000u32;
        }
    }
    else {
        neg_x = (-x) as u32;
    }
    assert(neg_x == -x);

    // Compute `(-x) / d` and `(-x) % d`. We can do this because `-x`
    // is non-negative and Verus supports dividing non-negative
    // numbers.

    let neg_x_div_d = neg_x / d;
    let neg_x_mod_d = neg_x % d;

    // Prove some useful things about `(-x) / d` and `(-x) % d`.

    assert(neg_x == d * neg_x_div_d + neg_x_mod_d) by {
        lemma_fundamental_div_mod(neg_x as int, d as int);
    }
    assert(neg_x_div_d <= i32::MAX) by {
        if x == i32::MIN {
            lemma_mul_inequality(2, d as int, neg_x_div_d as int);
        }
    }

    // There are two cases to consider. Case 1 is when `(-x) % d ==
    // 0`. Case 2 is when it's positive.

    if neg_x_mod_d == 0 {
        proof {
            lemma_mul_unary_negation(d as int, neg_x_div_d as int);
            assert(x == d * -neg_x_div_d);
            lemma_fundamental_div_mod_converse(x as int, d as int, -(neg_x_div_d as int), 0int);
        }
        (-(neg_x_div_d as i32), 0u32)
    }
    else {
        proof {
            lemma_mul_unary_negation(d as int, (neg_x_div_d + 1) as int);
            lemma_mul_is_distributive_add(d as int, neg_x_div_d as int, 1);
            assert(x == d as int * (-neg_x_div_d - 1) + (d - neg_x_mod_d) as int);
            lemma_fundamental_div_mod_converse(x as int, d as int, -(neg_x_div_d as int) - 1, (d - neg_x_mod_d) as int);
        }
        (-(neg_x_div_d as i32) - 1, d - neg_x_mod_d)
    }
}
    
// This function divides an `i32` by a `usize` and returns the
// quotient and remainder. You need this because Verus doesn't support
// using the `/` and `%` operator on negative numbers. And even if it
// did, the Rust versions of `/` of `%` produce "wrong" results for
// negative numbers. That is, Rust rounds towards zero rather than
// computing mathematical quotient and remainder.
fn divide_i32_by_usize(x: i32, d: usize) -> (qr: (i32, usize))
    requires
        d > 0,
    ensures
        ({
            let (q, r) = qr;
            q == x as int / d as int && r == x as int % d as int
        }),
{
    // There are three cases to consider:
    //
    // (1) `d <= u32::MAX`, so we can compute it by calling
    // `divide_i32_by_u32`.
    //
    // (2) `d > u32::MAX` and `x >= 0`, so we know that the
    // quotient and remainder are just `0` and `x`.
    //
    // (3) `d > u32::MAX` and `x < 0`, so we know that the
    // quotient and remainder are `-1` and `d + x`.

    if d <= u32::MAX as usize {
        let (q, r) = divide_i32_by_u32(x, d as u32);
        (q, r as usize)
    }
    else if x >= 0 {
        assert(0 == x as int / d as int && x == x as int % d as int) by {
            lemma_fundamental_div_mod_converse(x as int, d as int, 0, x as int);
        }
        (0, x as usize)
    }
    else {
        assert(-1 == x as int / d as int && d +  x == x as int % d as int) by {
            lemma_fundamental_div_mod_converse(x as int, d as int, -1, d + x);
        }

        // The remainder is `d + x`, but we can't directly add those
        // two values because we can't cast them to the same type. So instead
        // we compute `-x` then use subtraction to compute `d - (-x)`.
        let neg_x: usize = if x == i32::MIN { 0x80000000usize } else { (-x) as usize };
        (-1, d - neg_x)
    }
}

// This function computes the mean of a slice of `i32`s.
fn compute_mean_of_i32s(numbers: &[i32]) -> (result: i32)
    requires
        numbers.len() > 0,
    ensures
        result == mean(numbers@.map(|_index, n: i32| n as int)),
{
    // The natural way to compute the mean is to first compute the sum
    // and then divide by the length. But this won't be verifiable
    // because we can't prove the absence of overflow when summing the
    // array. So instead we use the following algorithm.
    //
    // We iterate through the elements of the slice, keeping track of
    // the running sum of the first elements indirectly. That is, we
    // don't store that running sum `s` in a variable but rather we
    // keep track of `s / numbers.len()` and `s % numbers.len()`. The
    // former is guaranteed to fit in an `i32` and the latter is
    // guaranteed to fit in a `usize`. We store these in the variables
    // `quotient` and `remainder`. At the end of the loop, we return
    // `quotient` since it's the overall sum divided by the length of
    // the slice.

    let ghost nums = numbers@.map(|_index, n: i32| n as int);
    let mut quotient: i32 = 0;
    let mut remainder: usize = 0;
    let numbers_len: usize = numbers.len();
    for i in 0..numbers_len
        invariant
            quotient == sum(nums.take(i as int)) / numbers_len as int,
            remainder == sum(nums.take(i as int)) % numbers_len as int,
            numbers_len == numbers.len(),
            nums == numbers@.map(|_index, n: i32| n as int),
    {
        let n = numbers[i];

        // Prove that:
        //
        // (1) We can go from the running sum of the first `i`
        // elements to the sum of the first `i + 1` elements by adding
        // the `i`the element.
        //
        // (2) The running sum divided by `numbers.len()` is bounded
        // between `i32::MIN` and `i32::MAX`, so the running quotient
        // can be stored in an `i32`.
        //
        // (3) We can update the running quotient and remainder using
        // an algorithm that doesn't need the running sum as input.
        // It just needs the old running quotient and remainder.

        proof {
            lemma_how_to_update_running_sum(nums, i as int);
            lemma_sum_ratio_bound(nums.take(i + 1), numbers_len as int, i32::MIN as int, i32::MAX as int);
            lemma_how_to_add_then_divide(sum(nums.take(i as int)), n as int, numbers_len as int);
        }

        let (q, r) = divide_i32_by_usize(n, numbers_len);

        if r >= numbers_len - remainder {
            // Prove that we won't overflow by adding one to `q`. This
            // follows from the facts that `q == n / numbers_len`,
            // `numbers_len >= 2`, and `q <= i32::MAX`.
            assert(q < i32::MAX) by {
                lemma_effect_of_dividing_by_two_or_more(n as int, numbers_len as int);
            }
            remainder -= (numbers_len - r);
            quotient += (q + 1);
        }
        else {
            remainder += r;
            quotient += q;
        }
    }
    
    assert(nums == nums.take(nums.len() as int));
    quotient
}

// This function computes the absolute difference between two `i32`s as a `u32`.
fn compute_absolute_difference(x: i32, y: i32) -> (z: u32)
    ensures
        z == abs(x - y),
{
    if x >= y {
        if y >= 0 || x < 0 {
            (x - y) as u32
        }
        else {
            let neg_y: u32 = if y == i32::MIN { 0x80000000u32 } else { (-y) as u32 };
            x as u32 + neg_y
        }
    }
    else {
        if x >= 0 || y < 0 {
            (y - x) as u32
        }
        else {
            let neg_x: u32 = if x == i32::MIN { 0x80000000u32 } else { (-x) as u32 };
            y as u32 + neg_x
        }
    }
}

/// Target function

pub fn mean_absolute_deviation(numbers: &[i32]) -> (result: u32)
    requires
        numbers.len() > 0,
    ensures
        result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)),
{
    let numbers_mean: i32 = compute_mean_of_i32s(numbers);
    let ghost deviations = numbers@.map(|_index, n: i32| n as int).map(|_index, n: int| abs(n - numbers_mean));

    // The natural way to compute the mean absolute deviation is to
    // first compute the sum and then divide by the length. But this
    // won't be verifiable because we can't prove the absence of
    // overflow when summing the deviations. So instead we use the
    // following algorithm.
    //
    // We iterate through the elements of the slice, keeping track of
    // the running sum of the first deviations indirectly. That is, we
    // don't store that running sum `s` in a variable but rather we
    // keep track of `s / numbers.len()` and `s % numbers.len()`. The
    // former is guaranteed to fit in an `u32` and the latter is
    // guaranteed to fit in a `usize`. We store these in the variables
    // `quotient` and `remainder`. At the end of the loop, we return
    // `quotient` since it's the overall sum divided by the length of
    // the slice.

    let mut quotient: u32 = 0;
    let mut remainder: usize = 0;
    let numbers_len: usize = numbers.len();
    for i in 0..numbers_len
        invariant
            quotient == sum(deviations.take(i as int)) / numbers_len as int,
            remainder == sum(deviations.take(i as int)) % numbers_len as int,
            numbers_len == numbers.len(),
            numbers_mean == mean(numbers@.map(|_index, n: i32| n as int)),
            deviations == numbers@.map(|_index, n: i32| n as int).map(|_index, n: int| abs(n - numbers_mean)),
    {
        let n: u32 = compute_absolute_difference(numbers[i], numbers_mean);

        // Prove that:
        //
        // (1) We can go from the running sum of the first `i`
        // elements to the sum of the first `i + 1` elements by adding
        // the `i`the element.
        //
        // (2) The running sum divided by `numbers.len()` is bounded
        // between `u32::MIN` and `u32::MAX`, so the running quotient
        // can be stored in an `u32`.
        //
        // (3) We can update the running quotient and remainder using
        // an algorithm that doesn't need the running sum as input.
        // It just needs the old running quotient and remainder.

        proof {
            lemma_how_to_update_running_sum(deviations, i as int);
            lemma_sum_ratio_bound(deviations.take(i + 1), numbers_len as int, u32::MIN as int, u32::MAX as int);
            lemma_how_to_add_then_divide(sum(deviations.take(i as int)), n as int, numbers_len as int);
        }

        let q: u32 = (n as usize / numbers_len) as u32;
        let r: usize = n as usize % numbers_len;

        if r >= numbers_len - remainder {
            // Prove that we won't overflow by adding one to `q`. This
            // follows from the facts that `q == n / numbers_len`,
            // `numbers_len >= 2`, and `q <= u32::MAX`.
            assert(q < u32::MAX) by {
                lemma_effect_of_dividing_by_two_or_more(n as int, numbers_len as int);
            }
            remainder -= (numbers_len - r);
            quotient += (q + 1);
        }
        else {
            remainder += r;
            quotient += q;
        }
    }
    
    assert(deviations == deviations.take(deviations.len() as int));
    quotient
}

} // verus!
fn main() {}

/*
### VERUS END
*/

/*
### PROMPT
from typing import List


def mean_absolute_deviation(numbers: List[float]) -> float:
    """ For a given list of input numbers, calculate Mean Absolute Deviation
    around the mean of this dataset.
    Mean Absolute Deviation is the average absolute difference between each
    element and a centerpoint (mean in this case):
    MAD = average | x - x_mean |
    >>> mean_absolute_deviation([1.0, 2.0, 3.0, 4.0])
    1.0
    """

*/

/*
### ENTRY POINT
mean_absolute_deviation
*/

/*
### CANONICAL SOLUTION
    mean = sum(numbers) / len(numbers)
    return sum(abs(x - mean) for x in numbers) / len(numbers)

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert abs(candidate([1.0, 2.0, 3.0]) - 2.0/3.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0]) - 1.0) < 1e-6
    assert abs(candidate([1.0, 2.0, 3.0, 4.0, 5.0]) - 6.0/5.0) < 1e-6


*/
