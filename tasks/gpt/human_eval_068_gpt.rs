/// Given an array representing a branch of a tree that has non-negative integer nodes
/// your task is to pluck one of the nodes and return it.
/// The plucked node should be the node with the smallest even value.
/// If multiple nodes with the same smallest even value are found return the node that has smallest index.
///
/// The plucked node should be returned in a list, [smallest_value, its index],
/// If there are no even values or the given array is empty, return an empty Vec.
///
/// # Examples
///
/// ```
/// # fn main() {
/// // Example 1:
/// assert_eq!(pluck(&[4, 2, 3]), Some((2, 1)));
/// // Explanation: 2 has the smallest even value, and 2 has the smallest index.
///
/// // Example 2:
/// assert_eq!(pluck(&[1, 2, 3]), Some((2, 1)));
/// // Explanation: 2 has the smallest even value, and 2 has the smallest index.
///
/// // Example 3:
/// assert_eq!(pluck(&[]), None);
///
/// // Example 4:
/// assert_eq!(pluck(&[5, 0, 3, 0, 4, 2]), Some((0, 1)));
/// // Explanation: 0 is the smallest value, but there are two zeros,
/// // so we will choose the first zero, which has the smallest index.
/// # }
/// ```
///
/// # Constraints
///
/// * 1 <= nodes.length <= 10000
/// * 0 <= node.value

use vstd::prelude::*;
fn main() {}

verus!{
    struct PluckResult {
        value: u32,
        index: usize,
    }

    fn pluck(arr: Vec<u32>) -> (result: Option<PluckResult>) {
        let mut min_val: Option<u32> = None;
        let mut min_idx: usize = 0;

        let mut i = 0;
        while i < arr.len() {
            let val = arr[i];
            if val % 2 == 0 {
                match min_val {
                    None => {
                        min_val = Some(val);
                        min_idx = i;
                    },
                    Some(current_min) => {
                        if val < current_min || (val == current_min && i < min_idx) {
                            min_val = Some(val);
                            min_idx = i;
                        }
                    },
                }
            }
            i += 1;
        }

        match min_val {
            Some(val) => Some(PluckResult { value: val, index: min_idx }),
            None => None,
        }
    }
}
