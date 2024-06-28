/// Given a vector of numbers, return whether or not they are sorted
/// in ascending order. If vector has more than 1 duplicate of the same
/// number, return False. Assume no negative numbers and only integers.
///
/// # Examples
///
/// ```
/// assert_eq!(is_sorted(vec![5]), true);
/// assert_eq!(is_sorted(vec![1, 2, 3, 4, 5]), true);
/// assert_eq!(is_sorted(vec![1, 3, 2, 4, 5]), false);
/// assert_eq!(is_sorted(vec![1, 2, 3, 4, 5, 6]), true);
/// assert_eq!(is_sorted(vec![1, 2, 3, 4, 5, 6, 7]), true);
/// assert_eq!(is_sorted(vec![1, 3, 2, 4, 5, 6, 7]), false);
/// assert_eq!(is_sorted(vec![1, 2, 2, 3, 3, 4]), true);
/// assert_eq!(is_sorted(vec![1, 2, 2, 2, 3, 4]), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn is_sorted(lst: Vec<u32>) -> (result: bool) {
    
    let mut prev: Option<u32> = None;
    let mut counts: Vec<(u32, u32)> = Vec::new();

    let mut i = 0;
    while i < lst.len() {
        let item = lst[i];
        if let Some(p) = prev {
            if item < p {
                return false;
            }
        }

        let mut found = false;
        let mut new_counts = Vec::new();
        let mut j = 0;
        while j < counts.len() {
            let (count_item, count_val) = counts[j];
            if count_item == item {
                let new_count = count_val + 1;
                if new_count > 2 {
                    return false;
                }
                new_counts.push((count_item, new_count));
                found = true;
            } else {
                new_counts.push((count_item, count_val));
            }
            j += 1;
        }
        if !found {
            new_counts.push((item, 1));
        }
        counts = new_counts;

        prev = Some(item);
        i += 1;
    }
    true
}
}
