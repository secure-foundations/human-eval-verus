/// You are given a rectangular grid of wells. Each row represents a single well,
/// and each 1 in a row represents a single unit of water.
/// Each well has a corresponding bucket that can be used to extract water from it, 
/// and all buckets have the same capacity.
/// Your task is to use the buckets to empty the wells.
/// Output the number of times you need to lower the buckets.
///
/// Example 1:
///     Input: 
///         grid : [[0,0,1,0], [0,1,0,0], [1,1,1,1]]
///         bucket_capacity : 1
///     Output: 6
///
/// Example 2:
///     Input: 
///         grid : [[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]]
///         bucket_capacity : 2
///     Output: 5
///
/// Example 3:
///     Input: 
///         grid : [[0,0,0], [0,0,0]]
///         bucket_capacity : 5
///     Output: 0
///
/// Constraints:
///     * all wells have the same length
///     * 1 <= grid.length <= 10^2
///     * 1 <= grid[0].length <= 10^2
///     * grid[i][j] -> 0 | 1
///     * 1 <= capacity <= 10

use vstd::prelude::*;
fn main() {}

verus!{
fn max_fill(grid: Vec<Vec<u8>>, capacity: u8) -> (ret: u32) {
    let mut total_water_units = 0;
    let mut i = 0;
    while i < grid.len() {
        let row = &grid[i];
        let mut j = 0;
        while j < row.len() {
            if row[j] == 1 {
                total_water_units += 1;
            }
            j += 1;
        }
        i += 1;
    }
    // Since we can't use floating-point arithmetic, we'll use integer division and check for a remainder.
    // If there's a remainder, we need to add one more unit to account for the incomplete fill.
    let units_per_capacity = total_water_units / (capacity as u32);
    let has_remainder = total_water_units % (capacity as u32) > 0;
    if has_remainder {
        units_per_capacity + 1
    } else {
        units_per_capacity
    }
}
}