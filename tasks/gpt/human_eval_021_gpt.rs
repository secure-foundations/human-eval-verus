
use vstd::prelude::*;
fn main() {}

verus!{

fn rescale_to_unit(numbers: Vec<i64>) -> (rescaled_numbers: Vec<i64>) {
    let mut min = numbers[0];
    let mut max = numbers[0];

    let mut i = 0;
    while i < numbers.len() {
        let value = numbers[i];
        if value < min {
            min = value;
        }
        if value > max {
            max = value;
        }
        i += 1;
    }

    let range = max - min;
    let mut rescaled_numbers = vec![];

    i = 0;
    while i < numbers.len() {
        let value = numbers[i];
        // Convert to unsigned integers for the division operation
        if range != 0 {
            let scaled_value = ((value - min) as u64) * 1000;
            let rescaled_value = scaled_value / (range as u64);
            // Convert back to i64 after division
            rescaled_numbers.push(rescaled_value as i64);
        } else {
            // If range is zero, all numbers are the same and the rescaled value is 0
            rescaled_numbers.push(0);
        }
        i += 1;
    }

    rescaled_numbers
}
}
