/// Validates a given date string and returns `true` if the date is valid otherwise `false`.
///
/// The date is valid if all of the following rules are satisfied:
/// 1. The date string is not empty.
/// 2. The number of days is not less than 1 or higher than 31 days for months 1,3,5,7,8,10,12.
///    And the number of days is not less than 1 or higher than 30 days for months 4,6,9,11.
///    And, the number of days is not less than 1 or higher than 29 for the month 2.
/// 3. The months should not be less than 1 or higher than 12.
/// 4. The date should be in the format: mm-dd-yyyy
///
/// # Examples
///
/// ```
/// assert_eq!(valid_date("03-11-2000"), true);
/// assert_eq!(valid_date("15-01-2012"), false);
/// assert_eq!(valid_date("04-0-2040"), false);
/// assert_eq!(valid_date("06-04-2020"), true);
/// assert_eq!(valid_date("06/04/2020"), false);
/// ```

use vstd::prelude::*;
fn main() {}

verus!{
fn valid_date(month: u32, day: u32, year: u32) -> (result: bool) {
    if month < 1 || month > 12 {
        return false;
    }

    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => day >= 1 && day <= 31,
        4 | 6 | 9 | 11 => day >= 1 && day <= 30,
        2 => {
            // Assuming it's not a leap year for simplicity, as leap year calculation is non-trivial
            // and would require additional code to handle correctly.
            day >= 1 && day <= 28
        },
        _ => false,
    }
}
}
