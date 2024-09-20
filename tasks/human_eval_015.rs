

/*
### ID
HumanEval/15
*/
/*
### VERUS BEGIN
*/
use vstd::prelude::*;



verus! {

    // specification

    pub closed spec fn single_digit_number_to_char(n : nat) -> char
    {
        if n == 0 {
            '0'
        } else if n == 1 {
            '1'
        } else if n == 2 {
            '2'
        } else if n == 3 {
            '3'
        } else if n == 4 {
            '4'
        } else if n == 5 {
            '5'
        } else if n == 6 {
            '6'
        } else if n == 7 {
            '7'
        } else if n == 8 {
            '8'
        } else {
            '9'
        }
}

    pub closed spec fn number_to_char(n : nat) -> Seq<char>
        decreases n
    {
        if (n == 0) {
            seq![]
        } else {
            number_to_char(n / 10).add(seq![single_digit_number_to_char(n % 10)])
        }
    }

    pub open spec fn string_sequence(n : nat) -> Seq<char> 
        decreases n
    {
        if n == 0 {
            seq!['0']
        } else {
            string_sequence((n-1) as nat).add(seq![' '].add(number_to_char(n)))
        }
    }

    // proof fn sanity_check()
    //     {
    //         assert (string_sequence(1) == seq!['0', ' ', '1']) by (compute);
    //         assert (string_sequence(3) == seq!['0', ' ', '1', ' ', '2', ' ', '3']) by (compute);
    //         assert ((number_to_char(158) == seq!['1', '5', '8'])) by (compute);
    //     }

    // implementation
    fn single_digit_number_to_char_impl(n : u8) -> (output : char)
        requires 0 <= n <= 9
        ensures single_digit_number_to_char(n as nat) == output
    {
        if n == 0 {
            '0'
        } else if n == 1 {
            '1'
        } else if n == 2 {
            '2'
        } else if n == 3 {
            '3'
        } else if n == 4 {
            '4'
        } else if n == 5 {
            '5'
        } else if n == 6 {
            '6'
        } else if n == 7 {
            '7'
        } else if n == 8 {
            '8'
        } else {
            '9'
        }
    }


    pub fn number_to_char_impl(n : u8) -> (char_vec : Vec<char>)
        ensures char_vec@ == number_to_char(n as nat)
    {
        let mut i = n;
        let mut output = vec![];

        while (i > 0) 
            invariant
                number_to_char(n as nat) == number_to_char(i as nat).add(output@),
        {
            let m = i % 10;
            let current = single_digit_number_to_char_impl(m);

            // assert (number_to_char(i as nat) == number_to_char((i/10) as nat).add(seq![single_digit_number_to_char((i % 10) as nat)]));
            // assert (number_to_char(n as nat) == number_to_char((i/10) as nat).add(seq![single_digit_number_to_char((i % 10) as nat)]).add(output@));

            output.insert(0, current);
            i = i / 10;

            assert (number_to_char(n as nat) == number_to_char(i as nat).add(output@));
           }
        return output;
    }




    fn string_sequence_impl(n : u8) -> (string_seq : Vec<char>)
        requires n >= 0 
        ensures string_seq@ == string_sequence(n as nat)
    {
        let mut i = n;
        let mut output = vec![];
        while (i > 0) 
            invariant n >= i >= 0,
                        string_sequence(n as nat) == string_sequence(i as nat) + output@
            decreases i
        {
            let mut next = number_to_char_impl(i);

            // assert (string_sequence((i) as nat) == string_sequence((i-1) as nat).add(seq![' '].add(number_to_char(i as nat))));

            // assert (string_sequence((n) as nat) == string_sequence((i-1) as nat).add(seq![' '].add(number_to_char(i as nat))) + output@);

            next.append(&mut output);
            output = next;
            // assert (string_sequence((n) as nat) == string_sequence((i-1) as nat).add(seq![' ']) + output@);
            output.insert(0, ' ');
            i = i - 1;

            assert (string_sequence((n) as nat) == string_sequence((i) as nat) + output@);
        }
        output.insert(0, '0');
        assert (string_sequence(n as nat) == output@);
        return output;
    }

} // verus!
fn main() {
    // print!("{:?}", number_to_char_impl(158));
    // print!("{:?}", string_sequence_impl(20));
    }

/*
### VERUS END
*/

/*
### PROMPT


def string_sequence(n: int) -> str:
    """ Return a string containing space-delimited numbers starting from 0 upto n inclusive.
    >>> string_sequence(0)
    '0'
    >>> string_sequence(5)
    '0 1 2 3 4 5'
    """

*/

/*
### ENTRY POINT
string_sequence
*/

/*
### CANONICAL SOLUTION
    return ' '.join([str(x) for x in range(n + 1)])

*/

/*
### TEST


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(0) == '0'
    assert candidate(3) == '0 1 2 3'
    assert candidate(10) == '0 1 2 3 4 5 6 7 8 9 10'

*/

