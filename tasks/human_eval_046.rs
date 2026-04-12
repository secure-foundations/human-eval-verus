/*
### ID
HumanEval/46
*/
/*
### VERUS BEGIN
*/
use vstd::{invariant, prelude::*};

verus! {

proof fn lemma_fib4_n70_does_not_overflow()
    ensures  fib4_spec(70) <= u64::MAX
{
    assert(fib4_spec(0) == 0);
    assert(fib4_spec(1) == 0);
    assert(fib4_spec(2) == 2);
    assert(fib4_spec(3) == 0);
    assert(fib4_spec(4) == 2);
    assert(fib4_spec(5) == 4);
    assert(fib4_spec(6) == 8);
    assert(fib4_spec(7) == 14);
    assert(fib4_spec(8) == 28);
    assert(fib4_spec(9) == 54);
    assert(fib4_spec(10) == 104);
    assert(fib4_spec(11) == 200);
    assert(fib4_spec(12) == 386);
    assert(fib4_spec(13) == 744);
    assert(fib4_spec(14) == 1434);
    assert(fib4_spec(15) == 2764);
    assert(fib4_spec(16) == 5328);
    assert(fib4_spec(17) == 10270);
    assert(fib4_spec(18) == 19796);
    assert(fib4_spec(19) == 38158);
    assert(fib4_spec(20) == 73552);
    assert(fib4_spec(21) == 141776);
    assert(fib4_spec(22) == 273282);
    assert(fib4_spec(23) == 526768);
    assert(fib4_spec(24) == 1015378);
    assert(fib4_spec(25) == 1957204);
    assert(fib4_spec(26) == 3772632);
    assert(fib4_spec(27) == 7271982);
    assert(fib4_spec(28) == 14017196);
    assert(fib4_spec(29) == 27019014);
    assert(fib4_spec(30) == 52080824);
    assert(fib4_spec(31) == 100389016);
    assert(fib4_spec(32) == 193506050);
    assert(fib4_spec(33) == 372994904);
    assert(fib4_spec(34) == 718970794);
    assert(fib4_spec(35) == 1385860764);
    assert(fib4_spec(36) == 2671332512);
    assert(fib4_spec(37) == 5149158974);
    assert(fib4_spec(38) == 9925323044);
    assert(fib4_spec(39) == 19131675294);
    assert(fib4_spec(40) == 36877489824);
    assert(fib4_spec(41) == 71083647136);
    assert(fib4_spec(42) == 137018135298);
    assert(fib4_spec(43) == 264110947552);
    assert(fib4_spec(44) == 509090219810);
    assert(fib4_spec(45) == 981302949796);
    assert(fib4_spec(46) == 1891522252456);
    assert(fib4_spec(47) == 3646026369614);
    assert(fib4_spec(48) == 7027941791676);
    assert(fib4_spec(49) == 13546793363542);
    assert(fib4_spec(50) == 26112283777288);
    assert(fib4_spec(51) == 50333045302120);
    assert(fib4_spec(52) == 97020064234626);
    assert(fib4_spec(53) == 187012186677576);
    assert(fib4_spec(54) == 360477579991610);
    assert(fib4_spec(55) == 694842876205932);
    assert(fib4_spec(56) == 1339352707109744);
    assert(fib4_spec(57) == 2581685349984862);
    assert(fib4_spec(58) == 4976358513292148);
    assert(fib4_spec(59) == 9592239446592686);
    assert(fib4_spec(60) == 18489636016979440);
    assert(fib4_spec(61) == 35639919326849136);
    assert(fib4_spec(62) == 68698153303713410);
    assert(fib4_spec(63) == 132419948094134672);
    assert(fib4_spec(64) == 255247656741676658);
    assert(fib4_spec(65) == 492005677466373876);
    assert(fib4_spec(66) == 948371435605898616);
    assert(fib4_spec(67) == 1828044717908083822);
    assert(fib4_spec(68) == 3523669487722032972);
    assert(fib4_spec(69) == 6792091318702389286);
    assert(fib4_spec(70) == 13092176959938404696);
    // This times out and per comput only also times out so here we are
    //reveal_with_fuel(fib4_spec, 70);
    // This is true but verifier cannot see it at any cost
    assert (fib4_spec(70) <= u64::MAX);
}

proof fn lemma_fib4_is_monotomic_after_inc_4(n : nat)
    ensures (n>3) ==> (fib4_spec(n) <=  fib4_spec(n+1))
    decreases n
{
    if(n <= 3){
    } else {
        lemma_fib4_is_monotomic_after_inc_4((n-1) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n-2) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n-3) as nat);
        lemma_fib4_is_monotomic_after_inc_4((n-4) as nat);
    }

}

spec fn fib4_spec(n : nat) -> (out : nat)
    decreases n
{
    match n {
        x if x <= 0 => 0,
        x if x == 1 => 0,
        x if x == 2 => 2,
        x if x == 3 => 0,
        _ => fib4_spec((n - 1) as nat) + fib4_spec((n - 2) as nat) + fib4_spec((n - 3) as nat) + fib4_spec((n - 4) as nat),
    }
}

proof fn lemma_fib4_monotonic_transitive(a: nat, b: nat)
    requires 3 <= a <= b
    ensures fib4_spec(a) <= fib4_spec(b)
    decreases b - a
{
    if a < b {
        lemma_fib4_is_monotomic_after_inc_4(a);
        lemma_fib4_monotonic_transitive((a + 1) as nat, b);
    }
}


fn fib4(n : u32) -> (out : u64)
    requires n <= 70
    ensures out == fib4_spec(n as nat)
{
    match n{
        x if x <= 0 => return 0,
        x if x == 1 => return 0,
        x if x == 2 => return 2,
        x if x == 3 => return 0,
        _ => 0
    };


    let mut x0 = 0;
    let mut x1 = 0;
    let mut x2 = 2;
    let mut x3 = 0;
    let mut i = 3;

    while (i <  n)
        invariant x3 == fib4_spec(i   as nat),
                  x2 == fib4_spec((i-1) as nat),
                  x1 == fib4_spec((i-2) as nat),
                  x0 == fib4_spec((i-3) as nat),
                  3 <= i <= n <= 70
        decreases n -i 
    {
        let x3p = x3;
        proof{
            lemma_fib4_n70_does_not_overflow();
            lemma_fib4_monotonic_transitive((i + 1) as nat, 70);
        }

        x3 = x3 + x2 + x1 + x0;

        x0 = x1 ;
        x1 = x2 ;
        x2 = x3p;
        i+= 1;
    }
    return x3;

}
// TODO: Put your solution (the specification, implementation, and proof) to the task here
fn static_checks() {

    reveal_with_fuel(fib4_spec,8);

    let x = fib4(5);
    assert(x == 4);

    let x = fib4(8);
    assert(x == 28);
}

} // verus!
fn main() {
    assert!(fib4(5) == 4);
    assert!(fib4(8) == 28);
    assert!(fib4(10) == 104);
    assert!(fib4(12) == 386);
}

/*
### VERUS END
*/

/*
### PROMPT


def fib4(n: int):
    """The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
    fib4(0) -> 0
    fib4(1) -> 0
    fib4(2) -> 2
    fib4(3) -> 0
    fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4).
    Please write a function to efficiently compute the n-th element of the fib4 number sequence.  Do not use recursion.
    >>> fib4(5)
    4
    >>> fib4(6)
    8
    >>> fib4(7)
    14
    """

*/

/*
### ENTRY POINT
fib4
*/

/*
### CANONICAL SOLUTION
    results = [0, 0, 2, 0]
    if n < 4:
        return results[n]

    for _ in range(4, n + 1):
        results.append(results[-1] + results[-2] + results[-3] + results[-4])
        results.pop(0)

    return results[-1]

*/

/*
### TEST


METADATA = {}


def check(candidate):
    assert candidate(5) == 4
    assert candidate(8) == 28
    assert candidate(10) == 104
    assert candidate(12) == 386


*/
