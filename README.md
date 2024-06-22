# VerusBench: Hand-Written Examples of Verified Verus Code

This is intended to be a collection of examples translated from the [HumanEval]
benchmark into Rust.  The goal is that each example will include a textual
prompt, a [Verus] specification that mathematically captures the prompt, Rust
code implementing the example, and any proof annotations needed for [Verus] to
verify that the code is correct.

See the [task list](./tasks.md) for which tasks have been completed and which
still need work.

Contributors will be acknowledged in any publications that may be published
about this benchmark.

[HumanEval]: https://github.com/openai/human-eval
[Verus]: https://github.com/verus-lang/verus
