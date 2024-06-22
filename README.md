# VerusBench: Hand-Written Examples of Verified Verus Code

This is intended to be a collection of examples translated from the [HumanEval]
benchmark into Rust.  The goal is that each example will include a textual
prompt, a [Verus] specification that mathematically captures the prompt, Rust
code implementing the example, and any proof annotations needed for [Verus] to
verify that the code is correct.  We plan to use the repository to evaluate
how well AI techniques can produce Verus proofs.  It will also serve as a useful
collection of examples for people just learning Verus.

See the [task list](./tasks.md) for which tasks have been completed and which
still need work.  If you'd like to work on a task, **please put your name next
to it** on the list, so we can avoid duplicated effort.

Contributors will be acknowledged in any publications that may be published
about this benchmark.

[HumanEval]: https://github.com/openai/human-eval
[Verus]: https://github.com/verus-lang/verus
