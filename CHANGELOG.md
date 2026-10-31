# Changelog

## [0.1.0] - 2026-10-31

* Regular grammars with interleave, `nonEmpty`, and block-permutation `allOf`, with a proven check, run by `decide`, that every word of a shape is in a grammar, and a shortest counterexample when it is not
* `Shape.kinds` and `Shape.collapse` coarsen a shape so that a consumer can check it first and cache the result, with `Accepts.of_coarse` to carry acceptance back
