# Changelog

## [0.2.1] - 2026-11-01

* `accepts` and `counterexample` check a shape built by `cat`, `alt`, and `star` in time linear in its length, so a run of 100 optional letters takes 15 ms by `decide +kernel` rather than 34 s

## [0.2.0] - 2026-10-31

* `Diagnosis.unexpected` and `Diagnosis.incomplete` carry the grammar symbols that could come next, so `Diagnosis` now takes the symbol type

## [0.1.0] - 2026-10-31

* Regular grammars with interleave, `nonEmpty`, and block-permutation `allOf`, with a proven check, run by `decide`, that every word of a shape is in a grammar, and a shortest counterexample when it is not
* `Shape.kinds` and `Shape.collapse` coarsen a shape so that a consumer can check it first and cache the result, with `Accepts.of_coarse` to carry acceptance back
* `Shape.indexed` tags a shape's letters with their positions, so a counterexample says which part of the shape produced each letter
* `diagnose` says whether a word goes wrong at a letter that cannot follow the ones before it, or by ending too soon
