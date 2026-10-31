# Regular

A Lean 4 library of regular grammars with a decision procedure, proven correct, for whether every word of one regular language is in another. It is built to run under `decide` at compile time, so a library that types its input by a grammar, such as an HTML content model or a CSS value definition, can check a whole family of inputs at once and report a counterexample when the check fails.

It is not a general regular expression library, and does not try to be one: there is no parser for regex syntax, no matching of strings at run time, and no capture groups. Its one job is deciding inclusion between languages at compile time.

## Installation

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "regular"
git = "https://github.com/paulbutcher/lean-regular"
```

## Usage

```lean
import Regular

open Regular Regex

inductive Kind | length | percentage | color
  deriving DecidableEq, Repr

inductive Ty | lengthPercentage | color
  deriving DecidableEq

/-- A length or a percentage is a `<length-percentage>`. -/
def widens : Kind → Ty → Bool
  | .length, .lengthPercentage | .percentage, .lengthPercentage | .color, .color => true
  | _, _ => false

/-- CSS's `<length-percentage>{1,2} || <color>`. -/
def grammar : Regex Ty := someOf [rep 1 2 (.sym .lengthPercentage), .sym .color]

example : Accepts widens grammar
    (seq [Shape.one .color, Shape.one .length, Shape.opt .percentage]) := by
  decide

example : ¬Accepts widens grammar (seq [Shape.one .length, Shape.many .color]) := by
  decide

#eval counterexample widens grammar (seq [Shape.one .length, Shape.many .color])
-- some [Kind.length, Kind.color, Kind.color]
```

- A grammar is a `Regex σ` over symbols `σ`, and its words are lists of letters `α`, related to symbols by a matching function `m : α → σ → Bool` that you supply. Widening, where a narrower kind is accepted wherever a wider one is asked for, lives entirely in `m`.
- A shape is a `Regex α` over the letters themselves, describing what is known at compile time about some input: `Shape.one`, `Shape.opt`, `Shape.many`, `Shape.many1`, `Shape.word`, and `Shape.groups` and `Shape.groups1` for groups of letters with a separator between them, combined with `seq` or any other combinator.
- `Accepts m g s` says every word of the shape `s` is in the language of the grammar `g`, and it is `Decidable`, so `by decide` proves or refutes it. `accepts m g s` is the same check as a `Bool`.
- `counterexample m g s` returns a shortest word of `s` that `g` rejects, or `none` when `Accepts m g s` holds, for reporting which children or components are wrong and where.

## Grammars

- Primitives: `empty`, `eps`, `sym`, `cat`, `alt`, `star`, `interleave` (the shuffle of two languages), `nonEmpty` (the language without the empty word, CSS's `!`), and `allOf` (one word from each member, concatenated in any order, CSS's `&&`).
- `allOf` keeps each member's word contiguous, so `allOf [cat a b, c]` accepts `c a b` but not `a c b`, which `interleave` would also accept. Neither enumerates orders: their derivatives track which members remain.
- Derived: `opt`, `plus`, `pow`, `upTo`, `rep lo hi` (CSS's `{lo,hi}`), `atLeast lo` (`{lo,}`), `sepBy1 r sep` (CSS's `#` with a comma), `seq`, `oneOf`, and `someOf` (one or more members in any order, each at most once, CSS's `||`).

## Deciding

The procedure explores the product of the shape's partial derivatives (Antimirov's) with sets of the grammar's, breadth first, so a counterexample it finds is a shortest one. Everything `decide` evaluates is structurally recursive; the search runs on fuel bounded by a proven count of the reachable states. Its worst case is exponential in the size of the grammar, as any such check must be, but grammars the size of CSS shorthands decide well under a second.

`lake run bench` times `decide` and `decide +kernel` on CSS's `font`, `background`, and `grid-template`, and on HTML's `table`, each against shapes containing lists of unknown length. Plain `decide` takes from 20 to 215 ms on these, `background` being the slowest, and `decide +kernel` about half that.

## Explaining a rejection

A counterexample is a word, a list of letters, which says what sequence is wrong but not where it came from. Two functions turn it into a location:

- `Shape.indexed s` tags each letter of `s` with the position of the `sym` that produced it, numbered from 0 left to right, and checking it with `fun p s => m p.2 s` gives the same answer as checking `s` (`Shape.accepts_indexed_iff`). Its counterexample is then a list of positions in the shape: for `seq [one .caption, many .tr, one .thead]` against a `table`, `[(0, .caption), (2, .thead)]`. Indexed shapes never repeat, so check one only after the plain check has failed.
- `diagnose m g w` says how `w` goes wrong: `.unexpected i` when the letter at position `i` cannot follow the ones before it, such as a `thead` after a `tr`, and `.incomplete` when every letter can but the word stops too soon, such as a table with no rows.

## Performance in a consumer

A single check is fast, but an elaborator that runs one per element or per declaration runs hundreds per file, and they add up. Measured with 300 checks in a file, elaborated one at a time, each costs about 4 ms against a single literal child, plus about 3 ms for each further child, whatever the grammar: an element with ten literal children costs 30 ms even when its content model is `flow*`. Reusing an existing proof costs about 1 ms. Parallel elaboration, on by default, recovers less than a factor of two. To keep a file of markup or styles quick to elaborate:

- Check a coarser shape first, and fall back to the exact one only when that fails, using `Accepts.of_coarse`. `Shape.kinds` forgets order and count, which loses nothing for a grammar such as `flow*`; `Shape.collapse` keeps order but loosens repeated runs, for grammars such as `table`. The fallback costs more only on the rare element that fails, and it finds the true counterexample for the error message.
- Cache by the coarse shape. Distinct child lists rarely repeat exactly, but they coarsen to a few shapes per grammar, so proving each pair once as an auxiliary theorem and reusing it makes most checks cost 1 ms. CSS declarations repeat their exact shapes often enough to cache without coarsening.
- Leave to the types what they already enforce. Where children are typed by category and widen by coercion, only elements whose content models are structured, such as `table`, `dl`, or `ruby`, need a check.
- Prefer `decide +kernel`, which proves the same proposition in about half the time. `native_decide` is faster still, but trusts the compiler, which defeats the point of a verified check.

## Formal verification

- `accepts_iff`: `accepts m g s = true` exactly when `Accepts m g s`, where both languages are given by `Matches`, an inductive definition independent of the procedure.
- `counterexample_eq_none_iff` and `counterexample_spec`: `counterexample` returns `none` exactly when `Accepts` holds, and any word it returns matches the shape and not the grammar. `counterexample_shortest`: no word of the shape outside the grammar is shorter than the one it returns.
- `matches_allOf`: `allOf rs` matches exactly the concatenations of one word of each member, in some permutation of `rs`. `matches_someOf`: `someOf rs` matches exactly the nonempty concatenations of words of distinct members, in any order.
- `matches_rep`, `matches_atLeast`, `matches_plus`, `matches_pow`, and `matches_upTo` give the counts each repetition admits; `matches_sepBy1`, `matches_seq`, `matches_oneOf`, `matches_opt`, and `Shape.matches_word` the rest.
- `Shape.accepts_kinds` and `Shape.accepts_collapse`: each coarse shape contains the one it was made from, so `Accepts.of_coarse` transfers acceptance back.
- `Shape.matches_indexed`, `Shape.accepts_indexed_iff`, and `Shape.counterexample_indexed`: an indexed shape has the same words as its source, each letter tagged, and its counterexample with the tags removed is one to the source.
- `diagnose_accepted_iff`, `diagnose_unexpected`, and `diagnose_incomplete`: `.unexpected i` means no word of the grammar starts with the first `i + 1` letters, and `.incomplete` that the word is not in the grammar. Given that every symbol matches some letter, each shorter prefix in the first case, and every prefix in the second, does start a word of the grammar.
- `matches_cons_iff` and `nullable_iff`, the derivative property the procedure rests on, and `deriv_mem_states` with `length_states_le`, the finiteness that bounds its fuel.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
