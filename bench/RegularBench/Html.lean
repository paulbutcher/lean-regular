/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular
meta import Regular
meta import RegularBench.Timing

public section

namespace RegularBench.Html

open Regular Regex

inductive Element | caption | colgroup | thead | tbody | tr | tfoot | script | template
  deriving DecidableEq, Repr

inductive Category | caption | colgroup | thead | tbody | tr | tfoot | scriptSupporting
  deriving DecidableEq

def Element.matches : Element → Category → Bool
  | .script, .scriptSupporting | .template, .scriptSupporting => true
  | .caption, .caption | .colgroup, .colgroup | .thead, .thead | .tbody, .tbody | .tr, .tr
  | .tfoot, .tfoot => true
  | _, _ => false

/-- An optional caption, any number of column groups, an optional head, then bodies or rows,
then an optional foot, with script-supporting elements anywhere among them. -/
def table : Regex Category :=
  .interleave
    (seq [opt (.sym .caption), .star (.sym .colgroup), opt (.sym .thead),
      .alt (.star (.sym .tbody)) (plus (.sym .tr)), opt (.sym .tfoot)])
    (.star (.sym .scriptSupporting))

open Shape

#bench "table: caption, colgroup*, thead, tbody*, tfoot"
  Accepts Element.matches table
    (seq [one .caption, many .colgroup, one .thead, many .tbody, one .tfoot])

#bench "table: script*, tr+, template, script*"
  Accepts Element.matches table (seq [many .script, many1 .tr, one .template, many .script])

#bench "table, rejected: tr*, thead"
  ¬Accepts Element.matches table (seq [many .tr, one .thead])

#eval counterexample Element.matches table (seq [many .tr, one .thead])

end RegularBench.Html
