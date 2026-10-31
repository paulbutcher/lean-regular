/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Regular
meta import Regular
meta import RegularBench.Timing

/-! Grammars after CSS's value definitions, simplified where only the token kinds matter. -/

public section

namespace RegularBench.Css

open Regular Regex

inductive Kw
  | normal | italic | oblique | smallCaps | bold | bolder | lighter | condensed | expanded
  | small | medium | large | serif | sansSerif | monospace | caption | icon | menu
  | none | left | center | right | top | bottom | auto | cover | contain
  | repeatX | repeatY | repeat_ | space | round | noRepeat | scroll | fixed | local
  | borderBox | paddingBox | contentBox | minContent | maxContent
  deriving DecidableEq, Repr

/-- The kind of one component value, as known at compile time. -/
inductive Tok
  | length | percentage | number | flex | color | url | gradient | string | ident | lineNames
  | minmax | fitContent | repeatFn | kw (k : Kw) | slash | comma
  deriving DecidableEq, Repr

/-- A type or literal in a value definition. -/
inductive Ty
  | lengthPercentage | number | flex | color | image | string | customIdent | lineNames
  | minmax | fitContent | repeatFn | kw (k : Kw) | slash | comma
  deriving DecidableEq

def Tok.matches : Tok → Ty → Bool
  | .length, .lengthPercentage | .percentage, .lengthPercentage | .number, .number
  | .flex, .flex | .color, .color | .url, .image | .gradient, .image | .string, .string
  | .ident, .customIdent | .lineNames, .lineNames | .minmax, .minmax
  | .fitContent, .fitContent | .repeatFn, .repeatFn | .slash, .slash | .comma, .comma => true
  | .kw a, .kw b => a == b
  | _, _ => false

def k (x : Kw) : Regex Ty := .sym (.kw x)
def kws (xs : List Kw) : Regex Ty := oneOf (xs.map k)
def lp : Regex Ty := .sym .lengthPercentage
def commaList (r : Regex Ty) : Regex Ty := sepBy1 r (.sym .comma)

def font : Regex Ty :=
  .alt
    (seq [
      opt (someOf [kws [.normal, .italic, .oblique], kws [.normal, .smallCaps],
        .alt (kws [.normal, .bold, .bolder, .lighter]) (.sym .number),
        kws [.normal, .condensed, .expanded]]),
      .alt (kws [.small, .medium, .large]) lp,
      opt (seq [.sym .slash, oneOf [k .normal, .sym .number, lp]]),
      commaList (oneOf [.sym .string, plus (.sym .customIdent), kws [.serif, .sansSerif, .monospace]])])
    (kws [.caption, .icon, .menu])

def bgPosition : Regex Ty :=
  oneOf [
    .alt (kws [.left, .center, .right, .top, .bottom]) lp,
    seq [.alt (kws [.left, .center, .right]) lp, .alt (kws [.top, .center, .bottom]) lp],
    seq [kws [.left, .right], lp, kws [.top, .bottom], lp]]

def bgSize : Regex Ty := .alt (rep 1 2 (.alt lp (k .auto))) (kws [.cover, .contain])

def repeatStyle : Regex Ty :=
  .alt (kws [.repeatX, .repeatY]) (rep 1 2 (kws [.repeat_, .space, .round, .noRepeat]))

def box : Regex Ty := kws [.borderBox, .paddingBox, .contentBox]

def bgLayerParts : List (Regex Ty) :=
  [.alt (k .none) (.sym .image), seq [bgPosition, opt (seq [.sym .slash, bgSize])], repeatStyle,
    kws [.scroll, .fixed, .local], box, box]

def background : Regex Ty :=
  seq [.star (seq [someOf bgLayerParts, .sym .comma]), someOf (.sym .color :: bgLayerParts)]

def trackSize : Regex Ty :=
  oneOf [lp, .sym .flex, kws [.minContent, .maxContent, .auto], .sym .minmax, .sym .fitContent]

def trackList : Regex Ty :=
  seq [plus (seq [opt (.sym .lineNames), .alt trackSize (.sym .repeatFn)]), opt (.sym .lineNames)]

def explicitTrackList : Regex Ty :=
  seq [plus (seq [opt (.sym .lineNames), trackSize]), opt (.sym .lineNames)]

def gridTemplate : Regex Ty :=
  oneOf [
    k .none,
    seq [.alt (k .none) trackList, .sym .slash, .alt (k .none) trackList],
    seq [plus (seq [opt (.sym .lineNames), .sym .string, opt trackSize, opt (.sym .lineNames)]),
      opt (seq [.sym .slash, explicitTrackList])]]

open Shape

def t (x : Tok) : Regex Tok := one x
def tk (x : Kw) : Regex Tok := one (.kw x)

#bench "font: italic bold <length> / <number> <string>#"
  Accepts Tok.matches font
    (seq [tk .italic, tk .bold, t .length, t .slash, t .number, groups1 [.string] .comma])

#bench "font: <number> condensed small-caps <percentage> <ident>+, serif"
  Accepts Tok.matches font
    (seq [t .number, tk .condensed, tk .smallCaps, t .percentage, many1 .ident, t .comma,
      tk .serif])

#bench "font, rejected: <length> with families that may be absent"
  ¬Accepts Tok.matches font (seq [t .length, groups [.string] .comma])

#eval counterexample Tok.matches font (seq [t .length, groups [.string] .comma])

#bench "background: (url left top no-repeat ,)* <color> url center / cover"
  Accepts Tok.matches background
    (seq [.star (word [.url, .kw .left, .kw .top, .kw .noRepeat, .comma]),
      word [.color, .url, .kw .center, .slash, .kw .cover]])

#bench "background: (gradient <length> <percentage> / auto auto fixed border-box ,)* <color>"
  Accepts Tok.matches background
    (seq [.star (word [.gradient, .length, .percentage, .slash, .kw .auto, .kw .auto,
      .kw .fixed, .kw .borderBox, .comma]), t .color])

#bench "background, rejected: a position split by a repeat style"
  ¬Accepts Tok.matches background
    (seq [.star (word [.url, .kw .left, .kw .repeatX, .kw .top, .comma]), t .color])

#eval counterexample Tok.matches background
  (seq [.star (word [.url, .kw .left, .kw .repeatX, .kw .top, .comma]), t .color])

#bench "grid-template: <track-list> / <track-list>, each of unknown length"
  Accepts Tok.matches gridTemplate
    (seq [many1 .length, t .lineNames, t .slash, many1 .flex, t .repeatFn])

#bench "grid-template: ([names] <string> <length> [names])+ / ([names] <flex>)+"
  Accepts Tok.matches gridTemplate
    (seq [plus (word [.lineNames, .string, .length, .lineNames]), t .slash,
      plus (word [.lineNames, .flex])])

#bench "grid-template, rejected: <string>* / <flex>*"
  ¬Accepts Tok.matches gridTemplate (seq [many .string, t .slash, many .flex])

#eval counterexample Tok.matches gridTemplate (seq [many .string, t .slash, many .flex])

end RegularBench.Css
