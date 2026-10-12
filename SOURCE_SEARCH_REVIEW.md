# Plain-text source-search resolutions

The preparation search read all 903 preserved Lean sources and the four new
entry/verification sources. It found 269 lines matching the fixed FIVE
search strings. The following sentences resolve the actual occurrences,
grouped by their exact nature; the reproduction run preserves each line and
its location in `source-search.txt` so the reader can check every occurrence.

- Every `partial` hit is part of an ordinary identifier for a derivative,
  finite partial sum, or partial-fraction theorem (`partialS`, `partialX`,
  `partialSum`, or `partialFractions`, including names containing those
  identifiers); none is a `partial` declaration.
- Every `constant ` hit is ordinary mathematical prose about a constant
  coefficient/function, or the end of an ordinary identifier immediately
  before whitespace (`*_constant`, `*_nonconstant`, or `hconstant`); none
  declares an uninterpreted `constant`.
- The single `elab` hit at
  `src/WPFiniteCarry/InfinityExpansion.lean:3` is the word `elaboration` in a
  source comment and introduces no elaborator.
- The macro at `src/WPActualAngularSourceIdentity.lean:20`,
  `prove_actual_angular_entry`, expands to an explicit sequence of ordinary
  `have`, `simp`, `rw`, `norm_num`, `field_simp`, and ring tactics proving
  rational-function identities from proved nonzero denominator facts; it
  registers no command/term elaborator, inserts no declaration, and changes
  no environment or kernel-checking option.
- The macro at `src/WPActualConductorRows.lean:166`,
  `prove_actual_conductor_entry`, likewise expands to ordinary algebraic
  proof tactics on the displayed bivariate rational functions and proved
  denominator facts; its `try` tactics may leave goals but cannot supply a
  proof unless the enclosing theorem closes them, and it inserts no
  declaration or checking bypass.

There are no matches for `sorry`, `admit`, `unsafe`, `native_decide`,
`axiom `, `implemented_by`, or `extern` in the package Lean sources.
The two tactic macros and substring hits were retained byte-for-byte instead
of rewriting reviewed proof providers. This note resolves textual hits; the
named-axiom reading, strict source compilation, integration build and fresh
kernel replay supply their own distinct verification evidence.
