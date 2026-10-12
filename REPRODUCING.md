# Reproducing the proof

Use Linux or WSL with Python 3.11+, Git, Node.js/npm, and Lean's `elan`.
Start in a fresh extraction of this package, without an existing `.lake/`.

```sh
elan toolchain install leanprover/lean4:v4.33.1
python3 scripts/reproduce.py dependencies
python3 scripts/reproduce.py five
python3 scripts/reproduce.py kernel
```

The configuration pins the public dependencies. Setup changes only the
pinned mathlib checkout's `lean-toolchain` from 4.33.0 to 4.33.1, matching
this proof's Lean version. Node.js/npm build ProofWidgets' public assets.
The first build compiles the dependency libraries and can take substantial
time and disk space. No previous W_p compiled objects are supplied or used.

## What to check

The target is `WPReview.literal_all_primes`: every natural prime `p >= 7`
satisfies the exact congruence in the README. The separately written formula
in `Verification.Challenge` is connected to that export by proved equalities
in `Verification.Binding`. The equality branch of `RationalCongruent`
handles a zero difference; otherwise the difference has p-adic valuation
at least five. `WPReview.literal_congruence_iff` also gives the equivalent
integer divisibility statement after clearing the denominator.

The fixed five checks are:

1. Compile sources with `--trust=0 -DwarningAsError=true`. The integration
   build strictly compiles the 903 unchanged proof providers once; the
   explicit `lake env lean` command additionally checks each of the four
   new entry/verification sources.
2. Read the plain-text source-search capture and resolve its hits using
   `SOURCE_SEARCH_REVIEW.md`.
3. Read the complete named theorem types and axiom outputs from
   `Verification.TypesAndAxioms`. Only `propext`, `Classical.choice`, and
   `Quot.sound` are allowed.
4. Check any generated auxiliary exposed by those reports in the same way.
5. Confirm that `lake build` completes.

The `five` command captures these outputs under `verification/results/`.
Its exit status does not replace reading the statement, search hits, and
axiom reports. The package's four new sources form the packaging unit;
there is no second unchanged-source replay of all proof providers.

## Kernel replay

The final command runs:

```sh
lake env leanchecker --fresh --verbose Verification.Binding
```

It rechecks the explicit congruence and its imported proof declarations in
a fresh Lean kernel environment. Require a zero exit code. This uses Lean's
kernel, rather than a separately implemented proof checker.

Keep build captures locally; `.lake/` and `verification/results/` are
excluded from publication. The PDF contains the complete written proof;
the TeX source is excluded. Independent reproduction from a fresh extraction
passed the strict build, all five checks, and the fresh Lean kernel replay.
