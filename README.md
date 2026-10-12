# The Wₚ supercongruence

For every prime $p\ge7$,

$$
W_p=\sum_{n=0}^{p-1}\frac{(6n)!}{(n!)^6\,10^{6n}}
(532n^2+126n+9)\equiv9p^2\pmod{p^5}.
$$

The congruence is in the ring of rational numbers whose denominators are
coprime to $p$.

The Lean theorem is `WPReview.literal_all_primes` in
[`src/WPReview/AllPrime.lean`](src/WPReview/AllPrime.lean).
The complete written proof is [`docs/WpProof.pdf`](docs/WpProof.pdf).

## Reproduce

Install Python 3.11+, Node.js/npm, Git, and Lean's `elan`.
Use Linux or WSL and run from this folder:

```sh
python3 scripts/reproduce.py dependencies
python3 scripts/reproduce.py five
python3 scripts/reproduce.py kernel
```

The project pins Lean 4.33.1 and its mathlib dependencies. The checks compile
the proof, print its statement and axioms, and replay it in Lean's kernel.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`;
`sorry` and additional axioms are prohibited.

See [REPRODUCING.md](REPRODUCING.md) for build details.
