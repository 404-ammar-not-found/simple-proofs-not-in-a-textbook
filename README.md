# simple-proofs-not-in-a-textbook

Short, self-contained proofs of facts that "everyone knows" but that are rarely
proved carefully in standard textbooks. Each proof gets its own folder with a
LaTeX write-up (`.tex` + compiled `.pdf`) and, where possible, a Lean 4
formalization that checks it by machine.

## Proofs

### 1. The shortest path between two points is a straight line, over any ordered field

Folder: [`minimal_path_between_two_points/`](minimal_path_between_two_points/)

The usual proof works in ℝⁿ and uses square roots. This one assumes only the
ordered-field axioms, so it also holds in ℚⁿ, in ruler-and-compass geometry,
and in exact fraction arithmetic.

- **Setting.** Paths are made of finitely many straight steps. A vector *has a
  length* only when the square root of its squared length exists in the field.
- **Key lemma.** Cauchy–Schwarz, `x · y ≤ |x| |y|`, proved without taking
  square roots, including when equality holds.
- **Main theorem.** If every step of a path from **a** to **b** has a length,
  and the straight line from **a** to **b** does too, the path is at least as
  long as the straight line. With no redundant points, it equals the straight
  line's length only if it is the straight line.
- **Why lengths in the field matter.** In ℚ², going from (0,0) to (1,1) has no
  shortest path. The straight line would have length √2 ∉ ℚ, and rational
  two-step paths get as close to √2 as you like.

**Visual check.** `python3 minimal_path_between_two_points/simulation.py` (stdlib only)
writes [`simulation.svg`](minimal_path_between_two_points/simulation.svg). The left panel draws
random paths in ℝ², all longer than the straight line. The right panel draws the ℚ² paths, using
exact fractions, with lengths 10/7, 58/41, … closing in on √2 but never reaching it.

**Lean check.** [`lean/MinimalPath.lean`](minimal_path_between_two_points/lean/MinimalPath.lean)
proves the Cauchy–Schwarz lemma, the main theorem and the ℚ² example with Mathlib, with
no `sorry`. To rebuild it, install [elan](https://github.com/leanprover/elan), then:

```sh
cd minimal_path_between_two_points/lean
lake exe cache get   # download prebuilt Mathlib
lake build
```
