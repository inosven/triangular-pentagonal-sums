# Sums of two triangular numbers and a pentagonal number

Draft paper, verification programs and Lean 4 formalization. Status (2026-11-26): proof written
(11 pages); checked by an independent AI referee pass, which found no error in the proofs;
formalized in Lean 4 except for the classical input (see below); not yet read by a human
mathematician.

Archived on Zenodo (2026-11-26, CC BY 4.0): version 1 is https://doi.org/10.5281/zenodo.24570763;
all versions: https://doi.org/10.5281/zenodo.24570762.

## Claimed results

Every `n >= 0` is, with `x, y, z >= 0`:

- `T(x) + T(y) + z(3z-1)/2` (Sun's Conjecture 1.10 for the triple (3,3,5), arXiv:0905.0635);
- `f(x) + y(y+d)/2 + T(z)` for `f = x(3x-1)/2, x(3x+1)/2, x(3x+5)/2` exactly when
  `d <= 17, 7, 3` (odd `d`);
- `T(x) + y(3y-1)/2 + z(3z+1)/2` (OEIS A254574).

This is 20 of the 407 tuples of Conjecture 1.5 in Sun's arXiv:1502.03056:
`(3,-1,1,d,1,1)` for `d = 1..17`, `(3,1,1,d,1,1)` for `d = 1..7`, `(3,5,1,d,1,1)` for `d = 1,3`,
`(3,e,2,2,2,0)` for `e = -1,1,5`, `(3,1,3,-1,1,1)`, `(3,5,3,1,1,1)`.

## Files

- `paper/main.tex`, `paper/main.pdf`: the paper. Build with `/Library/TeX/texbin/pdflatex main.tex` (twice).
  What is new is the alternating sequence of moves and the infinite-order rotation argument
  (Theorems 3.2, 3.3); the move itself is in Sun (2015) and Cao et al. (2026), and the
  non-universality half of Theorem 1.2 is in Sun (2020).
- `check/finite_range.py`: the one computation the proof uses (2468 cases, `n <= 779`);
  writes and re-verifies `finite_range_certificate.json`.
- `check/thmAB.c`: exhaustive test of Theorems 3.2 and 3.3 on every triple (`cc -O2 -o thmAB thmAB.c && ./thmAB 300000` passed).
- `check/all20.py`: brute-force test of the 20 tuples and their membership in Sun's list.
- `check/dfamily.py`: both directions of Theorem 1.2 for odd `d < 27`.
- `check/classnum.py`: the forms `<1,1,3>` and `<1,3,3>` are alone in their genus (p-neighbours).
- `check/primseed.py`: numerical check of Proposition 4.1.
- `check/e2e_algorithm.py`: runs the algorithm of the proof from an arbitrary first solution.
- `check/sun_tuples_407.json`: Sun's list, parsed from the appendix of arXiv:1502.03056.

## Lean formalization

`lean/TriPent.lean` (Lean `v4.33.1`, mathlib at the revision in `lean/lakefile.toml`):

    cd lean && lake exe cache get && lake env lean TriPent.lean

The last lines of output list the axioms of the twelve main statements: only `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide`. Proposition 4.1 of the paper is
not formalized; it enters as the hypotheses `PrimRep133` and `PrimRep113`. Formalized without
hypotheses: Theorems 3.2 and 3.3 (`exists_other_residue`, `exists_mixed`) and Lemma 4.2
(`seedS`, `seedT`). Formalized from the hypotheses: Theorems 1.1, 1.2 (universality), 1.4 and
Corollary 1.3, including the 2468 small cases, which the kernel checks from an explicit list.

## Classical input

Proposition 4.1 (primitive representation by `x^2+y^2+3z^2` and `x^2+3y^2+3z^2`) rests on the
local-global principle for a genus and on class number one. The references were checked on 2026-11-26 against
bibliographic records and against the way other papers cite the same places: the four journal
references; O'Meara 81:14, 92:2 and 102:5; Cassels p. 129 (representation by a genus, cited so
by Wu and Sun, arXiv:1710.08763) and Cassels Chapter 12 (Minkowski reduction). Not checked
against the book itself: that the bound `g11*g22*g33 <= 2D` for reduced ternary forms is stated
in Cassels Chapter 12 (the bound is classical; `check/classnum.py` confirms the class numbers
independently).

## Not covered

`T + p5 + p5` (same kind), `(3,7,1,1,1,1)`, `(3,1,3,-1,1,3)`, `T + T + p8`, and the original
target A254629: the method does not reach them. Scouting scripts are in `../A254629-scout/`.
