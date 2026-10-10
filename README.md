# Regular Morley tetrahedra from p-secting planes

Deep Bhattacharjee

Tran (*The converse problem for the Morley tetrahedron*, arXiv:2609.06553) replaced the trisecting planes of
the Morley construction for a tetrahedron ABCD by p-secting planes, with one parameter e, f, g > 1 for each
pair of opposite edges, and conjectured that a regular Morley tetrahedron M_{e,f,g}(ABCD) forces a pair of
opposite edges whose four cross edges are equal (his Conjecture 8.6, listed among his open problems).

The conjecture is false. The paper proves:

1. **Theorem 1.3.** Put an isosceles tetrahedron in its box, A = (a,b,c), B = (a,−b,−c), C = (−a,b,−c),
   D = (−a,−b,c). For all e, f, g > 1, M_{e,f,g}(ABCD) is regular exactly when its vertex A′ is not the
   centre O and lies on one of the four lines through O in the directions (±1,±1,±1); every such interior
   point is A′ for exactly one triple (e, f, g).
2. **Corollary 1.4.** When a, b, c are pairwise different the tetrahedron has three different edge lengths
   and no pair of opposite edges with four equal cross edges, yet M_{e,f,g}(ABCD) is regular for infinitely
   many triples. So Conjecture 8.6 fails.
3. **Examples 1.5 and 1.6.** Closed-form parameters for the boxes (1,2,3), with 2 < e, f, g < 4, and
   (4,2,1), with e = f = 4.
4. **Theorem 1.7.** For quadrisecting planes, e = f = g = 4, an isosceles tetrahedron has a regular Morley
   tetrahedron only if it is regular.

The proofs are by hand. The construction is written through the signed distances to the four faces
(Section 2), which turns each p-secting plane into a linear condition; the half-turns of an isosceles
tetrahedron then carry A′ to B′, C′ and D′, and regularity becomes a condition on A′ alone.

## Paper

`preprintMorley/` holds the LaTeX source and the TikZ figures; `dist/` holds the PDF (9 pages), a source zip
(figures as PNG) and an arXiv tarball (figures as PDF), rebuilt by `scripts/build_paper.sh`.
`PRIORITY-CHECK.md` records the check, on 10 October 2026, that the conjecture was still open.

## Checks

```
verification/lean/                     Lean 4 + Mathlib v4.34.1: every statement of the paper, no sorry;
                                       `Morley.tran_false : ¬ TranConjecture`; Check.lean audits all 477
                                       theorems (only propext, Classical.choice and Quot.sound)
verification/c/morley.c                long double, planes built from Definition 1.1: the examples, Lemma 2.4,
                                       Theorem 1.3(b) on random points of the four lines, Lemma 2.1
verification/cpp/exact.cpp             exact arithmetic in Q and Q(sqrt 105): Section 3, both examples, and
                                       the case analysis of Theorem 1.7 for all shapes 1 <= alpha, beta,
                                       gamma <= 60
verification/shell/check_examples.sh   bc at 60 digits: the closed-form parameters of both examples
verification/python/verify_morley.py   the construction straight from Definition 1.1 (no formula from
                                       Section 2): Lemmas 2.1, 2.2, 2.4, Proposition 2.3, Remark 2.5,
                                       Theorem 1.3, Corollary 1.4, Lemma 3.1, both examples
verification/julia/verify_morley.jl    256-bit BigFloat: the examples to 70 digits, Proposition 2.3,
                                       Theorem 1.3, Theorem 1.7 on a grid of shapes
scripts/run_all.sh                     runs all of the above; exit status 0 means every check passed
```

## Citation

See `CITATION.cff`. Zenodo archives each release with the paper and the checks: concept DOI
[10.5281/zenodo.23285911](https://doi.org/10.5281/zenodo.23285911) (all versions), version 1.0.0
[10.5281/zenodo.23285912](https://doi.org/10.5281/zenodo.23285912).

## License

MIT, see `LICENSE`.
