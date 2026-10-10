Regular Morley tetrahedra from p-secting planes, by Deep Bhattacharjee.

Tran conjectured that a regular Morley tetrahedron built from p-secting planes forces a pair of opposite edges with four equal cross edges (arXiv:2609.06553, Conjecture 8.6). This release disproves it: for an isosceles tetrahedron in its box, the Morley tetrahedron is regular exactly when one vertex lies on one of four lines through the centre, and every such point occurs, so every isosceles tetrahedron with three different edge lengths is a counterexample. For e = f = g = 4 only the regular tetrahedron remains.

Files:
- `morley-p-secting.pdf`: the paper, 9 pages.
- `morley-p-secting-tex.zip`: LaTeX source with the figures as PNG.
- `morley-p-secting-arxiv.tar.gz`: LaTeX source with the figures as PDF, ready for arXiv.

The repository at this tag also holds the dated priority check (`PRIORITY-CHECK.md`) and the checks in C, C++, Bash, Python, Julia and Lean 4 with Mathlib (every statement formalized, no sorry, `Morley.tran_false : ¬ TranConjecture`, 477 theorems within propext, Classical.choice and Quot.sound).
