import Morley

/-!
# Axiom audit

Every theorem of the library may use only `propext`, `Classical.choice` and `Quot.sound`.
The first command checks all of them; the `#print axioms` lines show the main results.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if (`Morley).isPrefixOf n && (match ci with | .thmInfo _ => true | _ => false) then
      acc.push n else acc
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array Name := #[]
  for n in names do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (fun a => !allowed.contains a) then bad := bad.push n
  if bad.isEmpty then
    logInfo m!"axiom audit: {names.size} theorems, all within propext, Classical.choice, Quot.sound"
  else
    logError m!"axiom audit failed for {bad}"

-- Lemma 2.1
#print axioms Morley.R_strictMonoOn
#print axioms Morley.R_surj
#print axioms Morley.R_gt_one_iff
-- Lemma 2.2
#print axioms Morley.Tet.psect_eq
-- Proposition 2.3 and the remark after it
#print axioms Morley.Tet.mset_eq
#print axioms Morley.Tet.mv_interior
#print axioms Morley.Tet.mv_surj
#print axioms Morley.Tet.mv_inj
#print axioms Morley.Tet.mv_eq_mv
-- Lemma 2.4 and Remark 2.5
#print axioms Morley.mv_iso
#print axioms Morley.Tet.psect_swap
-- Theorem 1.3
#print axioms Morley.theorem_1_3a
#print axioms Morley.theorem_1_3b
#print axioms Morley.theorem_1_3b_regular
-- Corollary 1.4
#print axioms Morley.tran_false
#print axioms Morley.box_no_cross
#print axioms Morley.box_three_lengths
#print axioms Morley.box_regular_infinite
-- Examples 1.5 and 1.6
#print axioms Morley.example_1_5
#print axioms Morley.example_1_6
-- Theorem 1.7 and the box form of isosceles tetrahedra
#print axioms Morley.box_form
#print axioms Morley.theorem_1_7_box
#print axioms Morley.theorem_1_7
