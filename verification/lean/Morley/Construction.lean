import Morley.Tetra

/-!
# Proposition 2.3, the coincidence remark, Remark 2.5 and Lemma 2.4

* `ptype X Y`: the class of the edge `F_X ∩ F_Y` among the three pairs of opposite edges;
  `0` is `AB, CD` (parameter `e`), `1` is `BC, AD` (`f`), `2` is `AC, BD` (`g`);
* `mset par X`: the common points of the three planes that define the vertex `X'`;
* `mv par X`: the vertex `X'` of `M_{e,f,g}(ABCD)`, with `par = ![e, f, g]`;
* `mset_eq` (Proposition 2.3): the three planes meet exactly in `mv par X`;
* `mv_interior`, `mv_surj`, `mv_inj` (Proposition 2.3): `par ↦ X'` is a bijection from
  `(1, ∞)³` onto the interior;
* `mv_eq_mv`: two vertices coincide only if a parameter equals `2`;
* `psect_swap` (Remark 2.5): the plane for `p` towards `F_U` is the plane for `p/(p−1)`
  towards `F_W`;
* `mv_iso` (Lemma 2.4): an isometry carrying one tetrahedron to another, with matching
  parameters, carries the Morley vertices along.
-/

open Real

namespace Morley
open V

/-- The class of the edge `F_X ∩ F_Y`, which is the class of the opposite edge `XY`. -/
def ptype (X Y : Fin 4) : Fin 3 :=
  if (X = 0 ∧ Y = 1) ∨ (X = 1 ∧ Y = 0) ∨ (X = 2 ∧ Y = 3) ∨ (X = 3 ∧ Y = 2) then 0
  else if (X = 1 ∧ Y = 2) ∨ (X = 2 ∧ Y = 1) ∨ (X = 0 ∧ Y = 3) ∨ (X = 3 ∧ Y = 0) then 1
  else 2

theorem ptype_symm : ∀ X Y : Fin 4, ptype X Y = ptype Y X := by decide

/-- The vertex `Y ≠ X` with `ptype X Y = i`. -/
def oth (X : Fin 4) (i : Fin 3) : Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![2, 3, 0, 1]] i X

theorem oth_ne : ∀ (X : Fin 4) (i : Fin 3), oth X i ≠ X := by decide
theorem ptype_oth : ∀ (X : Fin 4) (i : Fin 3), ptype X (oth X i) = i := by decide
theorem oth_ptype : ∀ X Y : Fin 4, Y ≠ X → oth X (ptype X Y) = Y := by decide

/-- The three edges of a face lie in different classes. -/
theorem ptype_adj : ∀ U Y Z : Fin 4, U ≠ Y → U ≠ Z → Y ≠ Z → ptype U Y ≠ ptype U Z := by
  decide

namespace Tet

variable (T : Tet) (par : Fin 3 → ℝ)

/-- `ρ X Y = R_p(θ)` for the plane through `F_X ∩ F_Y` towards `F_X`, and `ρ X X = 1`. -/
noncomputable def ρ (X Y : Fin 4) : ℝ := if Y = X then 1 else R (par (ptype X Y)) (T.θ X Y)

/-- The points on the three planes that define the vertex `X'`. -/
def mset (X : Fin 4) : Set V := {Q | ∀ Y, Y ≠ X → Q ∈ T.psect X Y (par (ptype X Y))}

/-- The barycentric weights of `X'`. -/
noncomputable def wt (X Z : Fin 4) : ℝ := T.ρ par X Z / T.h Z

noncomputable def wsum (X : Fin 4) : ℝ :=
  T.wt par X 0 + T.wt par X 1 + T.wt par X 2 + T.wt par X 3

/-- The vertex `X'` of `M_{e,f,g}(ABCD)`, `par = ![e, f, g]`. -/
noncomputable def mv (X : Fin 4) : V := T.comb (fun Z => T.wt par X Z / T.wsum par X)

variable {par}

theorem ρ_self (X : Fin 4) : T.ρ par X X = 1 := by simp [ρ]

theorem ρ_ne {X Y : Fin 4} (h : Y ≠ X) : T.ρ par X Y = R (par (ptype X Y)) (T.θ X Y) := by
  simp [ρ, h]

section
variable (hpar : ∀ i, 1 < par i)
include hpar

theorem ρ_pos (X Y : Fin 4) : 0 < T.ρ par X Y := by
  by_cases h : Y = X
  · rw [h, ρ_self]; norm_num
  · rw [T.ρ_ne h]
    exact R_pos (hpar _) (T.θ_pos X Y (Ne.symm h)) (T.θ_lt_pi X Y (Ne.symm h))

theorem wsum_pos (X : Fin 4) : 0 < T.wsum par X := by
  have := fun Z => div_pos (T.ρ_pos hpar X Z) (T.h_pos Z)
  simp only [wsum, wt]
  linarith [this 0, this 1, this 2, this 3]

/-- The distances of `X'` to the faces: `d_Z(X') = ρ X Z / wsum X`. -/
theorem d_mv (X Z : Fin 4) : T.d Z (T.mv par X) = T.ρ par X Z / T.wsum par X := by
  have hs := T.wsum_pos hpar X
  have hsum : (fun Z => T.wt par X Z / T.wsum par X) 0 +
      (fun Z => T.wt par X Z / T.wsum par X) 1 + (fun Z => T.wt par X Z / T.wsum par X) 2 +
      (fun Z => T.wt par X Z / T.wsum par X) 3 = 1 := by
    simp only
    rw [← add_div, ← add_div, ← add_div, div_eq_one_iff_eq (ne_of_gt hs)]
    rfl
  rw [mv, T.d_comb _ hsum]
  simp only [wt]
  have := T.h_pos Z
  field_simp

/-- Lemma 2.2 for the three planes of `X'`. -/
theorem mem_mset_iff (X : Fin 4) (Q : V) :
    Q ∈ T.mset par X ↔ ∀ Y, T.d Y Q = T.ρ par X Y * T.d X Q := by
  constructor
  · intro hQ Y
    by_cases hY : Y = X
    · rw [hY, ρ_self, one_mul]
    · have := hQ Y hY
      rw [T.psect_eq X Y (Ne.symm hY) _ (hpar _)] at this
      rw [T.ρ_ne hY]; exact this
  · intro hQ Y hY
    rw [T.psect_eq X Y (Ne.symm hY) _ (hpar _)]
    have := hQ Y
    rw [T.ρ_ne hY] at this
    exact this

/-- Proposition 2.3: the three planes meet in exactly one point, `X'`. -/
theorem mset_eq (X : Fin 4) : T.mset par X = {T.mv par X} := by
  ext Q
  rw [T.mem_mset_iff hpar, Set.mem_singleton_iff]
  constructor
  · intro hQ
    apply T.eq_of_d
    intro Z
    rw [T.d_mv hpar, hQ Z]
    have hb := (T.eq_comb_d Q).1
    rw [hQ 0, hQ 1, hQ 2, hQ 3] at hb
    have hs := T.wsum_pos hpar X
    have key : T.d X Q * T.wsum par X = 1 := by
      simp only [wsum, wt]
      linear_combination hb
    rw [eq_div_iff (ne_of_gt hs)]
    linear_combination T.ρ par X Z * key
  · rintro rfl Y
    rw [T.d_mv hpar, T.d_mv hpar, ρ_self]
    ring

theorem mv_mem (X : Fin 4) : T.mv par X ∈ T.mset par X := by
  rw [T.mset_eq hpar]; rfl

/-- Proposition 2.3: `X'` lies in the interior. -/
theorem mv_interior (X : Fin 4) : T.mv par X ∈ T.interior := by
  intro Z
  rw [T.d_mv hpar]
  exact div_pos (T.ρ_pos hpar X Z) (T.wsum_pos hpar X)

/-- The defining equations of `X'`. -/
theorem mv_eqs (X Y : Fin 4) : T.d Y (T.mv par X) = T.ρ par X Y * T.d X (T.mv par X) :=
  (T.mem_mset_iff hpar X _).1 (T.mv_mem hpar X) Y

/-- Two vertices of `M_{e,f,g}` coincide only if a parameter equals `2`. -/
theorem mv_eq_mv {X Y : Fin 4} (hXY : X ≠ Y) (h : T.mv par X = T.mv par Y) :
    par (ptype X Y) = 2 := by
  have m1 := T.mv_eqs hpar X Y
  have m2 := T.mv_eqs hpar Y X
  rw [← h] at m2
  rw [T.ρ_ne (Ne.symm hXY)] at m1
  rw [T.ρ_ne hXY, ptype_symm Y X, T.θ_symm Y X] at m2
  set r := R (par (ptype X Y)) (T.θ X Y) with hr
  have dY := (T.mv_interior hpar X) Y
  have hρ : 0 < r := R_pos (hpar _) (T.θ_pos X Y hXY) (T.θ_lt_pi X Y hXY)
  have h3 : T.d Y (T.mv par X) = r * r * T.d Y (T.mv par X) := by
    calc _ = r * T.d X (T.mv par X) := m1
      _ = r * (r * T.d Y (T.mv par X)) := by rw [← m2]
      _ = _ := by ring
  have h2 : r * r = 1 :=
    mul_right_cancel₀ (ne_of_gt dY) (h3.symm.trans (one_mul _).symm)
  have h1 : r = 1 := by nlinarith
  exact R_eq_one (hpar _) (T.θ_pos X Y hXY) (T.θ_lt_pi X Y hXY) h1

end

/-- Proposition 2.3: every interior point is `X'` for some parameters, namely those given by
`R_p(θ) = d_Y / d_X` (equation (2.4)). -/
theorem mv_surj (X : Fin 4) {Q : V} (hQ : Q ∈ T.interior) :
    ∃ par : Fin 3 → ℝ, (∀ i, 1 < par i) ∧ T.mv par X = Q := by
  let par : Fin 3 → ℝ := fun i => Rinv (T.d (oth X i) Q / T.d X Q) (T.θ X (oth X i))
  have hpar : ∀ i, 1 < par i := fun i =>
    Rinv_gt_one (div_pos (hQ _) (hQ _)) (T.θ_pos X _ (oth_ne X i).symm)
      (T.θ_lt_pi X _ (oth_ne X i).symm)
  refine ⟨par, hpar, ?_⟩
  have hmem : Q ∈ T.mset par X := by
    rw [T.mem_mset_iff hpar]
    intro Y
    by_cases hY : Y = X
    · rw [hY, ρ_self, one_mul]
    · rw [T.ρ_ne hY]
      have e := oth_ptype X Y hY
      have hR : R (par (ptype X Y)) (T.θ X Y) = T.d Y Q / T.d X Q := by
        simp only [par]
        rw [e]
        exact R_Rinv (div_pos (hQ Y) (hQ X)) (T.θ_pos X Y (Ne.symm hY))
          (T.θ_lt_pi X Y (Ne.symm hY))
      rw [hR, div_mul_cancel₀ _ (ne_of_gt (hQ X))]
  rw [T.mset_eq hpar] at hmem
  exact (Set.mem_singleton_iff.1 hmem).symm

/-- Proposition 2.3: the parameters are determined by `X'`. -/
theorem mv_inj (X : Fin 4) {par par' : Fin 3 → ℝ} (hpar : ∀ i, 1 < par i)
    (hpar' : ∀ i, 1 < par' i) (h : T.mv par X = T.mv par' X) : par = par' := by
  funext i
  have hY : oth X i ≠ X := oth_ne X i
  have ht : ptype X (oth X i) = i := ptype_oth X i
  have m1 := T.mv_eqs hpar X (oth X i)
  have m2 := T.mv_eqs hpar' X (oth X i)
  rw [← h] at m2
  have hd := (T.mv_interior hpar X) X
  rw [T.ρ_ne hY] at m1 m2
  have hR : R (par (ptype X (oth X i))) (T.θ X (oth X i)) =
      R (par' (ptype X (oth X i))) (T.θ X (oth X i)) :=
    mul_right_cancel₀ (ne_of_gt hd) (m1.symm.trans m2)
  have := R_injOn (T.θ_pos X _ (Ne.symm hY)) (T.θ_lt_pi X _ (Ne.symm hY)) (hpar _) (hpar' _) hR
  rwa [ht] at this

/-- Remark 2.5: the `p`-secting plane towards `F_U` is the `p/(p−1)`-secting plane towards
`F_W`. -/
theorem psect_swap (U W : Fin 4) (hUW : U ≠ W) {p : ℝ} (hp : 1 < p) :
    T.psect U W p = T.psect W U (p / (p - 1)) := by
  rw [T.psect_eq U W hUW p hp, T.psect_eq W U hUW.symm _ (conj_gt_one hp), T.θ_symm W U,
    R_conj hp]
  have hR := R_pos hp (T.θ_pos U W hUW) (T.θ_lt_pi U W hUW)
  ext Q
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h; rw [h]; field_simp
  · intro h; rw [h]; field_simp

/-- The inward unit normal is the unit vector orthogonal to the face with positive component
towards the opposite vertex. -/
theorem nrm_char (X : Fin 4) (m : V) (hm : dot m m = 1)
    (hface : ∀ Y, Y ≠ X → dot m (T.P Y - T.P (f0 X)) = 0)
    (hpos : 0 < dot m (T.P X - T.P (f0 X))) : T.nrm X = m := by
  have hc : cross (T.P (f1 X) - T.P (f0 X)) (T.P (f2 X) - T.P (f0 X)) ≠ 0 := T.cv_ne X
  apply unit_normal_unique hc (z := T.P X - T.P (f0 X))
  · rw [T.dot_nrm_sub, T.d_face X _ (f1_ne X), T.d_face X _ (f0_ne X)]; ring
  · rw [T.dot_nrm_sub, T.d_face X _ (f2_ne X), T.d_face X _ (f0_ne X)]; ring
  · exact hface _ (f1_ne X)
  · exact hface _ (f2_ne X)
  · exact T.nrm_unit X
  · exact hm
  · rw [T.dot_nrm_sub, T.d_face X _ (f0_ne X), sub_zero]; exact T.h_pos X
  · exact hpos

end Tet

/-! ### Isometries and Lemma 2.4 -/

/-- The isometry `Q ↦ L (Q − o) + o'`, where `L` has the orthonormal rows `r₁, r₂, r₃`. -/
structure Iso where
  r₁ : V
  r₂ : V
  r₃ : V
  o : V
  o' : V
  h11 : dot r₁ r₁ = 1
  h22 : dot r₂ r₂ = 1
  h33 : dot r₃ r₃ = 1
  h12 : dot r₁ r₂ = 0
  h13 : dot r₁ r₃ = 0
  h23 : dot r₂ r₃ = 0

namespace Iso

variable (g : Iso)

/-- The linear part. -/
def lin (v : V) : V := ⟨dot g.r₁ v, dot g.r₂ v, dot g.r₃ v⟩

/-- The isometry itself. -/
def app (Q : V) : V := g.lin (Q - g.o) + g.o'

theorem lin_dot (u v : V) : dot (g.lin u) (g.lin v) = dot u v := by
  have hu := frame_complete g.h11 g.h22 g.h33 g.h12 g.h13 g.h23 u
  conv_rhs => rw [hu]
  rw [dot_add_left, dot_add_left, dot_smul_left, dot_smul_left, dot_smul_left]
  simp only [lin]
  vexpand
  ring

theorem app_sub (Q Q' : V) : g.app Q - g.app Q' = g.lin (Q - Q') := by
  simp only [app, lin]; vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- An isometry preserves distances. -/
theorem dist2_app (Q Q' : V) : dist2 (g.app Q) (g.app Q') = dist2 Q Q' := by
  rw [dist2, dist2, V.sq, V.sq, app_sub, lin_dot]

end Iso

section iso

variable {T T' : Tet} {g : Iso} {σ : Fin 4 → Fin 4} (hσ : Function.Injective σ)
  (hP : ∀ X, g.app (T.P X) = T'.P (σ X))
include hσ hP

theorem nrm_iso (X : Fin 4) : T'.nrm (σ X) = g.lin (T.nrm X) := by
  have hsurj := Finite.surjective_of_injective hσ
  obtain ⟨Z, hZ⟩ := hsurj (f0 (σ X))
  have hZX : Z ≠ X := fun h => f0_ne (σ X) (by rw [← hZ, h])
  have key : ∀ Y, T'.P (σ Y) - T'.P (f0 (σ X)) = g.lin (T.P Y - T.P Z) := by
    intro Y
    rw [← hZ, ← hP, ← hP, g.app_sub]
  apply T'.nrm_char (σ X)
  · rw [g.lin_dot]; exact T.nrm_unit X
  · intro Y' hY'
    obtain ⟨Y, rfl⟩ := hsurj Y'
    have hYX : Y ≠ X := fun h => hY' (by rw [h])
    rw [key, g.lin_dot, T.dot_nrm_sub, T.d_face X Y hYX, T.d_face X Z hZX, sub_zero]
  · rw [key, g.lin_dot, T.dot_nrm_sub, T.d_face X Z hZX, sub_zero]
    exact T.h_pos X

/-- An isometry preserves the distances to corresponding faces. -/
theorem d_iso (X : Fin 4) (Q : V) : T'.d (σ X) (g.app Q) = T.d X Q := by
  have hne : σ (f0 X) ≠ σ X := fun h => f0_ne X (hσ h)
  rw [T'.d_eq (σ X) (σ (f0 X)) hne, ← hP, g.app_sub, nrm_iso hσ hP, g.lin_dot, Tet.d]

/-- An isometry preserves dihedral angles. -/
theorem θ_iso (U W : Fin 4) : T'.θ (σ U) (σ W) = T.θ U W := by
  rw [Tet.θ, Tet.θ, nrm_iso hσ hP, nrm_iso hσ hP, g.lin_dot]

/-- Lemma 2.4: if an isometry maps each vertex `X` of `T` to the vertex `σ X` of `T'`, and the
edge `σ Y σ Z` of `T'` carries the parameter of `YZ`, then it maps `X'` to `(σ X)'`. -/
theorem mv_iso {par par' : Fin 3 → ℝ} (hpar : ∀ i, 1 < par i) (hpar' : ∀ i, 1 < par' i)
    (hcompat : ∀ X Y, par' (ptype (σ X) (σ Y)) = par (ptype X Y)) (X : Fin 4) :
    g.app (T.mv par X) = T'.mv par' (σ X) := by
  have hmem : g.app (T.mv par X) ∈ T'.mset par' (σ X) := by
    rw [T'.mem_mset_iff hpar']
    intro Y'
    obtain ⟨Y, rfl⟩ := Finite.surjective_of_injective hσ Y'
    rw [d_iso hσ hP, d_iso hσ hP]
    have hρ : T'.ρ par' (σ X) (σ Y) = T.ρ par X Y := by
      by_cases hY : Y = X
      · subst hY; rw [Tet.ρ_self, Tet.ρ_self]
      · rw [T'.ρ_ne (fun h => hY (hσ h)), T.ρ_ne hY, hcompat, θ_iso hσ hP]
    rw [hρ]
    exact T.mv_eqs hpar X Y
  rw [T'.mset_eq hpar'] at hmem
  exact hmem

end iso

end Morley
