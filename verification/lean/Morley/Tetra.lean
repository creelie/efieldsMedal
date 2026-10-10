import Morley.Vec
import Morley.Trig

/-!
# Section 2: the construction for an arbitrary tetrahedron

* `Tet`: a nondegenerate tetrahedron `P 0 = A, P 1 = B, P 2 = C, P 3 = D`;
* `nrm X`: the inward unit normal of the face `F_X` opposite `X`; `d X Q` the signed distance
  from `Q` to the plane of `F_X`, positive on the side of `X`; `h X = d X (P X)` the height;
* barycentric coordinates: every point is `∑ (d X Q / h X) • P X` (`eq_comb_d`);
* `θ U W`: the interior dihedral angle at the edge `F_U ∩ F_W`, `cos θ = −n_U · n_W`;
* `psect U W p` (Definition 1.1): the plane through the edge `F_U ∩ F_W` containing the
  half-plane inside the dihedral angle that makes the angle `θ/p` with the face `F_U`;
* `psect_eq` (Lemma 2.2): `psect U W p = {Q | d W Q = R p θ * d U Q}`.
-/

open Real

namespace Morley
open V

/-- The face opposite `X` has the vertices `f0 X < f1 X < f2 X`. -/
def f0 (X : Fin 4) : Fin 4 := if X = 0 then 1 else 0
def f1 (X : Fin 4) : Fin 4 := if X = 0 ∨ X = 1 then 2 else 1
def f2 (X : Fin 4) : Fin 4 := if X = 3 then 2 else 3

theorem fin4_cases (X : Fin 4) : X = 0 ∨ X = 1 ∨ X = 2 ∨ X = 3 := by
  revert X; decide

theorem f0_ne : ∀ X : Fin 4, f0 X ≠ X := by decide
theorem f1_ne : ∀ X : Fin 4, f1 X ≠ X := by decide
theorem f2_ne : ∀ X : Fin 4, f2 X ≠ X := by decide
theorem face_cases : ∀ X Y : Fin 4, Y ≠ X → Y = f0 X ∨ Y = f1 X ∨ Y = f2 X := by decide

@[simp] theorem f0_0 : f0 0 = 1 := by decide
@[simp] theorem f0_1 : f0 1 = 0 := by decide
@[simp] theorem f0_2 : f0 2 = 0 := by decide
@[simp] theorem f0_3 : f0 3 = 0 := by decide
@[simp] theorem f1_0 : f1 0 = 2 := by decide
@[simp] theorem f1_1 : f1 1 = 2 := by decide
@[simp] theorem f1_2 : f1 2 = 1 := by decide
@[simp] theorem f1_3 : f1 3 = 1 := by decide
@[simp] theorem f2_0 : f2 0 = 3 := by decide
@[simp] theorem f2_1 : f2 1 = 3 := by decide
@[simp] theorem f2_2 : f2 2 = 3 := by decide
@[simp] theorem f2_3 : f2 3 = 2 := by decide

/-- The two endpoints of the edge `F_U ∩ F_W`: the vertices other than `U` and `W`. -/
def e0 (U W : Fin 4) : Fin 4 := if U ≠ 0 ∧ W ≠ 0 then 0 else if U ≠ 1 ∧ W ≠ 1 then 1 else 2
def e1 (U W : Fin 4) : Fin 4 := if U ≠ 3 ∧ W ≠ 3 then 3 else if U ≠ 2 ∧ W ≠ 2 then 2 else 1

theorem e_props : ∀ U W : Fin 4, U ≠ W →
    e0 U W ≠ U ∧ e0 U W ≠ W ∧ e1 U W ≠ U ∧ e1 U W ≠ W ∧ e0 U W ≠ e1 U W := by decide

theorem e_symm : ∀ U W : Fin 4, e0 U W = e0 W U ∧ e1 U W = e1 W U := by decide

/-- A nondegenerate tetrahedron `ABCD`, `P 0 = A`, `P 1 = B`, `P 2 = C`, `P 3 = D`. -/
structure Tet where
  P : Fin 4 → V
  nondeg : dot (P 1 - P 0) (cross (P 2 - P 0) (P 3 - P 0)) ≠ 0

/-- Vector identities used below. -/
theorem dot_sub_split (n Q a b : V) : dot n (Q - a) = dot n (Q - b) + dot n (b - a) := by
  vexpand; ring

theorem dot_sub_sub (n Q Q' a : V) : dot n (Q - a) - dot n (Q' - a) = dot n (Q - Q') := by
  vexpand; ring

theorem cross_cross_eq (u w : V) : cross u (cross u w) = dot u w • u - dot u u • w := by
  vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring

namespace Tet

variable (T : Tet)

/-- The triple product `(B − A) · ((C − A) × (D − A))`. -/
def det : ℝ := dot (T.P 1 - T.P 0) (cross (T.P 2 - T.P 0) (T.P 3 - T.P 0))

/-- A normal vector of the face opposite `X`. -/
def cv (X : Fin 4) : V := cross (T.P (f1 X) - T.P (f0 X)) (T.P (f2 X) - T.P (f0 X))

/-- `cv X · (X − f0 X)`, which is `± det`. -/
def side (X : Fin 4) : ℝ := dot (T.cv X) (T.P X - T.P (f0 X))

theorem side_eq (X : Fin 4) : T.side X = (if X = 0 ∨ X = 2 then -1 else 1) * T.det := by
  rcases fin4_cases X with rfl | rfl | rfl | rfl <;>
    simp only [side, cv, det, f0_0, f0_1, f0_2, f0_3, f1_0, f1_1, f1_2, f1_3, f2_0, f2_1, f2_2,
      f2_3] <;> norm_num <;> vexpand <;> ring

theorem side_ne (X : Fin 4) : T.side X ≠ 0 := by
  rw [side_eq]
  have := T.nondeg
  split_ifs <;> simp [det, this]

theorem cv_ne (X : Fin 4) : T.cv X ≠ 0 := by
  intro h
  apply T.side_ne X
  rw [side, h]; vexpand; ring

theorem cv_sq_pos (X : Fin 4) : 0 < dot (T.cv X) (T.cv X) := dot_self_pos (T.cv_ne X)

/-- The orientation sign making the normal point towards `X`. -/
noncomputable def sgn (X : Fin 4) : ℝ := if 0 < T.side X then 1 else -1

theorem sgn_sq (X : Fin 4) : T.sgn X * T.sgn X = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_side_pos (X : Fin 4) : 0 < T.sgn X * T.side X := by
  unfold sgn
  have := T.side_ne X
  split_ifs with h
  · linarith
  · push Not at h
    have : T.side X < 0 := lt_of_le_of_ne h this
    linarith

/-- The inward unit normal of the face opposite `X`. -/
noncomputable def nrm (X : Fin 4) : V :=
  (T.sgn X / Real.sqrt (dot (T.cv X) (T.cv X))) • T.cv X

/-- The signed distance from `Q` to the plane of the face opposite `X`. -/
noncomputable def d (X : Fin 4) (Q : V) : ℝ := dot (T.nrm X) (Q - T.P (f0 X))

/-- The height of `X` over the opposite face. -/
noncomputable def h (X : Fin 4) : ℝ := T.d X (T.P X)

theorem nrm_unit (X : Fin 4) : dot (T.nrm X) (T.nrm X) = 1 := by
  have hq := T.cv_sq_pos X
  have hs : Real.sqrt (dot (T.cv X) (T.cv X)) ^ 2 = dot (T.cv X) (T.cv X) :=
    Real.sq_sqrt (le_of_lt hq)
  have hs0 : Real.sqrt (dot (T.cv X) (T.cv X)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  rw [nrm, dot_smul_left, dot_smul_right]
  field_simp
  rw [hs]
  have := T.sgn_sq X
  nlinarith [this]

theorem cv_face (X Y : Fin 4) (hY : Y ≠ X) : dot (T.cv X) (T.P Y - T.P (f0 X)) = 0 := by
  rcases face_cases X Y hY with rfl | rfl | rfl
  · vexpand; ring
  · rw [cv, dot_comm]; exact dot_cross_left _ _
  · rw [cv, dot_comm]; exact dot_cross_right _ _

theorem d_face (X Y : Fin 4) (hY : Y ≠ X) : T.d X (T.P Y) = 0 := by
  rw [d, nrm, dot_smul_left, T.cv_face X Y hY, mul_zero]

theorem h_pos (X : Fin 4) : 0 < T.h X := by
  rw [h, d, nrm, dot_smul_left]
  have hq := T.cv_sq_pos X
  have := T.sgn_side_pos X
  rw [div_mul_eq_mul_div]
  apply div_pos _ (Real.sqrt_pos.2 hq)
  exact this

/-- The signed distance can be measured from any vertex of the face. -/
theorem d_eq (X Y : Fin 4) (hY : Y ≠ X) (Q : V) : T.d X Q = dot (T.nrm X) (Q - T.P Y) := by
  rw [d, dot_sub_split _ Q (T.P (f0 X)) (T.P Y)]
  have := T.d_face X Y hY
  rw [d] at this
  rw [this, add_zero]

theorem dot_nrm_sub (X : Fin 4) (Q Q' : V) : dot (T.nrm X) (Q - Q') = T.d X Q - T.d X Q' := by
  rw [d, d, dot_sub_sub]

theorem vertex_ne (Y Z : Fin 4) (hYZ : Y ≠ Z) : T.P Y ≠ T.P Z := by
  intro he
  have h1 := T.h_pos Z
  rw [h, ← he, T.d_face Z Y hYZ] at h1
  exact lt_irrefl _ h1

/-! ### Barycentric coordinates -/

/-- The affine combination `∑ μ X • P X`. -/
def comb (μ : Fin 4 → ℝ) : V := μ 0 • T.P 0 + μ 1 • T.P 1 + μ 2 • T.P 2 + μ 3 • T.P 3

theorem d_comb (μ : Fin 4 → ℝ) (hμ : μ 0 + μ 1 + μ 2 + μ 3 = 1) (X : Fin 4) :
    T.d X (T.comb μ) = μ X * T.h X := by
  have expand : T.d X (T.comb μ) = μ 0 * T.d X (T.P 0) + μ 1 * T.d X (T.P 1) +
      μ 2 * T.d X (T.P 2) + μ 3 * T.d X (T.P 3) := by
    simp only [d, comb]
    vexpand
    linear_combination ((T.nrm X).x * (T.P (f0 X)).x + (T.nrm X).y * (T.P (f0 X)).y
      + (T.nrm X).z * (T.P (f0 X)).z) * hμ
  rw [expand]
  rcases fin4_cases X with rfl | rfl | rfl | rfl
  · rw [T.d_face 0 1 (by decide), T.d_face 0 2 (by decide), T.d_face 0 3 (by decide), h]; ring
  · rw [T.d_face 1 0 (by decide), T.d_face 1 2 (by decide), T.d_face 1 3 (by decide), h]; ring
  · rw [T.d_face 2 0 (by decide), T.d_face 2 1 (by decide), T.d_face 2 3 (by decide), h]; ring
  · rw [T.d_face 3 0 (by decide), T.d_face 3 1 (by decide), T.d_face 3 2 (by decide), h]; ring

/-- Every point is an affine combination of the vertices (Cramer's rule). -/
theorem exists_comb (Q : V) : ∃ μ : Fin 4 → ℝ, μ 0 + μ 1 + μ 2 + μ 3 = 1 ∧ Q = T.comb μ := by
  have hD := T.nondeg
  have key : ∀ q a b c : V, dot a (cross b c) • q =
      dot q (cross b c) • a + dot a (cross q c) • b + dot a (cross b q) • c := by
    intro q a b c; vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring
  have k := key (Q - T.P 0) (T.P 1 - T.P 0) (T.P 2 - T.P 0) (T.P 3 - T.P 0)
  set D := dot (T.P 1 - T.P 0) (cross (T.P 2 - T.P 0) (T.P 3 - T.P 0)) with hDdef
  have kx := congrArg V.x k
  have ky := congrArg V.y k
  have kz := congrArg V.z k
  set m1 := dot (Q - T.P 0) (cross (T.P 2 - T.P 0) (T.P 3 - T.P 0)) with hm1
  set m2 := dot (T.P 1 - T.P 0) (cross (Q - T.P 0) (T.P 3 - T.P 0)) with hm2
  set m3 := dot (T.P 1 - T.P 0) (cross (T.P 2 - T.P 0) (Q - T.P 0)) with hm3
  simp only [V.smul_x, V.smul_y, V.smul_z, V.add_x, V.add_y, V.add_z, V.sub_x, V.sub_y,
    V.sub_z] at kx ky kz
  refine ⟨![1 - m1 / D - m2 / D - m3 / D, m1 / D, m2 / D, m3 / D], by simp; ring, ?_⟩
  simp only [comb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ext
  · simp only [V.smul_x, V.add_x]; field_simp; linear_combination kx
  · simp only [V.smul_y, V.add_y]; field_simp; linear_combination ky
  · simp only [V.smul_z, V.add_z]; field_simp; linear_combination kz

/-- Barycentric coordinates: `Q = ∑ (d X Q / h X) • P X`, and the coefficients sum to 1. -/
theorem eq_comb_d (Q : V) :
    (T.d 0 Q / T.h 0 + T.d 1 Q / T.h 1 + T.d 2 Q / T.h 2 + T.d 3 Q / T.h 3 = 1) ∧
      Q = T.comb (fun X => T.d X Q / T.h X) := by
  obtain ⟨μ, hμ, hQ⟩ := T.exists_comb Q
  have key : ∀ X, T.d X Q / T.h X = μ X := by
    intro X
    rw [hQ, T.d_comb μ hμ X, mul_div_assoc, div_self (ne_of_gt (T.h_pos X)), mul_one]
  have hf : (fun X => T.d X Q / T.h X) = μ := funext key
  rw [hf]
  exact ⟨by rw [key 0, key 1, key 2, key 3]; exact hμ, hQ⟩

/-- A point is determined by its four distances. -/
theorem eq_of_d {Q Q' : V} (h : ∀ X, T.d X Q = T.d X Q') : Q = Q' := by
  rw [(T.eq_comb_d Q).2, (T.eq_comb_d Q').2]
  simp only [h]

/-- The interior: all four signed distances positive. -/
def interior : Set V := {Q | ∀ X, 0 < T.d X Q}

/-! ### Dihedral angles -/

/-- The interior dihedral angle at the edge `F_U ∩ F_W`. -/
noncomputable def θ (U W : Fin 4) : ℝ := Real.arccos (-(dot (T.nrm U) (T.nrm W)))

theorem θ_symm (U W : Fin 4) : T.θ U W = T.θ W U := by rw [θ, θ, dot_comm]

theorem nn_sq_lt_one (U W : Fin 4) (hUW : U ≠ W) :
    dot (T.nrm U) (T.nrm W) * dot (T.nrm U) (T.nrm W) < 1 := by
  by_contra hge
  push Not at hge
  have hl := lagrange (T.nrm U) (T.nrm W)
  rw [T.nrm_unit U, T.nrm_unit W] at hl
  have hc0 : cross (T.nrm U) (T.nrm W) = 0 := by
    apply dot_self_eq_zero
    have := dot_self_nonneg (cross (T.nrm U) (T.nrm W))
    linarith
  have hcc := cross_cross_eq (T.nrm U) (T.nrm W)
  rw [hc0, T.nrm_unit U] at hcc
  -- n_W = (n_U · n_W) n_U
  have hW : T.nrm W = dot (T.nrm U) (T.nrm W) • T.nrm U := by
    have hx := congrArg V.x hcc
    have hy := congrArg V.y hcc
    have hz := congrArg V.z hcc
    ext
    · vexpand at hx ⊢; linear_combination hx
    · vexpand at hy ⊢; linear_combination hy
    · vexpand at hz ⊢; linear_combination hz
  obtain ⟨h1, h2, -, -, -⟩ := e_props U W hUW
  have hhW := T.h_pos W
  rw [h, T.d_eq W (e0 U W) h2, hW, dot_smul_left, ← T.d_eq U (e0 U W) h1,
    T.d_face U W hUW.symm] at hhW
  simp at hhW

theorem cos_θ (U W : Fin 4) (hUW : U ≠ W) : Real.cos (T.θ U W) = -(dot (T.nrm U) (T.nrm W)) := by
  have := T.nn_sq_lt_one U W hUW
  rw [θ, Real.cos_arccos] <;> nlinarith

theorem θ_pos (U W : Fin 4) (hUW : U ≠ W) : 0 < T.θ U W := by
  have := T.nn_sq_lt_one U W hUW
  rw [θ, Real.arccos_pos]; nlinarith

theorem θ_lt_pi (U W : Fin 4) (hUW : U ≠ W) : T.θ U W < π := by
  have := T.nn_sq_lt_one U W hUW
  rw [θ, Real.arccos_lt_pi]; nlinarith

theorem sin_θ (U W : Fin 4) (hUW : U ≠ W) :
    Real.sin (T.θ U W) = Real.sqrt (1 - dot (T.nrm U) (T.nrm W) * dot (T.nrm U) (T.nrm W)) := by
  rw [θ, Real.sin_arccos]; ring_nf

/-! ### Definition 1.1 and Lemma 2.2 -/

/-- The edge vector of `F_U ∩ F_W`. -/
def tv (U W : Fin 4) : V := T.P (e1 U W) - T.P (e0 U W)

/-- From the edge to the third vertex `W` of the face `F_U`. -/
def wv (U W : Fin 4) : V := T.P W - T.P (e0 U W)

/-- The component of `wv` orthogonal to the edge. -/
noncomputable def v0 (U W : Fin 4) : V :=
  T.wv U W - (dot (T.wv U W) (T.tv U W) / dot (T.tv U W) (T.tv U W)) • T.tv U W

/-- The unit vector in the face `F_U`, orthogonal to the edge, pointing into the face. -/
noncomputable def vu (U W : Fin 4) : V := (1 / Real.sqrt (dot (T.v0 U W) (T.v0 U W))) • T.v0 U W

/-- Definition 1.1: the `p`-secting plane of the edge `F_U ∩ F_W` towards the face `F_U`.  It is
the plane through the edge spanned by the edge and the direction `cos φ • vu + sin φ • n_U`,
`φ = θ/p`: the half-plane `r > 0` lies inside the dihedral angle and makes the angle `θ/p`
with the half-face of `F_U` (and `θ − θ/p` with that of `F_W`). -/
noncomputable def psect (U W : Fin 4) (p : ℝ) : Set V :=
  {Q | ∃ s r : ℝ, Q = T.P (e0 U W) + s • T.tv U W +
    r • (Real.cos (T.θ U W / p) • T.vu U W + Real.sin (T.θ U W / p) • T.nrm U)}

/-- The unit edge vector. -/
noncomputable def te (U W : Fin 4) : V := (1 / Real.sqrt (dot (T.tv U W) (T.tv U W))) • T.tv U W

section frame
variable {U W : Fin 4} (hUW : U ≠ W)
include hUW

theorem tv_ne : T.tv U W ≠ 0 := by
  obtain ⟨-, -, -, -, h5⟩ := e_props U W hUW
  intro h0
  apply T.vertex_ne _ _ h5.symm
  have := congrArg V.x h0; have := congrArg V.y h0; have := congrArg V.z h0
  simp only [tv] at *
  ext <;> vexpand at * <;> linarith

theorem nrmU_tv : dot (T.nrm U) (T.tv U W) = 0 := by
  obtain ⟨h1, -, h3, -, -⟩ := e_props U W hUW
  rw [tv, T.dot_nrm_sub, T.d_face U _ h3, T.d_face U _ h1]; ring

theorem nrmW_tv : dot (T.nrm W) (T.tv U W) = 0 := by
  obtain ⟨-, h2, -, h4, -⟩ := e_props U W hUW
  rw [tv, T.dot_nrm_sub, T.d_face W _ h4, T.d_face W _ h2]; ring

theorem nrmU_wv : dot (T.nrm U) (T.wv U W) = 0 := by
  obtain ⟨h1, -, -, -, -⟩ := e_props U W hUW
  rw [wv, T.dot_nrm_sub, T.d_face U _ hUW.symm, T.d_face U _ h1]; ring

theorem nrmW_wv : dot (T.nrm W) (T.wv U W) = T.h W := by
  obtain ⟨-, h2, -, -, -⟩ := e_props U W hUW
  rw [wv, T.dot_nrm_sub, T.d_face W _ h2, h]; ring

theorem v0_tv : dot (T.v0 U W) (T.tv U W) = 0 := by
  have ht := dot_self_pos (T.tv_ne hUW)
  rw [v0, dot_sub_left, dot_smul_left]
  field_simp
  ring

theorem nrmU_v0 : dot (T.nrm U) (T.v0 U W) = 0 := by
  rw [v0, dot_sub_right, dot_smul_right, T.nrmU_wv hUW, T.nrmU_tv hUW]; ring

theorem nrmW_v0 : dot (T.nrm W) (T.v0 U W) = T.h W := by
  rw [v0, dot_sub_right, dot_smul_right, T.nrmW_wv hUW, T.nrmW_tv hUW]; ring

theorem v0_ne : T.v0 U W ≠ 0 := by
  intro h0
  have := T.nrmW_v0 hUW
  rw [h0, dot_zero_right] at this
  linarith [T.h_pos W]

theorem vu_unit : dot (T.vu U W) (T.vu U W) = 1 := by
  have hq := dot_self_pos (T.v0_ne hUW)
  have hs : Real.sqrt (dot (T.v0 U W) (T.v0 U W)) ^ 2 = dot (T.v0 U W) (T.v0 U W) :=
    Real.sq_sqrt (le_of_lt hq)
  rw [vu, dot_smul_left, dot_smul_right]
  field_simp
  rw [hs]

theorem vu_tv : dot (T.vu U W) (T.tv U W) = 0 := by
  rw [vu, dot_smul_left, T.v0_tv hUW, mul_zero]

theorem nrmU_vu : dot (T.nrm U) (T.vu U W) = 0 := by
  rw [vu, dot_smul_right, T.nrmU_v0 hUW, mul_zero]

theorem nrmW_vu_pos : 0 < dot (T.nrm W) (T.vu U W) := by
  have hq := dot_self_pos (T.v0_ne hUW)
  rw [vu, dot_smul_right, T.nrmW_v0 hUW]
  exact mul_pos (one_div_pos.2 (Real.sqrt_pos.2 hq)) (T.h_pos W)

theorem te_unit : dot (T.te U W) (T.te U W) = 1 := by
  have hq := dot_self_pos (T.tv_ne hUW)
  have hs : Real.sqrt (dot (T.tv U W) (T.tv U W)) ^ 2 = dot (T.tv U W) (T.tv U W) :=
    Real.sq_sqrt (le_of_lt hq)
  rw [te, dot_smul_left, dot_smul_right]
  field_simp
  rw [hs]

theorem te_vu : dot (T.te U W) (T.vu U W) = 0 := by
  rw [te, dot_smul_left, dot_comm (T.tv U W) (T.vu U W), T.vu_tv hUW, mul_zero]

theorem te_nrmU : dot (T.te U W) (T.nrm U) = 0 := by
  rw [te, dot_smul_left, dot_comm (T.tv U W) (T.nrm U), T.nrmU_tv hUW, mul_zero]

theorem frame (w : V) :
    w = dot w (T.te U W) • T.te U W + dot w (T.vu U W) • T.vu U W + dot w (T.nrm U) • T.nrm U :=
  frame_complete (T.te_unit hUW) (T.vu_unit hUW) (T.nrm_unit U) (T.te_vu hUW) (T.te_nrmU hUW)
    (by rw [dot_comm]; exact T.nrmU_vu hUW) w

theorem parseval (w : V) :
    dot w w = dot w (T.te U W) * dot w (T.te U W) + dot w (T.vu U W) * dot w (T.vu U W) +
      dot w (T.nrm U) * dot w (T.nrm U) := by
  conv_lhs => arg 2; rw [T.frame hUW w]
  rw [dot_add_right, dot_add_right, dot_smul_right, dot_smul_right, dot_smul_right]

/-- The components of `n_W` in the frame: `n_W = sin θ • vu − cos θ • n_U`. -/
theorem nrmW_comp :
    dot (T.nrm W) (T.vu U W) = Real.sin (T.θ U W) ∧
      dot (T.nrm W) (T.nrm U) = -Real.cos (T.θ U W) ∧ dot (T.nrm W) (T.te U W) = 0 := by
  have ht : dot (T.nrm W) (T.te U W) = 0 := by
    rw [te, dot_smul_right, T.nrmW_tv hUW, mul_zero]
  have hc : dot (T.nrm W) (T.nrm U) = -Real.cos (T.θ U W) := by
    rw [T.cos_θ U W hUW, dot_comm]; ring
  refine ⟨?_, hc, ht⟩
  have hp := T.parseval hUW (T.nrm W)
  rw [T.nrm_unit W, ht, dot_comm (T.nrm W) (T.nrm U)] at hp
  rw [T.sin_θ U W hUW]
  have hpos := T.nrmW_vu_pos hUW
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos hpos]
  linarith

end frame

/-- Lemma 2.2: the `p`-secting plane of the edge `F_U ∩ F_W` towards `F_U` is the set where
`d_W = R_p(θ) d_U`. -/
theorem psect_eq (U W : Fin 4) (hUW : U ≠ W) (p : ℝ) (hp : 1 < p) :
    T.psect U W p = {Q | T.d W Q = R p (T.θ U W) * T.d U Q} := by
  obtain ⟨h1, h2, -, -, -⟩ := e_props U W hUW
  set θ := T.θ U W with hθ
  set φ := θ / p with hφ
  have h0 := T.θ_pos U W hUW
  have hπ := T.θ_lt_pi U W hUW
  have sθ : 0 < Real.sin θ := sin_theta_pos h0 hπ
  have sφ : 0 < Real.sin φ := sin_phi_pos hp h0 hπ
  have sφ0 : Real.sin φ ≠ 0 := ne_of_gt sφ
  obtain ⟨cW1, cW2, cW3⟩ := T.nrmW_comp hUW
  rw [← hθ] at cW1 cW2
  have hR : R p θ = Real.sin (θ - φ) / Real.sin φ := R_eq_sub hp
  have sub : Real.sin (θ - φ) = Real.sin θ * Real.cos φ - Real.cos θ * Real.sin φ :=
    Real.sin_sub θ φ
  ext Q
  simp only [psect, Set.mem_ofPred_eq]
  -- distances in terms of w = Q − P(e0)
  have dU : T.d U Q = dot (T.nrm U) (Q - T.P (e0 U W)) := T.d_eq U _ h1 Q
  have dW : T.d W Q = dot (T.nrm W) (Q - T.P (e0 U W)) := T.d_eq W _ h2 Q
  constructor
  · rintro ⟨s, r, rfl⟩
    have hw : T.P (e0 U W) + s • T.tv U W + r • (Real.cos φ • T.vu U W + Real.sin φ • T.nrm U)
        - T.P (e0 U W) = s • T.tv U W + r • (Real.cos φ • T.vu U W + Real.sin φ • T.nrm U) := by
      vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring
    rw [dU, dW, hw]
    simp only [dot_add_right, dot_smul_right]
    rw [T.nrmU_tv hUW, T.nrmW_tv hUW, T.nrmU_vu hUW, T.nrm_unit U, cW1,
      cW2, hR, sub]
    field_simp
    ring
  · intro hQ
    set w := Q - T.P (e0 U W) with hwdef
    set a := dot w (T.te U W)
    set x := dot w (T.vu U W)
    set y := dot w (T.nrm U)
    have hfr := T.frame hUW w
    have hdU : T.d U Q = y := by rw [dU, dot_comm]
    have hdW : T.d W Q = x * Real.sin θ - y * Real.cos θ := by
      rw [dW]
      conv_lhs => rw [hfr]
      simp only [dot_add_right, dot_smul_right]
      rw [cW3, cW1, cW2]; ring
    rw [hdU, hdW, hR, sub] at hQ
    -- x sin φ = y cos φ
    have key : x * Real.sin φ = y * Real.cos φ := by
      rw [div_mul_eq_mul_div, eq_div_iff sφ0] at hQ
      have : Real.sin θ * (x * Real.sin φ - y * Real.cos φ) = 0 := by linear_combination hQ
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    have pyth := Real.sin_sq_add_cos_sq φ
    refine ⟨a / Real.sqrt (dot (T.tv U W) (T.tv U W)), x * Real.cos φ + y * Real.sin φ, ?_⟩
    have hxr : x = (x * Real.cos φ + y * Real.sin φ) * Real.cos φ := by
      linear_combination (-x) * pyth + Real.sin φ * key
    have hyr : y = (x * Real.cos φ + y * Real.sin φ) * Real.sin φ := by
      linear_combination (-y) * pyth - Real.cos φ * key
    have hQw : Q = T.P (e0 U W) + w := by rw [hwdef]; vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring
    have hfr' : w = a • T.te U W + x • T.vu U W + y • T.nrm U := hfr
    rw [hQw, hfr']
    simp only [te]
    vexpand
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (T.vu U W).x * hxr + (T.nrm U).x * hyr
    · linear_combination (T.vu U W).y * hxr + (T.nrm U).y * hyr
    · linear_combination (T.vu U W).z * hxr + (T.nrm U).z * hyr

end Tet

end Morley
