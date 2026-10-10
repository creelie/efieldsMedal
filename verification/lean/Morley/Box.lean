import Morley.Construction

/-!
# Section 3: the isosceles tetrahedron in its box

* `box a b c`: the tetrahedron (1.1), `A = (a,b,c)`, `B = (a,−b,−c)`, `C = (−a,b,−c)`,
  `D = (−a,−b,c)`; `sx, sy, sz` are the signs of the vertices;
* `d_box`: `d_X = L_X / N`, with `L_X = 1 ± αx ± βy ± γz`, `α = 1/a`, `β = 1/b`, `γ = 1/c`;
* `htIso k`: the half-turns about the coordinate axes; they permute the vertices by the Klein
  group (`kl k`) and preserve the parameter classes;
* `theorem_1_3a`, `theorem_1_3b`: Theorem 1.3;
* `TranConjecture` (Conjecture 1.2), `box_no_cross`, `box_regular_infinite`
  (Corollary 1.4).  The disproof `tran_false` is in `Morley.Examples`, from Example 1.5.
-/

open Real

namespace Morley
open V

/-- The signs of the four vertices (and the directions of the lines `ℓ₁, …, ℓ₄`). -/
def sx : Fin 4 → ℝ := ![1, 1, -1, -1]
def sy : Fin 4 → ℝ := ![1, -1, 1, -1]
def sz : Fin 4 → ℝ := ![1, -1, -1, 1]

theorem sx_sq (X : Fin 4) : sx X * sx X = 1 := by fin_cases X <;> norm_num [sx]
theorem sy_sq (X : Fin 4) : sy X * sy X = 1 := by fin_cases X <;> norm_num [sy]
theorem sz_sq (X : Fin 4) : sz X * sz X = 1 := by fin_cases X <;> norm_num [sz]

/-- `1 + s_X · s_Y` is `4` for `Y = X` and `0` otherwise. -/
theorem sgn_dot (X Y : Fin 4) :
    1 + sx X * sx Y + sy X * sy Y + sz X * sz Y = if Y = X then 4 else 0 := by
  fin_cases X <;> fin_cases Y <;> norm_num [sx, sy, sz]

/-- The direction `δ_k` of the line `ℓ_{k+1}`. -/
def dir (k : Fin 4) : V := ⟨sx k, sy k, sz k⟩

/-- The point `Q` lies on `ℓ₁ ∪ ℓ₂ ∪ ℓ₃ ∪ ℓ₄`. -/
def onLines (Q : V) : Prop := ∃ k : Fin 4, ∃ t : ℝ, Q = t • dir k

theorem onLines_iff (Q : V) : onLines Q ↔ Q.x ^ 2 = Q.y ^ 2 ∧ Q.y ^ 2 = Q.z ^ 2 := by
  constructor
  · rintro ⟨k, t, rfl⟩
    simp only [dir, V.smul_x, V.smul_y, V.smul_z]
    fin_cases k <;> norm_num [sx, sy, sz]
  · rintro ⟨h1, h2⟩
    rcases on_lines Q.x Q.y Q.z h1 h2 with ⟨hy, hz⟩ | ⟨hy, hz⟩ | ⟨hy, hz⟩ | ⟨hy, hz⟩
    · exact ⟨0, Q.x, by ext <;> simp [dir, sx, sy, sz, hy, hz]⟩
    · exact ⟨1, Q.x, by ext <;> simp [dir, sx, sy, sz, hy, hz]⟩
    · exact ⟨3, -Q.x, by ext <;> simp [dir, sx, sy, sz, hy, hz]⟩
    · exact ⟨2, -Q.x, by ext <;> simp [dir, sx, sy, sz, hy, hz]⟩

/-- Four points form a regular tetrahedron: the six distances are equal and positive. -/
def Regular (Q : Fin 4 → V) : Prop :=
  0 < dist2 (Q 0) (Q 1) ∧ ∀ i j : Fin 4, i ≠ j → dist2 (Q i) (Q j) = dist2 (Q 0) (Q 1)

/-- The four points `(±x, ±y, ±z)` with the vertex signs: their squared distances are
`4(y²+z²)`, `4(x²+z²)`, `4(x²+y²)`. -/
theorem regular_signs (x y z : ℝ) :
    Regular (fun k => (⟨sx k * x, sy k * y, sz k * z⟩ : V)) ↔
      ((⟨x, y, z⟩ : V) ≠ 0 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) := by
  have e : ∀ k l : Fin 4,
      dist2 (⟨sx k * x, sy k * y, sz k * z⟩ : V) ⟨sx l * x, sy l * y, sz l * z⟩ =
        (sx k - sx l) ^ 2 * x ^ 2 + (sy k - sy l) ^ 2 * y ^ 2 + (sz k - sz l) ^ 2 * z ^ 2 := by
    intro k l
    simp only [dist2, V.sq, dot, V.sub_x, V.sub_y, V.sub_z, V.mk_x, V.mk_y, V.mk_z]
    ring
  have hne : (⟨x, y, z⟩ : V) ≠ 0 ↔ 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    constructor
    · intro h
      by_contra hle
      apply h
      have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
      ext <;> simp [hx, hy, hz]
    · intro h h0
      have hx := congrArg V.x h0
      have hy := congrArg V.y h0
      have hz := congrArg V.z h0
      simp only [V.mk_x, V.mk_y, V.mk_z, V.zero_x, V.zero_y, V.zero_z] at hx hy hz
      rw [hx, hy, hz] at h
      norm_num at h
  simp only [Regular, e]
  rw [hne]
  constructor
  · rintro ⟨h0, h⟩
    have h02 := h 0 2 (by decide)
    have h03 := h 0 3 (by decide)
    norm_num [sx, sy, sz] at h0 h02 h03
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by norm_num [sx, sy, sz]; nlinarith, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | (norm_num [sx, sy, sz] <;> nlinarith)

/-- The vertices (1.1). -/
def boxP (a b c : ℝ) (X : Fin 4) : V := ⟨sx X * a, sy X * b, sz X * c⟩

theorem box_det (a b c : ℝ) :
    dot (boxP a b c 1 - boxP a b c 0)
      (cross (boxP a b c 2 - boxP a b c 0) (boxP a b c 3 - boxP a b c 0)) = -16 * (a * b * c) := by
  simp [boxP, sx, sy, sz, dot, cross]
  ring

/-- The isosceles tetrahedron (1.1). -/
def box (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : Tet :=
  ⟨boxP a b c, by rw [box_det]; exact ne_of_lt (by nlinarith [mul_pos (mul_pos ha hb) hc])⟩

/-- `N = (α² + β² + γ²)^{1/2}`. -/
noncomputable def Nb (a b c : ℝ) : ℝ := Real.sqrt (a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2)

/-- `L_X(Q) = 1 ± αx ± βy ± γz`. -/
noncomputable def Lf (a b c : ℝ) (X : Fin 4) (Q : V) : ℝ :=
  1 + sx X * a⁻¹ * Q.x + sy X * b⁻¹ * Q.y + sz X * c⁻¹ * Q.z

/-- The inward unit normal `(±α, ±β, ±γ)/N`. -/
noncomputable def mvec (a b c : ℝ) (X : Fin 4) : V :=
  (Nb a b c)⁻¹ • (⟨sx X * a⁻¹, sy X * b⁻¹, sz X * c⁻¹⟩ : V)

theorem dot_mvec (a b c : ℝ) (X : Fin 4) (Q Q' : V) :
    dot (mvec a b c X) (Q - Q') = (Lf a b c X Q - Lf a b c X Q') / Nb a b c := by
  simp only [mvec, Lf]; vexpand; ring

section
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
include ha hb hc

theorem Nb_pos : 0 < Nb a b c := Real.sqrt_pos.2 (by positivity)

theorem Nb_sq : Nb a b c ^ 2 = a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2 := Real.sq_sqrt (by positivity)

theorem Lf_boxP (X Y : Fin 4) : Lf a b c X (boxP a b c Y) = if Y = X then 4 else 0 := by
  rw [← sgn_dot]
  simp only [Lf, boxP]
  field_simp

theorem mvec_unit (X : Fin 4) : dot (mvec a b c X) (mvec a b c X) = 1 := by
  have hN := Nb_sq ha hb hc
  have hinv : (Nb a b c)⁻¹ * Nb a b c = 1 := inv_mul_cancel₀ (ne_of_gt (Nb_pos ha hb hc))
  simp only [mvec]
  vexpand
  linear_combination ((Nb a b c)⁻¹ ^ 2 * a⁻¹ ^ 2) * sx_sq X +
    ((Nb a b c)⁻¹ ^ 2 * b⁻¹ ^ 2) * sy_sq X + ((Nb a b c)⁻¹ ^ 2 * c⁻¹ ^ 2) * sz_sq X -
    (Nb a b c)⁻¹ ^ 2 * hN + ((Nb a b c)⁻¹ * Nb a b c + 1) * hinv

theorem box_P : (box a b c ha hb hc).P = boxP a b c := rfl

/-- The inward normals of the box tetrahedron. -/
theorem nrm_box (X : Fin 4) : (box a b c ha hb hc).nrm X = mvec a b c X := by
  apply Tet.nrm_char _ X _ (mvec_unit ha hb hc X)
  · intro Y hY
    rw [box_P, dot_mvec, Lf_boxP ha hb hc, Lf_boxP ha hb hc, if_neg hY, if_neg (f0_ne X)]
    simp
  · rw [box_P, dot_mvec, Lf_boxP ha hb hc, Lf_boxP ha hb hc, if_pos rfl, if_neg (f0_ne X)]
    exact div_pos (by norm_num) (Nb_pos ha hb hc)

/-- `d_X = L_X / N`. -/
theorem d_box (X : Fin 4) (Q : V) : (box a b c ha hb hc).d X Q = Lf a b c X Q / Nb a b c := by
  rw [Tet.d, nrm_box ha hb hc, box_P, dot_mvec, Lf_boxP ha hb hc, if_neg (f0_ne X), sub_zero]

theorem interior_box (Q : V) : Q ∈ (box a b c ha hb hc).interior ↔ ∀ X, 0 < Lf a b c X Q := by
  have hN := Nb_pos ha hb hc
  constructor
  · intro h X
    have := h X
    rw [d_box ha hb hc] at this
    exact (div_pos_iff_of_pos_right hN).1 this
  · intro h X
    rw [d_box ha hb hc]
    exact div_pos (h X) hN

/-- The cosines (3.1) of the dihedral angles: `cos θ = −n_X · n_Y`. -/
theorem dot_mvec_mvec (X Y : Fin 4) :
    dot (mvec a b c X) (mvec a b c Y) =
      (sx X * sx Y * a⁻¹ ^ 2 + sy X * sy Y * b⁻¹ ^ 2 + sz X * sz Y * c⁻¹ ^ 2) /
        (a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2) := by
  rw [← Nb_sq ha hb hc]
  have := ne_of_gt (Nb_pos ha hb hc)
  simp only [mvec]
  vexpand
  field_simp

theorem θ_box (X Y : Fin 4) :
    (box a b c ha hb hc).θ X Y =
      Real.arccos (-((sx X * sx Y * a⁻¹ ^ 2 + sy X * sy Y * b⁻¹ ^ 2 + sz X * sz Y * c⁻¹ ^ 2) /
        (a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2))) := by
  rw [Tet.θ, nrm_box ha hb hc, nrm_box ha hb hc, dot_mvec_mvec ha hb hc]

end

/-! ### The half-turns -/

/-- The Klein group: `kl k X` has the signs of `X` times those of `k`. -/
def kl (k X : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] k X

theorem kl_inj : ∀ k : Fin 4, Function.Injective (kl k) := by decide

theorem kl_zero : ∀ k : Fin 4, kl k 0 = k := by decide

theorem ptype_kl : ∀ k X Y : Fin 4, ptype (kl k X) (kl k Y) = ptype X Y := by decide

theorem signs_kl (k X : Fin 4) :
    sx k * sx X = sx (kl k X) ∧ sy k * sy X = sy (kl k X) ∧ sz k * sz X = sz (kl k X) := by
  fin_cases k <;> fin_cases X <;> norm_num [sx, sy, sz, kl]

/-- The half-turn `diag(s_k)` about a coordinate axis (the identity for `k = 0`). -/
def htIso (k : Fin 4) : Iso where
  r₁ := ⟨sx k, 0, 0⟩
  r₂ := ⟨0, sy k, 0⟩
  r₃ := ⟨0, 0, sz k⟩
  o := 0
  o' := 0
  h11 := by simp only [dot, V.mk_x, V.mk_y, V.mk_z]; linarith [sx_sq k]
  h22 := by simp only [dot, V.mk_x, V.mk_y, V.mk_z]; linarith [sy_sq k]
  h33 := by simp only [dot, V.mk_x, V.mk_y, V.mk_z]; linarith [sz_sq k]
  h12 := by simp [dot]
  h13 := by simp [dot]
  h23 := by simp [dot]

theorem htIso_app (k : Fin 4) (Q : V) :
    (htIso k).app Q = ⟨sx k * Q.x, sy k * Q.y, sz k * Q.z⟩ := by
  simp only [Iso.app, Iso.lin, htIso]
  vexpand
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem htIso_boxP (a b c : ℝ) (k X : Fin 4) : (htIso k).app (boxP a b c X) = boxP a b c (kl k X) := by
  rw [htIso_app]
  obtain ⟨h1, h2, h3⟩ := signs_kl k X
  simp only [boxP, V.mk_x, V.mk_y, V.mk_z, ← h1, ← h2, ← h3]
  ext <;> simp only [V.mk_x, V.mk_y, V.mk_z] <;> ring

section
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {par : Fin 3 → ℝ}
  (hpar : ∀ i, 1 < par i)
include ha hb hc hpar

/-- Lemma 2.4 for the half-turns: the vertices of `M_{e,f,g}` are `(±x, ±y, ±z)` with the
vertex signs, where `A' = (x, y, z)`. -/
theorem mv_box (k : Fin 4) :
    (box a b c ha hb hc).mv par k =
      ⟨sx k * ((box a b c ha hb hc).mv par 0).x, sy k * ((box a b c ha hb hc).mv par 0).y,
        sz k * ((box a b c ha hb hc).mv par 0).z⟩ := by
  have h := mv_iso (T := box a b c ha hb hc) (T' := box a b c ha hb hc) (g := htIso k)
    (kl_inj k) (fun X => htIso_boxP a b c k X) hpar hpar
    (fun X Y => by rw [ptype_kl]) 0
  rw [kl_zero, htIso_app] at h
  exact h.symm

/-- Theorem 1.3(a): `M_{e,f,g}(ABCD)` is regular iff `A' ≠ O` and `A'` lies on one of the four
lines `ℓ₁, …, ℓ₄`. -/
theorem theorem_1_3a :
    Regular ((box a b c ha hb hc).mv par) ↔
      (box a b c ha hb hc).mv par 0 ≠ 0 ∧ onLines ((box a b c ha hb hc).mv par 0) := by
  have hf : (box a b c ha hb hc).mv par = fun k =>
      (⟨sx k * ((box a b c ha hb hc).mv par 0).x, sy k * ((box a b c ha hb hc).mv par 0).y,
        sz k * ((box a b c ha hb hc).mv par 0).z⟩ : V) :=
    funext (mv_box ha hb hc hpar)
  have key := regular_signs ((box a b c ha hb hc).mv par 0).x ((box a b c ha hb hc).mv par 0).y
    ((box a b c ha hb hc).mv par 0).z
  rw [← hf] at key
  rw [key, onLines_iff]

end

section
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
include ha hb hc

/-- Theorem 1.3(b): every interior point (in particular every point `Q ≠ O` of
`ℓ₁ ∪ … ∪ ℓ₄` in the interior) is `A'` for exactly one triple of parameters; by
`theorem_1_3b_regular` that triple gives a regular `M_{e,f,g}(ABCD)` when `Q` is on a line. -/
theorem theorem_1_3b {Q : V} (hQi : Q ∈ (box a b c ha hb hc).interior) :
    ∃! par : Fin 3 → ℝ, (∀ i, 1 < par i) ∧ (box a b c ha hb hc).mv par 0 = Q := by
  obtain ⟨par, hpar, hmv⟩ := (box a b c ha hb hc).mv_surj 0 hQi
  exact ⟨par, ⟨hpar, hmv⟩, fun par' ⟨hpar', hmv'⟩ =>
    (box a b c ha hb hc).mv_inj 0 hpar' hpar (hmv'.trans hmv.symm)⟩

theorem theorem_1_3b_regular {Q : V} (hQ0 : Q ≠ 0) (hQl : onLines Q) {par : Fin 3 → ℝ}
    (hpar : ∀ i, 1 < par i) (hmv : (box a b c ha hb hc).mv par 0 = Q) :
    Regular ((box a b c ha hb hc).mv par) := by
  rw [theorem_1_3a ha hb hc hpar, hmv]
  exact ⟨hQ0, hQl⟩

/-! ### Corollary 1.4 -/

/-- The squared edge lengths (1.2) by class: `AB, CD`; `BC, AD`; `AC, BD`. -/
def elen (a b c : ℝ) : Fin 3 → ℝ := ![4 * (b ^ 2 + c ^ 2), 4 * (a ^ 2 + b ^ 2), 4 * (a ^ 2 + c ^ 2)]

omit ha hb hc in
theorem dist2_box : ∀ X Y : Fin 4, X ≠ Y →
    dist2 (boxP a b c X) (boxP a b c Y) = elen a b c (ptype X Y) := by
  intro X Y h
  fin_cases X <;> fin_cases Y <;>
    simp_all [dist2, V.sq, dot, boxP, sx, sy, sz, elen, ptype] <;> ring

theorem elen_inj (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (elen a b c) := by
  obtain ⟨h1, h2, h3⟩ := three_lengths ha hb hc hab hac hbc
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso; apply h2; change 4 * (b ^ 2 + c ^ 2) = 4 * (a ^ 2 + b ^ 2) at h; linarith
  · exfalso; apply h1; change 4 * (b ^ 2 + c ^ 2) = 4 * (a ^ 2 + c ^ 2) at h; linarith
  · exfalso; apply h2; change 4 * (a ^ 2 + b ^ 2) = 4 * (b ^ 2 + c ^ 2) at h; linarith
  · rfl
  · exfalso; apply h3; change 4 * (a ^ 2 + b ^ 2) = 4 * (a ^ 2 + c ^ 2) at h; linarith
  · exfalso; apply h1; change 4 * (a ^ 2 + c ^ 2) = 4 * (b ^ 2 + c ^ 2) at h; linarith
  · exfalso; apply h3; change 4 * (a ^ 2 + c ^ 2) = 4 * (a ^ 2 + b ^ 2) at h; linarith
  · rfl

/-- The conclusion of Conjecture 1.2 for a tetrahedron: after relabeling, `AC = AD = BC = BD`. -/
def CrossEqual (T : Tet) : Prop :=
  ∃ U W Y Z : Fin 4, U ≠ W ∧ U ≠ Y ∧ U ≠ Z ∧ W ≠ Y ∧ W ≠ Z ∧ Y ≠ Z ∧
    dist2 (T.P U) (T.P Y) = dist2 (T.P U) (T.P Z) ∧
    dist2 (T.P U) (T.P Y) = dist2 (T.P W) (T.P Y) ∧
    dist2 (T.P U) (T.P Y) = dist2 (T.P W) (T.P Z)

/-- Corollary 1.4: with `a, b, c` pairwise different, the three classes of edges have different
lengths, and no pair of opposite edges has four equal cross edges. -/
theorem box_three_lengths (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ X Y Z W : Fin 4, X ≠ Y → Z ≠ W → ptype X Y ≠ ptype Z W →
      dist2 ((box a b c ha hb hc).P X) ((box a b c ha hb hc).P Y) ≠
        dist2 ((box a b c ha hb hc).P Z) ((box a b c ha hb hc).P W) := by
  intro X Y Z W hXY hZW hne h
  rw [box_P, dist2_box X Y hXY, dist2_box Z W hZW] at h
  exact hne (elen_inj ha hb hc hab hac hbc h)

theorem box_no_cross (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ CrossEqual (box a b c ha hb hc) := by
  rintro ⟨U, W, Y, Z, hUW, hUY, hUZ, hWY, hWZ, hYZ, h1, -, -⟩
  exact box_three_lengths ha hb hc hab hac hbc U Y U Z hUY hUZ (ptype_adj U Y Z hUY hUZ hYZ) h1

/-- The points `−t(1,1,1)`, `0 < t < 1/(α+β+γ)`, are interior. -/
theorem line_interior {t : ℝ} (ht : 0 < t) (ht' : t < (a⁻¹ + b⁻¹ + c⁻¹)⁻¹) :
    (-t) • dir 0 ∈ (box a b c ha hb hc).interior := by
  rw [interior_box ha hb hc]
  have hS : 0 < a⁻¹ + b⁻¹ + c⁻¹ := by positivity
  have h1 : t * (a⁻¹ + b⁻¹ + c⁻¹) < 1 := by
    have := mul_lt_mul_of_pos_right ht' hS
    rwa [inv_mul_cancel₀ (ne_of_gt hS)] at this
  have pa := mul_pos ht (inv_pos.2 ha)
  have pb := mul_pos ht (inv_pos.2 hb)
  have pc := mul_pos ht (inv_pos.2 hc)
  intro X
  fin_cases X <;> simp [Lf, dir, sx, sy, sz] <;> nlinarith

end

end Morley
