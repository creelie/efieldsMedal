import Morley.Box

/-!
# Examples 1.5 and 1.6, and the disproof of Conjecture 1.2

* `par_closed`: the parameter of Lemma 2.1 in closed form, `p = arccos c / arctan u`;
* `R4_closed` (3.3): `R_4(θ) = 1 + √(2(1 + cos θ))`;
* `example_1_5`, `example_1_6`: the stated parameters give the stated regular Morley tetrahedra,
  and all parameters lie strictly between `2` and `4` (Remark 2.5 uses `> 2`);
* `tran_false`: Conjecture 1.2 is false;
* `box_regular_infinite`: Corollary 1.4, infinitely many triples.
-/

open Real

namespace Morley
open V

theorem sqrt_eq_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : y ^ 2 = x) : Real.sqrt x = y := by
  rw [← h, Real.sqrt_sq hy]

/-- Lemma 2.1 in closed form: if `θ = arccos c` and `√(1 − c²)/(ρ + c) = u` with `ρ + c > 0`, then
`p = θ / arctan u` satisfies `p > 1` and `R_p(θ) = ρ`. -/
theorem par_closed {θ ρ c u : ℝ} (hρ : 0 < ρ) (hc : -1 < c) (hc' : c < 1)
    (hθ : θ = Real.arccos c) (hpos : 0 < ρ + c) (hu : Real.sqrt (1 - c ^ 2) / (ρ + c) = u) :
    1 < θ / Real.arctan u ∧ R (θ / Real.arctan u) θ = ρ := by
  have h0 : 0 < θ := by rw [hθ, Real.arccos_pos]; exact hc'
  have hπ : θ < π := by rw [hθ, Real.arccos_lt_pi]; exact hc
  have hcos : Real.cos θ = c := by rw [hθ, Real.cos_arccos (by linarith) (by linarith)]
  have hsin : Real.sin θ = Real.sqrt (1 - c ^ 2) := by rw [hθ, Real.sin_arccos]
  have hs : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have key : θ / Real.arctan u = Rinv ρ θ := by
    rw [Rinv, hcos, hsin, arccot_eq_arctan (div_pos hpos hs), inv_div, hu]
  rw [key]
  exact ⟨Rinv_gt_one hρ h0 hπ, R_Rinv hρ h0 hπ⟩

/-- Equation (3.3): `R_4(θ) = 1 + √(2(1 + cos θ))`. -/
theorem R4_closed {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    R 4 θ = 1 + Real.sqrt (2 * (1 + Real.cos θ)) := by
  have hs := sin_phi_pos (by norm_num : (1 : ℝ) < 4) h0 hπ
  rw [R, R4_eq θ (ne_of_gt hs), R4_sub_one θ h0 hπ]

/-- `p < 4` as soon as `(R_p(θ) − 1)² < 2(1 + cos θ)`. -/
theorem lt_four {θ p : ℝ} (h0 : 0 < θ) (hπ : θ < π) (hp : 1 < p)
    (h : (R p θ - 1) ^ 2 < 2 * (1 + Real.cos θ)) : p < 4 := by
  by_contra hle
  push Not at hle
  have hmono : R 4 θ ≤ R p θ :=
    (R_strictMonoOn h0 hπ).le_iff_le (by norm_num : (4 : ℝ) ∈ Set.Ioi 1) hp |>.2 hle
  rw [R4_closed h0 hπ] at hmono
  have hsq : Real.sqrt (2 * (1 + Real.cos θ)) ^ 2 = 2 * (1 + Real.cos θ) :=
    Real.sq_sqrt (by nlinarith [Real.neg_one_le_cos θ])
  have hsn := Real.sqrt_nonneg (2 * (1 + Real.cos θ))
  nlinarith

@[simp] theorem sx0 : sx 0 = 1 := rfl
@[simp] theorem sx1 : sx 1 = 1 := rfl
@[simp] theorem sx2 : sx 2 = -1 := rfl
@[simp] theorem sx3 : sx 3 = -1 := rfl
@[simp] theorem sy0 : sy 0 = 1 := rfl
@[simp] theorem sy1 : sy 1 = -1 := rfl
@[simp] theorem sy2 : sy 2 = 1 := rfl
@[simp] theorem sy3 : sy 3 = -1 := rfl
@[simp] theorem sz0 : sz 0 = 1 := rfl
@[simp] theorem sz1 : sz 1 = -1 := rfl
@[simp] theorem sz2 : sz 2 = -1 := rfl
@[simp] theorem sz3 : sz 3 = 1 := rfl

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp

theorem ptype01 : ptype 0 1 = 0 := by decide
theorem ptype02 : ptype 0 2 = 2 := by decide
theorem ptype03 : ptype 0 3 = 1 := by decide

/-! ### Example 1.5 -/

/-- The parameters of Example 1.5. -/
noncomputable def e15 : ℝ := Real.arccos (-23 / 49) / Real.arctan (4 * Real.sqrt 13 / 25)
noncomputable def f15 : ℝ := Real.arccos (41 / 49) / Real.arctan (20 * Real.sqrt 5 / 297)
noncomputable def g15 : ℝ := Real.arccos (31 / 49) / Real.arctan (5 * Real.sqrt 10 / 66)
noncomputable def par15 : Fin 3 → ℝ := ![e15, f15, g15]

/-- The tetrahedron `(a, b, c) = (1, 2, 3)`. -/
noncomputable def T15 : Tet := box 1 2 3 (by norm_num) (by norm_num) (by norm_num)

theorem θ15 : T15.θ 0 1 = Real.arccos (-23 / 49) ∧ T15.θ 0 2 = Real.arccos (31 / 49) ∧
    T15.θ 0 3 = Real.arccos (41 / 49) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [T15, θ_box] <;> norm_num

theorem R15 : (1 < e15 ∧ R e15 (T15.θ 0 1) = 2) ∧ (1 < g15 ∧ R g15 (T15.θ 0 2) = 13 / 5) ∧
    (1 < f15 ∧ R f15 (T15.θ 0 3) = 14 / 5) := by
  obtain ⟨t1, t2, t3⟩ := θ15
  refine ⟨?_, ?_, ?_⟩
  · rw [t1, e15]
    refine par_closed (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) ?_
    rw [sqrt_eq_of_sq (y := 12 * Real.sqrt 13 / 49) (by positivity)
      (by rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)]; norm_num)]
    ring
  · rw [t2, g15]
    refine par_closed (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) ?_
    rw [sqrt_eq_of_sq (y := 12 * Real.sqrt 10 / 49) (by positivity)
      (by rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]; norm_num)]
    ring
  · rw [t3, f15]
    refine par_closed (by norm_num) (by norm_num) (by norm_num) rfl (by norm_num) ?_
    rw [sqrt_eq_of_sq (y := 12 * Real.sqrt 5 / 49) (by positivity)
      (by rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num)]
    ring

theorem par15_gt : ∀ i, 1 < par15 i := by
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩, ⟨h3, -⟩⟩ := R15
  intro i
  rcases fin3_cases i with rfl | rfl | rfl
  · exact h1
  · exact h3
  · exact h2

/-- The vertex `A'` of Example 1.5. -/
noncomputable def Q15 : V := (2 / 7 : ℝ) • (⟨-1, -1, -1⟩ : V)

theorem mv15 : T15.mv par15 0 = Q15 := by
  have hm : Q15 ∈ T15.mset par15 0 := by
    rw [T15.mem_mset_iff par15_gt]
    obtain ⟨⟨-, r1⟩, ⟨-, r2⟩, ⟨-, r3⟩⟩ := R15
    intro Y
    rcases fin4_cases Y with rfl | rfl | rfl | rfl
    · simp [Tet.ρ_self]
    · rw [T15.ρ_ne (by decide), ptype01, show par15 0 = e15 from rfl, r1, T15, d_box, d_box]
      simp only [Lf, Q15, V.smul_x, V.smul_y, V.smul_z, sx, sy, sz]; norm_num; ring
    · rw [T15.ρ_ne (by decide), ptype02, show par15 2 = g15 from rfl, r2, T15, d_box, d_box]
      simp only [Lf, Q15, V.smul_x, V.smul_y, V.smul_z, sx, sy, sz]; norm_num; ring
    · rw [T15.ρ_ne (by decide), ptype03, show par15 1 = f15 from rfl, r3, T15, d_box, d_box]
      simp only [Lf, Q15, V.smul_x, V.smul_y, V.smul_z, sx, sy, sz]; norm_num; ring
  rw [T15.mset_eq par15_gt] at hm
  exact hm.symm

/-- Example 1.5: for `(a,b,c) = (1,2,3)` and the stated `e, f, g` (all in `(2, 4)`), the Morley
tetrahedron is regular, with vertices `(2/7)(−1,−1,−1)`, `(2/7)(−1,1,1)`, `(2/7)(1,−1,1)`,
`(2/7)(1,1,−1)`.  The edges are `AB² = 52`, `AC² = 40`, `AD² = 20`. -/
theorem example_1_5 :
    (∀ i, 2 < par15 i ∧ par15 i < 4) ∧
    T15.mv par15 0 = (2 / 7 : ℝ) • (⟨-1, -1, -1⟩ : V) ∧
    T15.mv par15 1 = (2 / 7 : ℝ) • (⟨-1, 1, 1⟩ : V) ∧
    T15.mv par15 2 = (2 / 7 : ℝ) • (⟨1, -1, 1⟩ : V) ∧
    T15.mv par15 3 = (2 / 7 : ℝ) • (⟨1, 1, -1⟩ : V) ∧
    Regular (T15.mv par15) ∧
    dist2 (T15.P 0) (T15.P 1) = 52 ∧ dist2 (T15.P 0) (T15.P 2) = 40 ∧
    dist2 (T15.P 0) (T15.P 3) = 20 := by
  obtain ⟨⟨h1, r1⟩, ⟨h2, r2⟩, ⟨h3, r3⟩⟩ := R15
  obtain ⟨t1, t2, t3⟩ := θ15
  have hθ : ∀ Y : Fin 4, Y ≠ 0 → 0 < T15.θ 0 Y ∧ T15.θ 0 Y < π := fun Y hY =>
    ⟨T15.θ_pos 0 Y (Ne.symm hY), T15.θ_lt_pi 0 Y (Ne.symm hY)⟩
  obtain ⟨a1, b1⟩ := hθ 1 (by decide)
  obtain ⟨a2, b2⟩ := hθ 2 (by decide)
  obtain ⟨a3, b3⟩ := hθ 3 (by decide)
  have hbox := fun k => mv_box (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num)
    (by norm_num) par15_gt k
  have hv : ∀ k : Fin 4, T15.mv par15 k = ⟨sx k * Q15.x, sy k * Q15.y, sz k * Q15.z⟩ := by
    intro k; rw [← mv15]; exact hbox k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases fin3_cases i with rfl | rfl | rfl
    · refine ⟨(R_gt_one_iff h1 a1 b1).1 (by rw [r1]; norm_num), lt_four a1 b1 h1 ?_⟩
      rw [show par15 0 = e15 from rfl, r1, t1, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
    · refine ⟨(R_gt_one_iff h3 a3 b3).1 (by rw [r3]; norm_num), lt_four a3 b3 h3 ?_⟩
      rw [show par15 1 = f15 from rfl, r3, t3, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
    · refine ⟨(R_gt_one_iff h2 a2 b2).1 (by rw [r2]; norm_num), lt_four a2 b2 h2 ?_⟩
      rw [show par15 2 = g15 from rfl, r2, t2, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  · exact mv15
  · rw [hv]; simp only [Q15, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp <;> norm_num
  · rw [hv]; simp only [Q15, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp <;> norm_num
  · rw [hv]; simp only [Q15, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp <;> norm_num
  · refine (theorem_1_3a (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num) (by norm_num)
      par15_gt).2 ?_
    change T15.mv par15 0 ≠ 0 ∧ onLines (T15.mv par15 0)
    rw [mv15]
    refine ⟨?_, 0, -2 / 7, ?_⟩
    · intro h; have := congrArg V.x h; simp [Q15] at this
    · ext <;> simp [Q15, dir] <;> norm_num
  · norm_num [T15, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]
  · norm_num [T15, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]
  · norm_num [T15, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]

/-- Corollary 1.4: Conjecture 1.2 (Tran, Conjecture 8.6) is false. -/
def TranConjecture : Prop :=
  ∀ (T : Tet) (par : Fin 3 → ℝ), (∀ i, 1 < par i) → Regular (T.mv par) → CrossEqual T

theorem tran_false : ¬ TranConjecture := by
  intro h
  have := h T15 par15 par15_gt example_1_5.2.2.2.2.2.1
  exact box_no_cross (a := 1) (b := 2) (c := 3) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) this

/-! ### Example 1.6 -/

/-- `r = √(5/21)`. -/
noncomputable def r16 : ℝ := Real.sqrt (5 / 21)

theorem r16_sq : r16 ^ 2 = 5 / 21 := Real.sq_sqrt (by norm_num)
theorem r16_pos : 0 < r16 := Real.sqrt_pos.2 (by norm_num)

noncomputable def g16 : ℝ :=
  Real.arccos (13 / 21) / Real.arctan (2 * Real.sqrt 17 / (17 + 35 * r16))
noncomputable def par16 : Fin 3 → ℝ := ![4, 4, g16]
noncomputable def s16 : ℝ := 5 / 2 - 9 / 2 * r16

/-- The tetrahedron `(a, b, c) = (4, 2, 1)`. -/
noncomputable def T16 : Tet := box 4 2 1 (by norm_num) (by norm_num) (by norm_num)

theorem θ16 : T16.θ 0 1 = Real.arccos (19 / 21) ∧ T16.θ 0 2 = Real.arccos (13 / 21) ∧
    T16.θ 0 3 = Real.arccos (-11 / 21) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [T16, θ_box] <;> norm_num

theorem R16 : R 4 (T16.θ 0 1) = 1 + 4 * r16 ∧ R 4 (T16.θ 0 3) = 1 + 2 * r16 ∧
    (1 < g16 ∧ R g16 (T16.θ 0 2) = 1 + 10 / 3 * r16) := by
  obtain ⟨t1, t2, t3⟩ := θ16
  have hr := r16_sq
  have hr0 := r16_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [R4_closed (T16.θ_pos 0 1 (by decide)) (T16.θ_lt_pi 0 1 (by decide)), t1,
      Real.cos_arccos (by norm_num) (by norm_num)]
    rw [sqrt_eq_of_sq (y := 4 * r16) (by positivity) (by rw [mul_pow, hr]; norm_num)]
  · rw [R4_closed (T16.θ_pos 0 3 (by decide)) (T16.θ_lt_pi 0 3 (by decide)), t3,
      Real.cos_arccos (by norm_num) (by norm_num)]
    rw [sqrt_eq_of_sq (y := 2 * r16) (by positivity) (by rw [mul_pow, hr]; norm_num)]
  · rw [t2, g16]
    refine par_closed (by positivity) (by norm_num) (by norm_num) rfl (by positivity) ?_
    rw [sqrt_eq_of_sq (y := 4 * Real.sqrt 17 / 21) (by positivity)
      (by rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)]; norm_num)]
    have : 0 < 17 + 35 * r16 := by positivity
    field_simp
    ring

theorem par16_gt : ∀ i, 1 < par16 i := by
  obtain ⟨-, -, h, -⟩ := R16
  intro i
  rcases fin3_cases i with rfl | rfl | rfl
  · show (1 : ℝ) < 4; norm_num
  · show (1 : ℝ) < 4; norm_num
  · exact h

noncomputable def Q16 : V := s16 • (⟨-1, -1, -1⟩ : V)

theorem mv16 : T16.mv par16 0 = Q16 := by
  have hm : Q16 ∈ T16.mset par16 0 := by
    rw [T16.mem_mset_iff par16_gt]
    obtain ⟨r1, r3, -, r2⟩ := R16
    have hr := r16_sq
    intro Y
    rcases fin4_cases Y with rfl | rfl | rfl | rfl
    · simp [Tet.ρ_self]
    · rw [T16.ρ_ne (by decide), ptype01, show par16 0 = 4 from rfl, r1, T16, d_box, d_box,
        mul_div_assoc']
      congr 1
      simp only [Lf, Q16, s16, V.smul_x, V.smul_y, V.smul_z, sx0, sx1, sx2, sx3, sy0, sy1, sy2, sy3, sz0, sz1, sz2, sz3]
      linear_combination (-63 / 2) * hr
    · rw [T16.ρ_ne (by decide), ptype02, show par16 2 = g16 from rfl, r2, T16, d_box, d_box,
        mul_div_assoc']
      congr 1
      simp only [Lf, Q16, s16, V.smul_x, V.smul_y, V.smul_z, sx0, sx1, sx2, sx3, sy0, sy1, sy2, sy3, sz0, sz1, sz2, sz3]
      linear_combination (-105 / 4) * hr
    · rw [T16.ρ_ne (by decide), ptype03, show par16 1 = 4 from rfl, r3, T16, d_box, d_box,
        mul_div_assoc']
      congr 1
      simp only [Lf, Q16, s16, V.smul_x, V.smul_y, V.smul_z, sx0, sx1, sx2, sx3, sy0, sy1, sy2, sy3, sz0, sz1, sz2, sz3]
      linear_combination (-63 / 4) * hr
  rw [T16.mset_eq par16_gt] at hm
  exact hm.symm

/-- Example 1.6: for `(a,b,c) = (4,2,1)`, `e = f = 4` and the stated `g ∈ (2, 4)`, the Morley
tetrahedron is regular, with vertices `s(−1,−1,−1)`, `s(−1,1,1)`, `s(1,−1,1)`, `s(1,1,−1)`,
`s = 5/2 − (9/2)√(5/21) > 0`.  The edges are `AB² = 20`, `AC² = 68`, `AD² = 80`. -/
theorem example_1_6 :
    (∀ i, 2 < par16 i ∧ par16 i < 4 ∨ par16 i = 4) ∧ 2 < g16 ∧ g16 < 4 ∧ 0 < s16 ∧
    T16.mv par16 0 = s16 • (⟨-1, -1, -1⟩ : V) ∧
    T16.mv par16 1 = s16 • (⟨-1, 1, 1⟩ : V) ∧
    T16.mv par16 2 = s16 • (⟨1, -1, 1⟩ : V) ∧
    T16.mv par16 3 = s16 • (⟨1, 1, -1⟩ : V) ∧
    Regular (T16.mv par16) ∧
    dist2 (T16.P 0) (T16.P 1) = 20 ∧ dist2 (T16.P 0) (T16.P 2) = 68 ∧
    dist2 (T16.P 0) (T16.P 3) = 80 := by
  obtain ⟨-, -, hg, rg⟩ := R16
  have t2 := θ16.2.1
  have hr := r16_sq
  have hr0 := r16_pos
  have a2 := T16.θ_pos 0 2 (by decide)
  have b2 := T16.θ_lt_pi 0 2 (by decide)
  have hg2 : 2 < g16 := (R_gt_one_iff hg a2 b2).1 (by rw [rg]; nlinarith)
  have hg4 : g16 < 4 := by
    apply lt_four a2 b2 hg
    rw [rg, t2, Real.cos_arccos (by norm_num) (by norm_num)]
    nlinarith
  have hs : 0 < s16 := by
    rw [s16]
    have : r16 < 5 / 9 := by nlinarith
    linarith
  have hbox := fun k => mv_box (a := 4) (b := 2) (c := 1) (by norm_num) (by norm_num)
    (by norm_num) par16_gt k
  have hv : ∀ k : Fin 4, T16.mv par16 k = ⟨sx k * Q16.x, sy k * Q16.y, sz k * Q16.z⟩ := by
    intro k; rw [← mv16]; exact hbox k
  refine ⟨?_, hg2, hg4, hs, mv16, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases fin3_cases i with rfl | rfl | rfl
    · right; rfl
    · right; rfl
    · left; exact ⟨hg2, hg4⟩
  · rw [hv]; simp only [Q16, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp
  · rw [hv]; simp only [Q16, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp
  · rw [hv]; simp only [Q16, V.smul_x, V.smul_y, V.smul_z]; ext <;> simp
  · refine (theorem_1_3a (a := 4) (b := 2) (c := 1) (by norm_num) (by norm_num) (by norm_num)
      par16_gt).2 ?_
    change T16.mv par16 0 ≠ 0 ∧ onLines (T16.mv par16 0)
    rw [mv16]
    refine ⟨?_, 0, -s16, ?_⟩
    · intro h; have := congrArg V.x h; simp [Q16] at this; linarith
    · ext <;> simp [Q16, dir]
  · norm_num [T16, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]
  · norm_num [T16, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]
  · norm_num [T16, box_P, dist2, V.sq, dot, boxP, sx, sy, sz]

/-! ### Corollary 1.4: infinitely many triples -/

section
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
include ha hb hc

/-- Corollary 1.4: `M_{e,f,g}(ABCD)` is regular for infinitely many triples. -/
theorem box_regular_infinite :
    {par : Fin 3 → ℝ | (∀ i, 1 < par i) ∧ Regular ((box a b c ha hb hc).mv par)}.Infinite := by
  set t0 := (a⁻¹ + b⁻¹ + c⁻¹)⁻¹ with ht0def
  have ht0 : 0 < t0 := by positivity
  haveI : Infinite (Set.Ioo (0 : ℝ) t0) := (Set.Ioo_infinite ht0).to_subtype
  have hex : ∀ t : Set.Ioo (0 : ℝ) t0, ∃ par : Fin 3 → ℝ,
      (∀ i, 1 < par i) ∧ (box a b c ha hb hc).mv par 0 = (-(t : ℝ)) • dir 0 := by
    intro t
    obtain ⟨par, ⟨hpar, hmv⟩, -⟩ :=
      theorem_1_3b ha hb hc (line_interior ha hb hc t.2.1 t.2.2)
    exact ⟨par, hpar, hmv⟩
  choose f hf1 hf2 using hex
  apply Set.infinite_of_injective_forall_mem (f := f)
  · intro t s hts
    have h := (hf2 t).symm.trans ((congrArg (fun p => (box a b c ha hb hc).mv p 0) hts).trans
      (hf2 s))
    have hx := congrArg V.x h
    simp [dir] at hx
    exact Subtype.ext hx
  · intro t
    refine ⟨hf1 t, theorem_1_3b_regular ha hb hc ?_ ⟨0, -(t : ℝ), rfl⟩ (hf1 t) (hf2 t)⟩
    intro h
    have hx := congrArg V.x h
    simp [dir] at hx
    exact (ne_of_gt t.2.1) hx

end

end Morley
