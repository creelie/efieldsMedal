import Mathlib

/-!
# Algebraic steps of "Regular Morley tetrahedra from p-secting planes"

Kernel-checked versions of the identities, inequalities and case analyses used in the
proofs of the paper. The geometric statements (the planes, the distances to the faces)
are reduced in the paper to these facts.

* Lemma 2.1: `ratio_sub`, `ratio_cot`, `sin_sub_sin_half`, `cot_strictAnti`.
* Lemma 2.1 for p = 4, equation (3.3) (Example 1.6, Section 4):
  `sin_three_mul_eq`, `R4_eq`, `R4_sub_one_sq`, `R4_sub_one`.
* Section 3: the face functions `LA`, `LB`, `LC`, `LD`, their values at the vertices
  (`faces_at_vertices`), the half-turns (`halfturns`), the edge lengths of the Morley
  tetrahedron (`morley_edges`, `regular_iff`), the ratios on the four lines
  (`ratios_delta1` to `ratios_delta4`) and Corollary 1.4 (`three_lengths`).
* Examples 1.5 and 1.6: `example_123`, `example_421`.
* Theorem 1.7: `r_identity`, `quot_eq_one_sub`, `no_common_quotient`, `case_analysis`,
  `theorem_four_algebra`.
-/

open Real

namespace Morley

/-! ## Lemma 2.1 -/

/-- `sin (θ - φ) = sin θ cos φ - cos θ sin φ`, the first step of Lemma 2.1. -/
theorem ratio_sub (θ φ : ℝ) :
    Real.sin (θ - φ) = Real.sin θ * Real.cos φ - Real.cos θ * Real.sin φ :=
  Real.sin_sub θ φ

/-- `R_p(θ) = sin θ cot φ - cos θ` with `φ = θ / p`. -/
theorem ratio_cot (θ φ : ℝ) (h : Real.sin φ ≠ 0) :
    Real.sin (θ - φ) / Real.sin φ = Real.sin θ * (Real.cos φ / Real.sin φ) - Real.cos θ := by
  rw [Real.sin_sub]
  field_simp

/-- `sin (θ - φ) - sin φ = 2 cos (θ/2) sin (θ/2 - φ)`: so `R_p(θ) > 1` iff `φ < θ/2`. -/
theorem sin_sub_sin_half (θ φ : ℝ) :
    Real.sin (θ - φ) - Real.sin φ = 2 * Real.cos (θ / 2) * Real.sin (θ / 2 - φ) := by
  rw [Real.sin_sub_sin]
  have h1 : (θ - φ - φ) / 2 = θ / 2 - φ := by ring
  have h2 : (θ - φ + φ) / 2 = θ / 2 := by ring
  rw [h1, h2]
  ring

/-- The cotangent decreases on `(0, π)`, written without division:
`cot φ₂ < cot φ₁` for `0 < φ₁ < φ₂ < π`. -/
theorem cot_strictAnti {φ₁ φ₂ : ℝ} (h0 : 0 < φ₁) (h12 : φ₁ < φ₂) (h2 : φ₂ < π) :
    Real.cos φ₂ * Real.sin φ₁ < Real.cos φ₁ * Real.sin φ₂ := by
  have s21 : 0 < Real.sin (φ₂ - φ₁) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub] at s21
  linarith

/-- `sin 3u = sin u (1 + 2 cos 2u)`. -/
theorem sin_three_mul_eq (u : ℝ) :
    Real.sin (3 * u) = Real.sin u * (1 + 2 * Real.cos (2 * u)) := by
  rw [Real.sin_three_mul, Real.cos_two_mul]
  linear_combination (-4 * Real.sin u) * Real.sin_sq_add_cos_sq u

/-- Equation (3.3): `R_4(θ) = 1 + 2 cos (θ/2)`. -/
theorem R4_eq (θ : ℝ) (h : Real.sin (θ / 4) ≠ 0) :
    Real.sin ((4 - 1) * θ / 4) / Real.sin (θ / 4) = 1 + 2 * Real.cos (θ / 2) := by
  have e1 : (4 - 1) * θ / 4 = 3 * (θ / 4) := by ring
  have e2 : θ / 2 = 2 * (θ / 4) := by ring
  rw [e1, e2, sin_three_mul_eq]
  field_simp

/-- `(R_4(θ) - 1)^2 = 2 (1 + cos θ)`. -/
theorem R4_sub_one_sq (θ : ℝ) : (2 * Real.cos (θ / 2)) ^ 2 = 2 * (1 + Real.cos θ) := by
  have h : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
  rw [h, Real.cos_two_mul]
  ring

/-- Equation (3.3): `R_4(θ) - 1 = √(2 (1 + cos θ))` for `0 < θ < π`. -/
theorem R4_sub_one (θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) :
    2 * Real.cos (θ / 2) = Real.sqrt (2 * (1 + Real.cos θ)) := by
  have hc : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  rw [← R4_sub_one_sq, Real.sqrt_sq (by linarith)]

/-! ## Section 3: isosceles tetrahedra -/

/-- The face functions of Section 3; `d_X = L_X / N`. -/
def LA (α β γ x y z : ℝ) : ℝ := 1 + α * x + β * y + γ * z
def LB (α β γ x y z : ℝ) : ℝ := 1 + α * x - β * y - γ * z
def LC (α β γ x y z : ℝ) : ℝ := 1 - α * x + β * y - γ * z
def LD (α β γ x y z : ℝ) : ℝ := 1 - α * x - β * y + γ * z

/-- Each `L_X` equals `4` at `X` and vanishes at the other three vertices of
`A = (a,b,c)`, `B = (a,-b,-c)`, `C = (-a,b,-c)`, `D = (-a,-b,c)`. -/
theorem faces_at_vertices {a b c α β γ : ℝ} (ha : α * a = 1) (hb : β * b = 1)
    (hc : γ * c = 1) :
    (LA α β γ a b c = 4 ∧ LA α β γ a (-b) (-c) = 0 ∧ LA α β γ (-a) b (-c) = 0 ∧
      LA α β γ (-a) (-b) c = 0) ∧
    (LB α β γ a b c = 0 ∧ LB α β γ a (-b) (-c) = 4 ∧ LB α β γ (-a) b (-c) = 0 ∧
      LB α β γ (-a) (-b) c = 0) ∧
    (LC α β γ a b c = 0 ∧ LC α β γ a (-b) (-c) = 0 ∧ LC α β γ (-a) b (-c) = 4 ∧
      LC α β γ (-a) (-b) c = 0) ∧
    (LD α β γ a b c = 0 ∧ LD α β γ a (-b) (-c) = 0 ∧ LD α β γ (-a) b (-c) = 0 ∧
      LD α β γ (-a) (-b) c = 4) := by
  simp only [LA, LB, LC, LD]
  exact
    ⟨⟨by linear_combination ha + hb + hc, by linear_combination ha - hb - hc,
        by linear_combination -ha + hb - hc, by linear_combination -ha - hb + hc⟩,
      ⟨by linear_combination ha - hb - hc, by linear_combination ha + hb + hc,
        by linear_combination -ha - hb + hc, by linear_combination -ha + hb - hc⟩,
      ⟨by linear_combination -ha + hb - hc, by linear_combination -ha - hb + hc,
        by linear_combination ha + hb + hc, by linear_combination ha - hb - hc⟩,
      ⟨by linear_combination -ha - hb + hc, by linear_combination -ha + hb - hc,
        by linear_combination ha - hb - hc, by linear_combination ha + hb + hc⟩⟩

/-- The half-turns `h₁, h₂, h₃` about the coordinate axes permute the face functions as
`(A B)(C D)`, `(A C)(B D)` and `(A D)(B C)`. -/
theorem halfturns (α β γ x y z : ℝ) :
    (LA α β γ x (-y) (-z) = LB α β γ x y z ∧ LC α β γ x (-y) (-z) = LD α β γ x y z) ∧
    (LA α β γ (-x) y (-z) = LC α β γ x y z ∧ LB α β γ (-x) y (-z) = LD α β γ x y z) ∧
    (LA α β γ (-x) (-y) z = LD α β γ x y z ∧ LB α β γ (-x) (-y) z = LC α β γ x y z) := by
  simp only [LA, LB, LC, LD]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ring

/-- The squared edge lengths of `A'B'C'D'` with `A' = (x,y,z)`, `B' = (x,-y,-z)`,
`C' = (-x,y,-z)`, `D' = (-x,-y,z)`. -/
theorem morley_edges (x y z : ℝ) :
    (x - x) ^ 2 + (y - -y) ^ 2 + (z - -z) ^ 2 = 4 * (y ^ 2 + z ^ 2) ∧
    (-x - -x) ^ 2 + (y - -y) ^ 2 + (-z - z) ^ 2 = 4 * (y ^ 2 + z ^ 2) ∧
    (x - -x) ^ 2 + (y - y) ^ 2 + (z - -z) ^ 2 = 4 * (x ^ 2 + z ^ 2) ∧
    (x - -x) ^ 2 + (-y - -y) ^ 2 + (-z - z) ^ 2 = 4 * (x ^ 2 + z ^ 2) ∧
    (x - -x) ^ 2 + (y - -y) ^ 2 + (z - z) ^ 2 = 4 * (x ^ 2 + y ^ 2) ∧
    (x - -x) ^ 2 + (-y - y) ^ 2 + (-z - -z) ^ 2 = 4 * (x ^ 2 + y ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- Theorem 1.3(a): the three edge lengths agree iff `x² = y² = z²`. -/
theorem regular_iff (x y z : ℝ) :
    (y ^ 2 + z ^ 2 = x ^ 2 + z ^ 2 ∧ x ^ 2 + z ^ 2 = x ^ 2 + y ^ 2) ↔
      (x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- `x² = y² = z²` means that `(x,y,z)` lies on one of the four lines `ℓ₁, …, ℓ₄`. -/
theorem on_lines (x y z : ℝ) (h1 : x ^ 2 = y ^ 2) (h2 : y ^ 2 = z ^ 2) :
    (y = x ∧ z = x) ∨ (y = -x ∧ z = -x) ∨ (y = x ∧ z = -x) ∨ (y = -x ∧ z = x) := by
  have hy : y = x ∨ y = -x := by
    have : (y - x) * (y + x) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have hz : z = x ∨ z = -x := by
    have : (z - x) * (z + x) = 0 := by linear_combination -h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact Or.inl ⟨hy, hz⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hy, hz⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hy, hz⟩))
  · exact Or.inr (Or.inl ⟨hy, hz⟩)

/-- Equation (3.2) and the table in the proof of Theorem 1.7: on the line through
`δ₁ = (1,1,1)`, `L_B - L_A = -2t w_CD` and so on. -/
theorem ratios_delta1 (α β γ t : ℝ) :
    LB α β γ t t t - LA α β γ t t t = -2 * t * (β + γ) ∧
    LC α β γ t t t - LA α β γ t t t = -2 * t * (α + γ) ∧
    LD α β γ t t t - LA α β γ t t t = -2 * t * (α + β) := by
  simp only [LA, LB, LC, LD]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem ratios_delta2 (α β γ t : ℝ) :
    LB α β γ t (-t) (-t) - LA α β γ t (-t) (-t) = -2 * t * (-β - γ) ∧
    LC α β γ t (-t) (-t) - LA α β γ t (-t) (-t) = -2 * t * (α - γ) ∧
    LD α β γ t (-t) (-t) - LA α β γ t (-t) (-t) = -2 * t * (α - β) := by
  simp only [LA, LB, LC, LD]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem ratios_delta3 (α β γ t : ℝ) :
    LB α β γ (-t) t (-t) - LA α β γ (-t) t (-t) = -2 * t * (β - γ) ∧
    LC α β γ (-t) t (-t) - LA α β γ (-t) t (-t) = -2 * t * (-α - γ) ∧
    LD α β γ (-t) t (-t) - LA α β γ (-t) t (-t) = -2 * t * (β - α) := by
  simp only [LA, LB, LC, LD]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem ratios_delta4 (α β γ t : ℝ) :
    LB α β γ (-t) (-t) t - LA α β γ (-t) (-t) t = -2 * t * (γ - β) ∧
    LC α β γ (-t) (-t) t - LA α β γ (-t) (-t) t = -2 * t * (γ - α) ∧
    LD α β γ (-t) (-t) t - LA α β γ (-t) (-t) t = -2 * t * (-α - β) := by
  simp only [LA, LB, LC, LD]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Corollary 1.4: pairwise different `a, b, c > 0` give three different values of
`b² + c²`, `a² + c²`, `a² + b²`. -/
theorem three_lengths {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    b ^ 2 + c ^ 2 ≠ a ^ 2 + c ^ 2 ∧ b ^ 2 + c ^ 2 ≠ a ^ 2 + b ^ 2 ∧
      a ^ 2 + c ^ 2 ≠ a ^ 2 + b ^ 2 := by
  refine ⟨fun h => hab ?_, fun h => hac ?_, fun h => hbc ?_⟩
  · have : (a - b) * (a + b) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : (a - c) * (a + c) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · have : (b - c) * (b + c) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith

/-! ## Examples 1.5 and 1.6 -/

/-- Example 1.5, `(a,b,c) = (1,2,3)`, `(α,β,γ) = (1,1/2,1/3)`, `X = -(2/7)(1,1,1)`:
the cosines, the squared sines, `L_A(X)`, `λ`, the three ratios, and the squared tangents
`tan² φ = sin² θ / (ρ + cos θ)²`, together with `ρ + cos θ > 0`. -/
theorem example_123 :
    let α : ℚ := 1; let β : ℚ := 1 / 2; let γ : ℚ := 1 / 3
    let N2 := α ^ 2 + β ^ 2 + γ ^ 2
    let cCD := (-α ^ 2 + β ^ 2 + γ ^ 2) / N2
    let cBD := (α ^ 2 - β ^ 2 + γ ^ 2) / N2
    let cBC := (α ^ 2 + β ^ 2 - γ ^ 2) / N2
    let t : ℚ := 2 / 7
    let LAX := 1 - t * (α + β + γ)
    let lam := t / LAX
    let rCD := 1 + 2 * (β + γ) * lam
    let rBD := 1 + 2 * (α + γ) * lam
    let rBC := 1 + 2 * (α + β) * lam
    N2 = 49 / 36 ∧ cCD = -23 / 49 ∧ cBD = 31 / 49 ∧ cBC = 41 / 49 ∧
    1 - cCD ^ 2 = 144 * 13 / 49 ^ 2 ∧ 1 - cBD ^ 2 = 144 * 10 / 49 ^ 2 ∧
    1 - cBC ^ 2 = 144 * 5 / 49 ^ 2 ∧
    LAX = 10 / 21 ∧ lam = 3 / 5 ∧ rCD = 2 ∧ rBD = 13 / 5 ∧ rBC = 14 / 5 ∧
    0 < rCD + cCD ∧ 0 < rBD + cBD ∧ 0 < rBC + cBC ∧
    (1 - cCD ^ 2) / (rCD + cCD) ^ 2 = 16 * 13 / 25 ^ 2 ∧
    (1 - cBD ^ 2) / (rBD + cBD) ^ 2 = 25 * 10 / 66 ^ 2 ∧
    (1 - cBC ^ 2) / (rBC + cBC) ^ 2 = 400 * 5 / 297 ^ 2 := by
  norm_num

/-- Example 1.6, `(a,b,c) = (4,2,1)`, `(α,β,γ) = (1/4,1/2,1)`, with `s = √(5/21)`:
the cosines, `2(1 + cos θ) = (R_4 - 1)²` for the edges `CD` and `BC`, the common value of
`λ` for `e = f = 4`, the value of `t` and interiority, the third ratio and `tan φ_BD`. -/
theorem example_421 :
    let α : ℝ := 1 / 4; let β : ℝ := 1 / 2; let γ : ℝ := 1
    let N2 := α ^ 2 + β ^ 2 + γ ^ 2
    let s := Real.sqrt (5 / 21)
    let lam := 4 / 3 * s
    let t := 5 / 2 - 9 / 2 * s
    N2 = 21 / 16 ∧
    (-α ^ 2 + β ^ 2 + γ ^ 2) / N2 = 19 / 21 ∧ (α ^ 2 - β ^ 2 + γ ^ 2) / N2 = 13 / 21 ∧
    (α ^ 2 + β ^ 2 - γ ^ 2) / N2 = -11 / 21 ∧
    2 * (1 + 19 / 21) = (4 * s) ^ 2 ∧ 2 * (1 + -11 / 21) = (2 * s) ^ 2 ∧
    1 + 2 * (β + γ) * lam = 1 + 4 * s ∧ 1 + 2 * (α + β) * lam = 1 + 2 * s ∧
    t * (1 + (α + β + γ) * lam) = lam ∧ 0 < t ∧ 0 < 1 - t * (α + β + γ) ∧
    1 + 2 * (α + γ) * lam = 1 + 10 / 3 * s ∧
    1 - (13 / 21 : ℝ) ^ 2 = 16 * 17 / 21 ^ 2 ∧
    (4 * Real.sqrt 17 / 21) / (1 + 10 / 3 * s + 13 / 21) =
      2 * Real.sqrt 17 / (17 + 35 * s) := by
  intro α β γ N2 s lam t
  have hs2 : s ^ 2 = 5 / 21 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s < 1 / 2 := by nlinarith
  have hpos : 0 < 17 + 35 * s := by linarith
  have hpos' : 0 < 1 + 10 / 3 * s + 13 / 21 := by linarith
  refine ⟨by norm_num [N2, α, β, γ], by norm_num [N2, α, β, γ], by norm_num [N2, α, β, γ],
    by norm_num [N2, α, β, γ], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_⟩
  · linear_combination (-16) * hs2
  · linear_combination (-4) * hs2
  · simp only [lam, β, γ]; ring
  · simp only [lam, α, β]; ring
  · simp only [t, lam, α, β, γ]; linear_combination (-21 / 2) * hs2
  · simp only [t]; nlinarith
  · simp only [t, α, β, γ]; nlinarith
  · simp only [lam, α, γ]; ring
  · rw [div_eq_div_iff (ne_of_gt hpos') (ne_of_gt hpos)]
    ring

/-! ## Theorem 1.7 -/

/-- `r(u,v) - r(u,w)` with `r(u,v) = uv/(u+v)²`. -/
theorem r_identity (u v w : ℝ) (hv : u + v ≠ 0) (hw : u + w ≠ 0) :
    u * v / (u + v) ^ 2 - u * w / (u + w) ^ 2 =
      u * (v - w) * (u ^ 2 - v * w) / ((u + v) ^ 2 * (u + w) ^ 2) := by
  field_simp
  ring

/-- `(u² + v²)/(u + v)² = 1 - 2 r(u,v)`. -/
theorem quot_eq_one_sub (u v : ℝ) (h : u + v ≠ 0) :
    (u ^ 2 + v ^ 2) / (u + v) ^ 2 = 1 - 2 * (u * v / (u + v) ^ 2) := by
  field_simp
  ring

/-- The lines `ℓ₂, ℓ₃, ℓ₄` are impossible for `e = f = g = 4`: no `k` satisfies
`u² + v² = k (u + v)²` and `x² + y² = k (x - y)²` with `u, v, x, y > 0`. Here
`k = μ² N²`, and `(u,v)`, `(x,y)` are `(β,γ)`, `(α,γ)` for `δ₂`; `(α,γ)`, `(β,γ)` for
`δ₃`; `(α,β)`, `(β,γ)` for `δ₄` (only `w_E²` enters, so signs do not matter). -/
theorem no_common_quotient {u v x y k : ℝ} (hu : 0 < u) (hv : 0 < v) (hx : 0 < x)
    (hy : 0 < y) (h1 : u ^ 2 + v ^ 2 = k * (u + v) ^ 2)
    (h2 : x ^ 2 + y ^ 2 = k * (x - y) ^ 2) : False := by
  have huv : 0 < u * v := mul_pos hu hv
  have hxy : 0 < x * y := mul_pos hx hy
  have hk1 : k < 1 := by
    by_contra hk
    rw [not_lt] at hk
    have : (u + v) ^ 2 ≤ k * (u + v) ^ 2 := by nlinarith [sq_nonneg (u + v)]
    nlinarith
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  have : k * (x - y) ^ 2 ≤ (x - y) ^ 2 := by nlinarith
  nlinarith

/-- The case analysis at the end of the proof of Theorem 1.7. -/
theorem case_analysis {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (h1 : (β - α) * (γ ^ 2 - α * β) = 0) (h2 : (γ - β) * (α ^ 2 - β * γ) = 0) :
    α = β ∧ β = γ := by
  have hab : α = β := by
    by_contra hne
    have hb : γ ^ 2 = α * β := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd (by linarith) hne
      · linarith
    rcases mul_eq_zero.1 h2 with h | h
    · have hgb : γ = β := by linarith
      rw [hgb] at hb
      have : β * (β - α) = 0 := by linear_combination hb
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact hne (by linarith)
    · have ha2 : α ^ 2 = β * γ := by linarith
      have hc : (γ - α) * (γ ^ 2 + γ * α + α ^ 2) = 0 := by
        linear_combination γ * hb - α * ha2
      have hpos : 0 < γ ^ 2 + γ * α + α ^ 2 := by positivity
      have hga : γ = α := by
        rcases mul_eq_zero.1 hc with h' | h'
        · linarith
        · linarith
      rw [hga] at ha2
      have : α * (α - β) = 0 := by linear_combination ha2
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exact hne (by linarith)
  refine ⟨hab, ?_⟩
  rw [hab] at h2
  have h3 : β * (γ - β) ^ 2 = 0 := by linear_combination -h2
  rcases mul_eq_zero.1 h3 with h' | h'
  · linarith
  · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'
    linarith

/-- Theorem 1.7 for the line `ℓ₁`, from the three equal quotients to `α = β = γ`. -/
theorem theorem_four_algebra {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (h1 : (β ^ 2 + γ ^ 2) / (β + γ) ^ 2 = (α ^ 2 + γ ^ 2) / (α + γ) ^ 2)
    (h2 : (α ^ 2 + γ ^ 2) / (α + γ) ^ 2 = (α ^ 2 + β ^ 2) / (α + β) ^ 2) :
    α = β ∧ β = γ := by
  have nbg : γ + β ≠ 0 := by linarith
  have nga : γ + α ≠ 0 := by linarith
  have nag : α + γ ≠ 0 := by linarith
  have nab : α + β ≠ 0 := by linarith
  -- r(γ,β) = r(γ,α) and r(α,γ) = r(α,β)
  have e1 : γ * β / (γ + β) ^ 2 - γ * α / (γ + α) ^ 2 = 0 := by
    rw [show γ + β = β + γ by ring, show γ + α = α + γ by ring,
      show γ * β = β * γ by ring, show γ * α = α * γ by ring]
    rw [quot_eq_one_sub β γ (by linarith), quot_eq_one_sub α γ (by linarith)] at h1
    linarith
  have e2 : α * γ / (α + γ) ^ 2 - α * β / (α + β) ^ 2 = 0 := by
    rw [quot_eq_one_sub α γ (by linarith), quot_eq_one_sub α β (by linarith)] at h2
    linarith
  rw [r_identity γ β α nbg nga] at e1
  rw [r_identity α γ β nag nab] at e2
  have d1 : (γ + β) ^ 2 * (γ + α) ^ 2 ≠ 0 := by positivity
  have d2 : (α + γ) ^ 2 * (α + β) ^ 2 ≠ 0 := by positivity
  have f1 : γ * ((β - α) * (γ ^ 2 - β * α)) = 0 := by
    rw [div_eq_zero_iff] at e1
    rcases e1 with h | h
    · linear_combination h
    · exact absurd h d1
  have f2 : α * ((γ - β) * (α ^ 2 - γ * β)) = 0 := by
    rw [div_eq_zero_iff] at e2
    rcases e2 with h | h
    · linear_combination h
    · exact absurd h d2
  have g1 : (β - α) * (γ ^ 2 - α * β) = 0 := by
    rcases mul_eq_zero.1 f1 with h | h
    · linarith
    · linear_combination h
  have g2 : (γ - β) * (α ^ 2 - β * γ) = 0 := by
    rcases mul_eq_zero.1 f2 with h | h
    · linarith
    · linear_combination h
  exact case_analysis hα hβ hγ g1 g2

end Morley
