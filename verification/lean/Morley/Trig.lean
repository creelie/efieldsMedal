import Mathlib
import Morley.Algebra

/-!
# Lemma 2.1: the ratio `R_p(θ)`

`R p θ = sin((p − 1)θ/p) / sin(θ/p)`.  For `0 < θ < π`, `p ↦ R p θ` is a strictly increasing
bijection from `(1, ∞)` onto `(0, ∞)`, `R p θ > 1` iff `p > 2`, and the inverse is
`p = θ/φ` with `cot φ = (ρ + cos θ)/sin θ`.
-/

open Real

namespace Morley

/-- `R_p(θ) = sin((p−1)θ/p) / sin(θ/p)`. -/
noncomputable def R (p θ : ℝ) : ℝ := Real.sin ((p - 1) * θ / p) / Real.sin (θ / p)

section
variable {θ : ℝ}

theorem phi_pos {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) : 0 < θ / p := div_pos h0 (by linarith)

theorem phi_lt {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) : θ / p < θ := div_lt_self h0 hp

theorem sin_phi_pos {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) (hπ : θ < π) : 0 < Real.sin (θ / p) :=
  Real.sin_pos_of_pos_of_lt_pi (phi_pos hp h0) (lt_trans (phi_lt hp h0) hπ)

theorem sin_theta_pos (h0 : 0 < θ) (hπ : θ < π) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi h0 hπ

theorem R_arg {p : ℝ} (hp : 1 < p) : (p - 1) * θ / p = θ - θ / p := by
  have : p ≠ 0 := by linarith
  field_simp

/-- `R_p(θ) = sin(θ − φ)/sin φ` with `φ = θ/p`. -/
theorem R_eq_sub {p : ℝ} (hp : 1 < p) : R p θ = Real.sin (θ - θ / p) / Real.sin (θ / p) := by
  rw [R, R_arg hp]

/-- `R_p(θ) = sin θ cot(θ/p) − cos θ`. -/
theorem R_eq_cot {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) (hπ : θ < π) :
    R p θ = Real.sin θ * (Real.cos (θ / p) / Real.sin (θ / p)) - Real.cos θ := by
  rw [R_eq_sub hp]
  exact ratio_cot θ (θ / p) (ne_of_gt (sin_phi_pos hp h0 hπ))

theorem R_pos {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) (hπ : θ < π) : 0 < R p θ := by
  rw [R_eq_sub hp]
  apply div_pos _ (sin_phi_pos hp h0 hπ)
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [phi_lt hp h0]
  · linarith [phi_pos hp h0]

/-- The cotangent is strictly decreasing on `(0, π)`. -/
theorem cot_lt {φ₁ φ₂ : ℝ} (h0 : 0 < φ₁) (h12 : φ₁ < φ₂) (h2 : φ₂ < π) :
    Real.cos φ₂ / Real.sin φ₂ < Real.cos φ₁ / Real.sin φ₁ := by
  have s1 : 0 < Real.sin φ₁ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have s2 : 0 < Real.sin φ₂ := Real.sin_pos_of_pos_of_lt_pi (by linarith) h2
  rw [div_lt_div_iff₀ s2 s1]
  have := cot_strictAnti h0 h12 h2
  linarith

/-- Lemma 2.1: `p ↦ R_p(θ)` is strictly increasing on `(1, ∞)`. -/
theorem R_strictMonoOn (h0 : 0 < θ) (hπ : θ < π) :
    StrictMonoOn (fun p => R p θ) (Set.Ioi 1) := by
  intro p hp q hq hpq
  simp only [Set.mem_Ioi] at hp hq
  simp only
  rw [R_eq_cot hp h0 hπ, R_eq_cot hq h0 hπ]
  have hq' : θ / q < θ / p := div_lt_div_of_pos_left h0 (by linarith) hpq
  have := cot_lt (phi_pos hq h0) hq' (lt_trans (phi_lt hp h0) hπ)
  have hs := sin_theta_pos h0 hπ
  nlinarith

theorem R_injOn (h0 : 0 < θ) (hπ : θ < π) {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (h : R p θ = R q θ) : p = q :=
  (R_strictMonoOn h0 hπ).injOn hp hq h

theorem R_two (θ : ℝ) (h0 : 0 < θ) (hπ : θ < π) : R 2 θ = 1 := by
  rw [R]
  have : (2 - 1) * θ / 2 = θ / 2 := by ring
  rw [this, div_self (ne_of_gt (sin_phi_pos (by norm_num : (1 : ℝ) < 2) h0 hπ))]

/-- Lemma 2.1: `R_p(θ) > 1` if and only if `p > 2`. -/
theorem R_gt_one_iff {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) (hπ : θ < π) :
    1 < R p θ ↔ 2 < p := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := R_strictMonoOn h0 hπ hp (by norm_num : (2 : ℝ) ∈ Set.Ioi 1) hlt
      simp only at this
      rw [R_two θ h0 hπ] at this
      linarith
    · rw [heq, R_two θ h0 hπ] at h
      linarith
  · intro h
    have := R_strictMonoOn h0 hπ (by norm_num : (2 : ℝ) ∈ Set.Ioi 1) hp h
    simp only at this
    rwa [R_two θ h0 hπ] at this

/-- `R_p(θ) = 1` only for `p = 2`. -/
theorem R_eq_one {p : ℝ} (hp : 1 < p) (h0 : 0 < θ) (hπ : θ < π) (h : R p θ = 1) : p = 2 := by
  have := R_two θ h0 hπ
  exact R_injOn h0 hπ hp (by norm_num) (by rw [h, this])

/-- The angle `φ ∈ (0, π)` with `cot φ = c`. -/
noncomputable def arccot (c : ℝ) : ℝ := π / 2 - Real.arctan c

theorem arccot_pos (c : ℝ) : 0 < arccot c := by
  rw [arccot]; linarith [Real.arctan_lt_pi_div_two c]

theorem arccot_lt_pi (c : ℝ) : arccot c < π := by
  rw [arccot]; linarith [Real.neg_pi_div_two_lt_arctan c, Real.pi_pos]

theorem cot_arccot (c : ℝ) : Real.cos (arccot c) / Real.sin (arccot c) = c := by
  rw [arccot, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.sin_arctan, Real.cos_arctan]
  have : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- Lemma 2.1, inverse: for `ρ > 0` the parameter `p = θ/φ`, `cot φ = (ρ + cos θ)/sin θ`,
satisfies `p > 1` and `R_p(θ) = ρ`. -/
noncomputable def Rinv (ρ θ : ℝ) : ℝ := θ / arccot ((ρ + Real.cos θ) / Real.sin θ)

theorem arccot_lt_theta {ρ : ℝ} (hρ : 0 < ρ) (h0 : 0 < θ) (hπ : θ < π) :
    arccot ((ρ + Real.cos θ) / Real.sin θ) < θ := by
  set φ := arccot ((ρ + Real.cos θ) / Real.sin θ) with hφ
  have hs := sin_theta_pos h0 hπ
  have hc : Real.cos φ / Real.sin φ = (ρ + Real.cos θ) / Real.sin θ := cot_arccot _
  have hgt : Real.cos θ / Real.sin θ < Real.cos φ / Real.sin φ := by
    rw [hc]
    apply div_lt_div_of_pos_right _ hs
    linarith
  by_contra hle
  push Not at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have := cot_lt h0 hlt (arccot_lt_pi _)
    linarith
  · rw [heq] at hgt
    linarith

theorem Rinv_gt_one {ρ : ℝ} (hρ : 0 < ρ) (h0 : 0 < θ) (hπ : θ < π) : 1 < Rinv ρ θ := by
  rw [Rinv, one_lt_div (arccot_pos _)]
  exact arccot_lt_theta hρ h0 hπ

theorem R_Rinv {ρ : ℝ} (hρ : 0 < ρ) (h0 : 0 < θ) (hπ : θ < π) : R (Rinv ρ θ) θ = ρ := by
  have hp := Rinv_gt_one hρ h0 hπ
  rw [R_eq_cot hp h0 hπ]
  have hφ : θ / Rinv ρ θ = arccot ((ρ + Real.cos θ) / Real.sin θ) := by
    rw [Rinv]
    have := arccot_pos ((ρ + Real.cos θ) / Real.sin θ)
    field_simp
  rw [hφ, cot_arccot]
  have hs := sin_theta_pos h0 hπ
  field_simp
  ring

/-- Lemma 2.1: `p ↦ R_p(θ)` maps `(1, ∞)` onto `(0, ∞)`. -/
theorem R_surj {ρ : ℝ} (hρ : 0 < ρ) (h0 : 0 < θ) (hπ : θ < π) : ∃ p, 1 < p ∧ R p θ = ρ :=
  ⟨Rinv ρ θ, Rinv_gt_one hρ h0 hπ, R_Rinv hρ h0 hπ⟩

/-- For `ρ + cos θ > 0`, the angle of Lemma 2.1 is `arctan (sin θ / (ρ + cos θ))`. -/
theorem arccot_eq_arctan {c : ℝ} (hc : 0 < c) : arccot c = Real.arctan c⁻¹ := by
  rw [arccot, Real.arctan_inv_of_pos hc]

/-- Remark 2.5: `R_{p/(p−1)}(θ) = 1/R_p(θ)`. -/
theorem R_conj {p : ℝ} (hp : 1 < p) : R (p / (p - 1)) θ = 1 / R p θ := by
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : p ≠ 0 := by linarith
  have e1 : (p / (p - 1) - 1) * θ / (p / (p - 1)) = θ / p := by field_simp; ring
  have e2 : θ / (p / (p - 1)) = (p - 1) * θ / p := by field_simp
  rw [R, R, e1, e2, one_div_div]

theorem conj_gt_one {p : ℝ} (hp : 1 < p) : 1 < p / (p - 1) := by
  rw [one_lt_div (by linarith)]; linarith

end

end Morley
