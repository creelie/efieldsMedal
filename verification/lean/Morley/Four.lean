import Morley.Examples

/-!
# Section 4: Theorem 1.7, quadrisecting planes

* `theorem_1_7_box`: for the box tetrahedron (1.1), `M_{4,4,4}` is regular iff `a = b = c`;
* `box_form`: every isosceles tetrahedron is carried to a box tetrahedron (1.1) by an isometry
  (through its centroid and the half-bimedians, which are pairwise orthogonal);
* `theorem_1_7`: an isosceles tetrahedron has a regular `M_{4,4,4}` iff it is regular.
-/

open Real

namespace Morley
open V

section
variable {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
include ha hb hc

/-- The cosines (3.1), multiplied out. -/
theorem cos_box (X Y : Fin 4) (hXY : X ≠ Y) :
    Real.cos ((box a b c ha hb hc).θ X Y) * (a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2) =
      -(sx X * sx Y * a⁻¹ ^ 2 + sy X * sy Y * b⁻¹ ^ 2 + sz X * sz Y * c⁻¹ ^ 2) := by
  have hS : 0 < a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2 := by positivity
  rw [Tet.cos_θ _ X Y hXY, nrm_box ha hb hc, nrm_box ha hb hc, dot_mvec_mvec ha hb hc,
    neg_mul, div_mul_cancel₀ _ (ne_of_gt hS)]

/-- For an edge with parameter `4`, by (3.3): `(L_Y − L_A)² = 2(1 + cos θ) L_A²` at `A'`. -/
theorem key_four {par : Fin 3 → ℝ} (hpar : ∀ i, 1 < par i) (Y : Fin 4) (hY : Y ≠ 0)
    (hp : par (ptype 0 Y) = 4) :
    (Lf a b c Y ((box a b c ha hb hc).mv par 0) - Lf a b c 0 ((box a b c ha hb hc).mv par 0)) ^ 2
      = 2 * (1 + Real.cos ((box a b c ha hb hc).θ 0 Y)) *
        Lf a b c 0 ((box a b c ha hb hc).mv par 0) ^ 2 := by
  have h0 := (box a b c ha hb hc).θ_pos 0 Y (Ne.symm hY)
  have hπ := (box a b c ha hb hc).θ_lt_pi 0 Y (Ne.symm hY)
  have m := (box a b c ha hb hc).mv_eqs hpar 0 Y
  have hN := ne_of_gt (Nb_pos ha hb hc)
  rw [d_box ha hb hc, d_box ha hb hc, (box a b c ha hb hc).ρ_ne hY, hp, R4_closed h0 hπ,
    mul_div_assoc', div_left_inj' hN] at m
  have hs : Real.sqrt (2 * (1 + Real.cos ((box a b c ha hb hc).θ 0 Y))) ^ 2 =
      2 * (1 + Real.cos ((box a b c ha hb hc).θ 0 Y)) :=
    Real.sq_sqrt (by nlinarith [Real.neg_one_le_cos ((box a b c ha hb hc).θ 0 Y)])
  linear_combination Lf a b c 0 ((box a b c ha hb hc).mv par 0) ^ 2 * hs +
    (2 * Real.sqrt (2 * (1 + Real.cos ((box a b c ha hb hc).θ 0 Y))) *
        Lf a b c 0 ((box a b c ha hb hc).mv par 0) +
      (Lf a b c Y ((box a b c ha hb hc).mv par 0) -
        (1 + Real.sqrt (2 * (1 + Real.cos ((box a b c ha hb hc).θ 0 Y)))) *
          Lf a b c 0 ((box a b c ha hb hc).mv par 0))) * m

/-- Theorem 1.7 for the box tetrahedron (1.1): `M_{4,4,4}(ABCD)` is regular iff `a = b = c`. -/
theorem theorem_1_7_box :
    Regular ((box a b c ha hb hc).mv (fun _ => 4)) ↔ a = b ∧ b = c := by
  have h4 : ∀ i : Fin 3, 1 < (fun _ => (4 : ℝ)) i := fun _ => by norm_num
  have hα := inv_pos.2 ha
  have hβ := inv_pos.2 hb
  have hγ := inv_pos.2 hc
  rw [theorem_1_3a ha hb hc h4]
  constructor
  · rintro ⟨hne, k, t, hQ⟩
    have hL0 : 0 < Lf a b c 0 ((box a b c ha hb hc).mv (fun _ => 4) 0) :=
      ((interior_box ha hb hc _).1 ((box a b c ha hb hc).mv_interior h4 0)) 0
    have K1 := key_four ha hb hc h4 1 (by decide) rfl
    have K2 := key_four ha hb hc h4 2 (by decide) rfl
    have K3 := key_four ha hb hc h4 3 (by decide) rfl
    have H1 := cos_box ha hb hc 0 1 (by decide)
    have H2 := cos_box ha hb hc 0 2 (by decide)
    have H3 := cos_box ha hb hc 0 3 (by decide)
    simp only [sx0, sx1, sx2, sx3, sy0, sy1, sy2, sy3, sz0, sz1, sz2, sz3] at H1 H2 H3
    rw [hQ] at K1 K2 K3 hL0
    have d1 : Lf a b c 1 (t • dir k) - Lf a b c 0 (t • dir k) =
        -2 * t * (sy k * b⁻¹ + sz k * c⁻¹) := by
      simp only [Lf, dir, V.smul_x, V.smul_y, V.smul_z, sx0, sx1, sy0, sy1, sz0, sz1]; ring
    have d2 : Lf a b c 2 (t • dir k) - Lf a b c 0 (t • dir k) =
        -2 * t * (sx k * a⁻¹ + sz k * c⁻¹) := by
      simp only [Lf, dir, V.smul_x, V.smul_y, V.smul_z, sx0, sx2, sy0, sy2, sz0, sz2]; ring
    have d3 : Lf a b c 3 (t • dir k) - Lf a b c 0 (t • dir k) =
        -2 * t * (sx k * a⁻¹ + sy k * b⁻¹) := by
      simp only [Lf, dir, V.smul_x, V.smul_y, V.smul_z, sx0, sx3, sy0, sy3, sz0, sz3]; ring
    rw [d1] at K1
    rw [d2] at K2
    rw [d3] at K3
    set L := Lf a b c 0 (t • dir k) with hL
    set S := a⁻¹ ^ 2 + b⁻¹ ^ 2 + c⁻¹ ^ 2 with hS
    have E1 : (b⁻¹ ^ 2 + c⁻¹ ^ 2) * L ^ 2 = S * t ^ 2 * (sy k * b⁻¹ + sz k * c⁻¹) ^ 2 := by
      linear_combination (-S / 4) * K1 - (L ^ 2 / 2) * H1
    have E2 : (a⁻¹ ^ 2 + c⁻¹ ^ 2) * L ^ 2 = S * t ^ 2 * (sx k * a⁻¹ + sz k * c⁻¹) ^ 2 := by
      linear_combination (-S / 4) * K2 - (L ^ 2 / 2) * H2
    have E3 : (a⁻¹ ^ 2 + b⁻¹ ^ 2) * L ^ 2 = S * t ^ 2 * (sx k * a⁻¹ + sy k * b⁻¹) ^ 2 := by
      linear_combination (-S / 4) * K3 - (L ^ 2 / 2) * H3
    have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hL0)
    have quot : ∀ q w : ℝ, q * L ^ 2 = S * t ^ 2 * w ^ 2 → q = S * t ^ 2 / L ^ 2 * w ^ 2 := by
      intro q w h
      rw [div_mul_eq_mul_div, eq_div_iff hL2]
      linear_combination h
    have q1 := quot _ _ E1
    have q2 := quot _ _ E2
    have q3 := quot _ _ E3
    rcases fin4_cases k with rfl | rfl | rfl | rfl
    · simp only [sx0, sy0, sz0, one_mul] at q1 q2 q3
      have pbg : (b⁻¹ + c⁻¹) ^ 2 ≠ 0 := by positivity
      have pag : (a⁻¹ + c⁻¹) ^ 2 ≠ 0 := by positivity
      have pab : (a⁻¹ + b⁻¹) ^ 2 ≠ 0 := by positivity
      have h1 : (b⁻¹ ^ 2 + c⁻¹ ^ 2) / (b⁻¹ + c⁻¹) ^ 2 = (a⁻¹ ^ 2 + c⁻¹ ^ 2) / (a⁻¹ + c⁻¹) ^ 2 := by
        rw [q1, q2, mul_div_cancel_right₀ _ pbg, mul_div_cancel_right₀ _ pag]
      have h2 : (a⁻¹ ^ 2 + c⁻¹ ^ 2) / (a⁻¹ + c⁻¹) ^ 2 = (a⁻¹ ^ 2 + b⁻¹ ^ 2) / (a⁻¹ + b⁻¹) ^ 2 := by
        rw [q2, q3, mul_div_cancel_right₀ _ pag, mul_div_cancel_right₀ _ pab]
      obtain ⟨e1, e2⟩ := theorem_four_algebra hα hβ hγ h1 h2
      exact ⟨inv_inj.1 e1, inv_inj.1 e2⟩
    · simp only [sx1, sy1, sz1] at q1 q2
      exact (no_common_quotient (k := S * t ^ 2 / L ^ 2) hβ hγ hα hγ (by rw [q1]; ring) (by rw [q2]; ring)).elim
    · simp only [sx2, sy2, sz2] at q1 q2
      exact (no_common_quotient (k := S * t ^ 2 / L ^ 2) hα hγ hβ hγ (by rw [q2]; ring) (by rw [q1]; ring)).elim
    · simp only [sx3, sy3, sz3] at q1 q3
      exact (no_common_quotient (k := S * t ^ 2 / L ^ 2) hα hβ hβ hγ (by rw [q3]; ring) (by rw [q1]; ring)).elim
  · rintro ⟨rfl, rfl⟩
    set Q := (box a a a ha hb hc).mv (fun _ => 4) 0 with hQ
    have hN := ne_of_gt (Nb_pos ha hb hc)
    have m : ∀ Y : Fin 4, Y ≠ 0 →
        Lf a a a Y Q = R 4 ((box a a a ha hb hc).θ 0 Y) * Lf a a a 0 Q := by
      intro Y hY
      have := (box a a a ha hb hc).mv_eqs h4 0 Y
      rw [d_box ha hb hc, d_box ha hb hc, (box a a a ha hb hc).ρ_ne hY, mul_div_assoc',
        div_left_inj' hN] at this
      exact this
    have t12 : (box a a a ha hb hc).θ 0 1 = (box a a a ha hb hc).θ 0 2 := by
      rw [θ_box ha hb hc, θ_box ha hb hc]
      congr 1
      simp only [sx0, sx1, sx2, sy0, sy1, sy2, sz0, sz1, sz2]
      ring
    have t13 : (box a a a ha hb hc).θ 0 1 = (box a a a ha hb hc).θ 0 3 := by
      rw [θ_box ha hb hc, θ_box ha hb hc]
      congr 1
      simp only [sx0, sx1, sx3, sy0, sy1, sy3, sz0, sz1, sz3]
      ring
    have m1 := m 1 (by decide)
    have m2 := m 2 (by decide)
    have m3 := m 3 (by decide)
    rw [← t12] at m2
    rw [← t13] at m3
    have ha0 : a⁻¹ ≠ 0 := ne_of_gt hα
    have exy : Q.x = Q.y := by
      have e : Lf a a a 1 Q - Lf a a a 2 Q = 2 * a⁻¹ * (Q.x - Q.y) := by
        simp only [Lf, sx1, sx2, sy1, sy2, sz1, sz2]; ring
      rw [m1, m2, sub_self] at e
      have := mul_eq_zero.1 e.symm
      rcases this with h | h
      · exfalso; apply ha0; linarith
      · linarith
    have eyz : Q.y = Q.z := by
      have e : Lf a a a 2 Q - Lf a a a 3 Q = 2 * a⁻¹ * (Q.y - Q.z) := by
        simp only [Lf, sx2, sx3, sy2, sy3, sz2, sz3]; ring
      rw [m2, m3, sub_self] at e
      have := mul_eq_zero.1 e.symm
      rcases this with h | h
      · exfalso; apply ha0; linarith
      · linarith
    refine ⟨?_, 0, Q.x, ?_⟩
    · intro h0
      have e1 := m1
      rw [h0] at e1
      simp only [Lf, V.zero_x, V.zero_y, V.zero_z, mul_zero, add_zero] at e1
      have hR : R 4 ((box a a a ha hb hc).θ 0 1) = 1 := by linarith
      have := R_eq_one (by norm_num : (1 : ℝ) < 4)
        ((box a a a ha hb hc).θ_pos 0 1 (by decide))
        ((box a a a ha hb hc).θ_lt_pi 0 1 (by decide)) hR
      norm_num at this
    · ext <;> simp [dir, exy, eyz]

end

/-! ### Every isosceles tetrahedron is a box tetrahedron -/

/-- A tetrahedron is isosceles if its opposite edges have equal lengths. -/
def Isosceles (T : Tet) : Prop :=
  dist2 (T.P 0) (T.P 1) = dist2 (T.P 2) (T.P 3) ∧ dist2 (T.P 0) (T.P 2) = dist2 (T.P 1) (T.P 3) ∧
    dist2 (T.P 0) (T.P 3) = dist2 (T.P 1) (T.P 2)

/-- The centroid and the half-bimedians `(A ± B ∓ C ∓ D)/4`. -/
noncomputable def cen (T : Tet) : V := (1 / 4 : ℝ) • (T.P 0 + T.P 1 + T.P 2 + T.P 3)
noncomputable def bm1 (T : Tet) : V := (1 / 4 : ℝ) • (T.P 0 + T.P 1 - T.P 2 - T.P 3)
noncomputable def bm2 (T : Tet) : V := (1 / 4 : ℝ) • (T.P 0 - T.P 1 + T.P 2 - T.P 3)
noncomputable def bm3 (T : Tet) : V := (1 / 4 : ℝ) • (T.P 0 - T.P 1 - T.P 2 + T.P 3)

theorem P_sub_cen (T : Tet) (X : Fin 4) :
    T.P X - cen T = sx X • bm1 T + sy X • bm2 T + sz X • bm3 T := by
  rcases fin4_cases X with rfl | rfl | rfl | rfl <;>
    simp only [cen, bm1, bm2, bm3, sx0, sx1, sx2, sx3, sy0, sy1, sy2, sy3, sz0, sz1, sz2, sz3] <;>
    vexpand <;> refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Every isosceles tetrahedron is carried by an isometry to a tetrahedron (1.1), vertex by vertex:
the half-bimedians are pairwise orthogonal, and their lengths are `a`, `b`, `c`. -/
theorem box_form (T : Tet) (hT : Isosceles T) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ ∃ g : Iso, ∀ X, g.app (T.P X) = boxP a b c X := by
  obtain ⟨h01, h02, h03⟩ := hT
  have o23 : dot (bm2 T) (bm3 T) = 0 := by
    have e : dist2 (T.P 0) (T.P 1) - dist2 (T.P 2) (T.P 3) = 16 * dot (bm2 T) (bm3 T) := by
      simp only [dist2, V.sq, bm2, bm3]; vexpand; ring
    linarith
  have o13 : dot (bm1 T) (bm3 T) = 0 := by
    have e : dist2 (T.P 0) (T.P 2) - dist2 (T.P 1) (T.P 3) = 16 * dot (bm1 T) (bm3 T) := by
      simp only [dist2, V.sq, bm1, bm3]; vexpand; ring
    linarith
  have o12 : dot (bm1 T) (bm2 T) = 0 := by
    have e : dist2 (T.P 0) (T.P 3) - dist2 (T.P 1) (T.P 2) = 16 * dot (bm1 T) (bm2 T) := by
      simp only [dist2, V.sq, bm1, bm2]; vexpand; ring
    linarith
  have htrip : dot (T.P 1 - T.P 0) (cross (T.P 2 - T.P 0) (T.P 3 - T.P 0)) =
      -16 * dot (bm1 T) (cross (bm2 T) (bm3 T)) := by
    simp only [bm1, bm2, bm3]; vexpand; ring
  have hnd := T.nondeg
  rw [htrip] at hnd
  have n1 : bm1 T ≠ 0 := by intro h; apply hnd; rw [h]; vexpand; ring
  have n2 : bm2 T ≠ 0 := by intro h; apply hnd; rw [h]; vexpand; ring
  have n3 : bm3 T ≠ 0 := by intro h; apply hnd; rw [h]; vexpand; ring
  have p1 := dot_self_pos n1
  have p2 := dot_self_pos n2
  have p3 := dot_self_pos n3
  obtain ⟨a, ha, ha2⟩ : ∃ a : ℝ, 0 < a ∧ dot (bm1 T) (bm1 T) = a * a :=
    ⟨_, Real.sqrt_pos.2 p1, (Real.mul_self_sqrt (le_of_lt p1)).symm⟩
  obtain ⟨b, hb, hb2⟩ : ∃ b : ℝ, 0 < b ∧ dot (bm2 T) (bm2 T) = b * b :=
    ⟨_, Real.sqrt_pos.2 p2, (Real.mul_self_sqrt (le_of_lt p2)).symm⟩
  obtain ⟨c, hc, hc2⟩ : ∃ c : ℝ, 0 < c ∧ dot (bm3 T) (bm3 T) = c * c :=
    ⟨_, Real.sqrt_pos.2 p3, (Real.mul_self_sqrt (le_of_lt p3)).symm⟩
  have o21 : dot (bm2 T) (bm1 T) = 0 := by rw [dot_comm]; exact o12
  have o31 : dot (bm3 T) (bm1 T) = 0 := by rw [dot_comm]; exact o13
  have o32 : dot (bm3 T) (bm2 T) = 0 := by rw [dot_comm]; exact o23
  have unit : ∀ (k : ℝ) (u : V), 0 < k → dot u u = k * k → dot (k⁻¹ • u) (k⁻¹ • u) = 1 := by
    intro k u hk hu
    rw [dot_smul_left, dot_smul_right, hu]
    field_simp
  let g : Iso :=
    { r₁ := a⁻¹ • bm1 T, r₂ := b⁻¹ • bm2 T, r₃ := c⁻¹ • bm3 T, o := cen T, o' := 0
      h11 := unit a _ ha ha2
      h22 := unit b _ hb hb2
      h33 := unit c _ hc hc2
      h12 := by rw [dot_smul_left, dot_smul_right, o12]; ring
      h13 := by rw [dot_smul_left, dot_smul_right, o13]; ring
      h23 := by rw [dot_smul_left, dot_smul_right, o23]; ring }
  have c1 : ∀ X, dot (a⁻¹ • bm1 T) (T.P X - cen T) = sx X * a := by
    intro X
    rw [P_sub_cen, dot_smul_left, dot_add_right, dot_add_right, dot_smul_right, dot_smul_right,
      dot_smul_right, o12, o13, ha2,
      show a⁻¹ * (sx X * (a * a) + sy X * 0 + sz X * 0) = sx X * a * (a⁻¹ * a) by ring,
      inv_mul_cancel₀ (ne_of_gt ha), mul_one]
  have c2 : ∀ X, dot (b⁻¹ • bm2 T) (T.P X - cen T) = sy X * b := by
    intro X
    rw [P_sub_cen, dot_smul_left, dot_add_right, dot_add_right, dot_smul_right, dot_smul_right,
      dot_smul_right, o21, o23, hb2,
      show b⁻¹ * (sx X * 0 + sy X * (b * b) + sz X * 0) = sy X * b * (b⁻¹ * b) by ring,
      inv_mul_cancel₀ (ne_of_gt hb), mul_one]
  have c3 : ∀ X, dot (c⁻¹ • bm3 T) (T.P X - cen T) = sz X * c := by
    intro X
    rw [P_sub_cen, dot_smul_left, dot_add_right, dot_add_right, dot_smul_right, dot_smul_right,
      dot_smul_right, o31, o32, hc2,
      show c⁻¹ * (sx X * 0 + sy X * 0 + sz X * (c * c)) = sz X * c * (c⁻¹ * c) by ring,
      inv_mul_cancel₀ (ne_of_gt hc), mul_one]
  refine ⟨a, b, c, ha, hb, hc, g, fun X => ?_⟩
  simp only [Iso.app, Iso.lin, g, boxP]
  ext
  · simp only [V.add_x, V.zero_x, add_zero]; exact c1 X
  · simp only [V.add_y, V.zero_y, add_zero]; exact c2 X
  · simp only [V.add_z, V.zero_z, add_zero]; exact c3 X

/-- Distances, and hence regularity, are preserved by isometries. -/
theorem regular_iso (g : Iso) (Q : Fin 4 → V) : Regular (fun k => g.app (Q k)) ↔ Regular Q := by
  simp only [Regular, Iso.dist2_app]

theorem regular_boxP {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Regular (boxP a b c) ↔ a = b ∧ b = c := by
  have e : boxP a b c = fun k => (⟨sx k * a, sy k * b, sz k * c⟩ : V) := rfl
  rw [e, regular_signs]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, rfl, rfl⟩
    intro h
    have := congrArg V.x h
    simp only [V.mk_x, V.zero_x] at this
    linarith

/-- Theorem 1.7: an isosceles tetrahedron has a regular `M_{4,4,4}(ABCD)` if and only if it is
regular. -/
theorem theorem_1_7 (T : Tet) (hT : Isosceles T) :
    Regular (T.mv (fun _ => 4)) ↔ Regular T.P := by
  obtain ⟨a, b, c, ha, hb, hc, g, hg⟩ := box_form T hT
  have h4 : ∀ i : Fin 3, 1 < (fun _ => (4 : ℝ)) i := fun _ => by norm_num
  have hm : ∀ X, g.app (T.mv (fun _ => 4) X) = (box a b c ha hb hc).mv (fun _ => 4) X :=
    fun X => mv_iso (σ := id) (T' := box a b c ha hb hc) Function.injective_id (fun X => hg X)
      h4 h4 (fun _ _ => rfl) X
  rw [← regular_iso g (T.mv _),
    show (fun k => g.app (T.mv (fun _ => (4 : ℝ)) k)) = (box a b c ha hb hc).mv (fun _ => 4)
      from funext hm,
    theorem_1_7_box ha hb hc, ← regular_boxP ha hb hc, ← regular_iso g T.P,
    show (fun k => g.app (T.P k)) = boxP a b c from funext hg]

end Morley
