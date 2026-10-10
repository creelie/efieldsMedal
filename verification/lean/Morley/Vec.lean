import Mathlib

/-!
# Vectors in ℝ³

A small coordinate model of Euclidean 3-space: vectors with three real coordinates, the dot
product, the cross product and the triple product.  Identities are proved coordinatewise with
`ring`, so nothing here depends on Mathlib's normed-space API.

Main facts:
* `cross_cross_self`: `|c|² n − (c·n) c = (n·v)(c×u) − (n·u)(c×v)` for `c = u×v`, which gives
  `perp_two` (a vector orthogonal to `u` and `v` is a multiple of `u×v`);
* `unit_normal_unique`: two unit vectors orthogonal to `u`, `v` (with `u×v ≠ 0`) that are both
  positive on a vector `z` are equal;
* `frame_complete`: every vector is the sum of its components in an orthonormal frame.
-/

namespace Morley

/-- A vector, or a point, of ℝ³. -/
@[ext] structure V where
  x : ℝ
  y : ℝ
  z : ℝ

namespace V

instance : Zero V := ⟨⟨0, 0, 0⟩⟩
instance : Add V := ⟨fun u v => ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩⟩
instance : Sub V := ⟨fun u v => ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩⟩
instance : Neg V := ⟨fun u => ⟨-u.x, -u.y, -u.z⟩⟩
instance : SMul ℝ V := ⟨fun k u => ⟨k * u.x, k * u.y, k * u.z⟩⟩

@[simp] theorem zero_x : (0 : V).x = 0 := rfl
@[simp] theorem zero_y : (0 : V).y = 0 := rfl
@[simp] theorem zero_z : (0 : V).z = 0 := rfl
@[simp] theorem add_x (u v : V) : (u + v).x = u.x + v.x := rfl
@[simp] theorem add_y (u v : V) : (u + v).y = u.y + v.y := rfl
@[simp] theorem add_z (u v : V) : (u + v).z = u.z + v.z := rfl
@[simp] theorem sub_x (u v : V) : (u - v).x = u.x - v.x := rfl
@[simp] theorem sub_y (u v : V) : (u - v).y = u.y - v.y := rfl
@[simp] theorem sub_z (u v : V) : (u - v).z = u.z - v.z := rfl
@[simp] theorem neg_x (u : V) : (-u).x = -u.x := rfl
@[simp] theorem neg_y (u : V) : (-u).y = -u.y := rfl
@[simp] theorem neg_z (u : V) : (-u).z = -u.z := rfl
@[simp] theorem smul_x (k : ℝ) (u : V) : (k • u).x = k * u.x := rfl
@[simp] theorem smul_y (k : ℝ) (u : V) : (k • u).y = k * u.y := rfl
@[simp] theorem smul_z (k : ℝ) (u : V) : (k • u).z = k * u.z := rfl
@[simp] theorem mk_x (a b c : ℝ) : (V.mk a b c).x = a := rfl
@[simp] theorem mk_y (a b c : ℝ) : (V.mk a b c).y = b := rfl
@[simp] theorem mk_z (a b c : ℝ) : (V.mk a b c).z = c := rfl

/-- The dot product. -/
def dot (u v : V) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

/-- The cross product. -/
def cross (u v : V) : V :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- The squared length. -/
def sq (u : V) : ℝ := dot u u

/-- The squared distance between two points. -/
def dist2 (P Q : V) : ℝ := sq (P - Q)

end V

open V

/-- Rewrite everything into coordinates. -/
syntax "vexpand" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vexpand $[$loc]?) =>
    `(tactic| simp only [V.ext_iff, V.dot, V.cross, V.sq, V.dist2, V.add_x, V.add_y, V.add_z,
      V.sub_x, V.sub_y, V.sub_z, V.neg_x, V.neg_y, V.neg_z, V.smul_x, V.smul_y, V.smul_z,
      V.zero_x, V.zero_y, V.zero_z, V.mk_x, V.mk_y, V.mk_z] $[$loc]?)

theorem dot_comm (u v : V) : dot u v = dot v u := by vexpand; ring
theorem dot_add_right (u v w : V) : dot u (v + w) = dot u v + dot u w := by vexpand; ring
theorem dot_add_left (u v w : V) : dot (u + v) w = dot u w + dot v w := by vexpand; ring
theorem dot_sub_right (u v w : V) : dot u (v - w) = dot u v - dot u w := by vexpand; ring
theorem dot_sub_left (u v w : V) : dot (u - v) w = dot u w - dot v w := by vexpand; ring
theorem dot_smul_right (k : ℝ) (u v : V) : dot u (k • v) = k * dot u v := by vexpand; ring
theorem dot_smul_left (k : ℝ) (u v : V) : dot (k • u) v = k * dot u v := by vexpand; ring
theorem dot_neg_left (u v : V) : dot (-u) v = -dot u v := by vexpand; ring
theorem dot_zero_right (u : V) : dot u 0 = 0 := by vexpand; ring
theorem dot_self_nonneg (u : V) : 0 ≤ dot u u := by
  vexpand; nlinarith [sq_nonneg u.x, sq_nonneg u.y, sq_nonneg u.z]
theorem dot_self_eq_zero {u : V} (h : dot u u = 0) : u = 0 := by
  have hx : u.x = 0 := by
    vexpand at h; nlinarith [sq_nonneg u.x, sq_nonneg u.y, sq_nonneg u.z]
  have hy : u.y = 0 := by
    vexpand at h; nlinarith [sq_nonneg u.x, sq_nonneg u.y, sq_nonneg u.z]
  have hz : u.z = 0 := by
    vexpand at h; nlinarith [sq_nonneg u.x, sq_nonneg u.y, sq_nonneg u.z]
  ext <;> simp [hx, hy, hz]
theorem dot_self_pos {u : V} (h : u ≠ 0) : 0 < dot u u :=
  lt_of_le_of_ne (dot_self_nonneg u) (fun h' => h (dot_self_eq_zero h'.symm))

theorem dot_cross_left (u v : V) : dot u (cross u v) = 0 := by vexpand; ring
theorem dot_cross_right (u v : V) : dot v (cross u v) = 0 := by vexpand; ring
theorem cross_anticomm (u v : V) : cross v u = -cross u v := by vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `|c|² n − (c·n) c = (n·v)(c×u) − (n·u)(c×v)` for `c = u × v`. -/
theorem cross_cross_self (u v n : V) :
    dot (cross u v) (cross u v) • n - dot (cross u v) n • cross u v =
      dot n v • cross (cross u v) u - dot n u • cross (cross u v) v := by
  vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring

/-- A vector orthogonal to `u` and `v` is a multiple of `u × v`. -/
theorem perp_two {u v n : V} (hu : dot n u = 0) (hv : dot n v = 0) :
    dot (cross u v) (cross u v) • n = dot (cross u v) n • cross u v := by
  have h := cross_cross_self u v n
  rw [hu, hv] at h
  have hx := congrArg V.x h
  have hy := congrArg V.y h
  have hz := congrArg V.z h
  simp only [V.sub_x, V.sub_y, V.sub_z, V.smul_x, V.smul_y, V.smul_z] at hx hy hz
  ext <;> simp only [V.smul_x, V.smul_y, V.smul_z]
  · linear_combination hx
  · linear_combination hy
  · linear_combination hz

/-- Lagrange's identity `|u × v|² = |u|²|v|² − (u·v)²`. -/
theorem lagrange (u v : V) :
    dot (cross u v) (cross u v) = dot u u * dot v v - dot u v * dot u v := by
  vexpand; ring

/-- If `k • c = n` componentwise with `k = (c·n)/|c|²` (from `perp_two`). -/
theorem eq_smul_of_perp {c n : V} (hne : dot c c ≠ 0) (p : dot c c • n = dot c n • c) :
    n = (dot c n / dot c c) • c := by
  have px := congrArg V.x p
  have py := congrArg V.y p
  have pz := congrArg V.z p
  simp only [V.smul_x, V.smul_y, V.smul_z] at px py pz
  ext <;> simp only [V.smul_x, V.smul_y, V.smul_z] <;>
    rw [div_mul_eq_mul_div, eq_div_iff hne]
  · linear_combination px
  · linear_combination py
  · linear_combination pz

/-- A unit vector `(a/b) • c` with `b = |c|² ≠ 0` has `a² = b`. -/
theorem sq_of_unit {c : V} {a : ℝ} (hne : dot c c ≠ 0)
    (h : dot ((a / dot c c) • c) ((a / dot c c) • c) = 1) : a * a = dot c c := by
  rw [dot_smul_left, dot_smul_right, div_mul_cancel₀ a hne, div_mul_eq_mul_div,
    div_eq_one_iff_eq hne] at h
  exact h

/-- Uniqueness of the unit normal pointing to a given side. -/
theorem unit_normal_unique {u v n m z : V} (hc : cross u v ≠ 0)
    (hnu : dot n u = 0) (hnv : dot n v = 0) (hmu : dot m u = 0) (hmv : dot m v = 0)
    (hn : dot n n = 1) (hm : dot m m = 1) (hnz : 0 < dot n z) (hmz : 0 < dot m z) : n = m := by
  have hcc : 0 < dot (cross u v) (cross u v) := dot_self_pos hc
  have hne : dot (cross u v) (cross u v) ≠ 0 := ne_of_gt hcc
  have en := eq_smul_of_perp hne (perp_two hnu hnv)
  have em := eq_smul_of_perp hne (perp_two hmu hmv)
  have sn : dot (cross u v) n * dot (cross u v) n = dot (cross u v) (cross u v) := by
    apply sq_of_unit hne; rw [← en]; exact hn
  have sm : dot (cross u v) m * dot (cross u v) m = dot (cross u v) (cross u v) := by
    apply sq_of_unit hne; rw [← em]; exact hm
  have hsame : dot (cross u v) n = dot (cross u v) m := by
    have h2 : (dot (cross u v) n - dot (cross u v) m) * (dot (cross u v) n + dot (cross u v) m)
        = 0 := by linear_combination sn - sm
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · exfalso
      have hz1 := hnz
      have hz2 := hmz
      rw [en, dot_smul_left] at hz1
      rw [em, dot_smul_left] at hz2
      have hm' : dot (cross u v) m = -dot (cross u v) n := by linarith
      rw [hm', neg_div, neg_mul] at hz2
      linarith
  rw [en, em, hsame]

/-- Completeness of an orthonormal frame of ℝ³. -/
theorem frame_complete {e₁ e₂ e₃ : V} (h11 : dot e₁ e₁ = 1) (h22 : dot e₂ e₂ = 1)
    (h33 : dot e₃ e₃ = 1) (h12 : dot e₁ e₂ = 0) (h13 : dot e₁ e₃ = 0) (h23 : dot e₂ e₃ = 0)
    (w : V) : w = dot w e₁ • e₁ + dot w e₂ • e₂ + dot w e₃ • e₃ := by
  set r := w - (dot w e₁ • e₁ + dot w e₂ • e₂) with hr
  have r1 : dot r e₁ = 0 := by
    rw [hr, dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left, h11, dot_comm e₂ e₁, h12]
    ring
  have r2 : dot r e₂ = 0 := by
    rw [hr, dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left, h22, h12]; ring
  have c1 : dot e₃ e₁ = 0 := by rw [dot_comm]; exact h13
  have c2 : dot e₃ e₂ = 0 := by rw [dot_comm]; exact h23
  have hcc : dot (cross e₁ e₂) (cross e₁ e₂) = 1 := by
    rw [lagrange, h11, h22, h12]; ring
  have hne : dot (cross e₁ e₂) (cross e₁ e₂) ≠ 0 := by rw [hcc]; norm_num
  have pr := eq_smul_of_perp hne (perp_two r1 r2)
  have p3 := eq_smul_of_perp hne (perp_two c1 c2)
  rw [hcc, div_one] at pr p3
  have k3 : dot (cross e₁ e₂) e₃ * dot (cross e₁ e₂) e₃ = 1 := by
    have h := sq_of_unit hne (a := dot (cross e₁ e₂) e₃) (by rw [hcc, div_one, ← p3]; exact h33)
    rw [hcc] at h; exact h
  have hre3 : dot r e₃ = dot w e₃ := by
    rw [hr, dot_sub_left, dot_add_left, dot_smul_left, dot_smul_left, h13, h23]; ring
  -- r = (c·r) c = (c·r)(c·e₃) e₃, so r = (r·e₃) e₃
  have hrr : r = dot r e₃ • e₃ := by
    have hdot : dot r e₃ = dot (cross e₁ e₂) r * dot (cross e₁ e₂) e₃ := by
      conv_lhs => rw [pr]
      rw [dot_smul_left]
    rw [hdot]
    have px := congrArg V.x pr
    have py := congrArg V.y pr
    have pz := congrArg V.z pr
    have qx := congrArg V.x p3
    have qy := congrArg V.y p3
    have qz := congrArg V.z p3
    simp only [V.smul_x, V.smul_y, V.smul_z] at px py pz qx qy qz
    ext <;> simp only [V.smul_x, V.smul_y, V.smul_z]
    · linear_combination px - (dot (cross e₁ e₂) r * dot (cross e₁ e₂) e₃) * qx
        - (dot (cross e₁ e₂) r * (cross e₁ e₂).x) * k3
    · linear_combination py - (dot (cross e₁ e₂) r * dot (cross e₁ e₂) e₃) * qy
        - (dot (cross e₁ e₂) r * (cross e₁ e₂).y) * k3
    · linear_combination pz - (dot (cross e₁ e₂) r * dot (cross e₁ e₂) e₃) * qz
        - (dot (cross e₁ e₂) r * (cross e₁ e₂).z) * k3
  have hw : w = r + (dot w e₁ • e₁ + dot w e₂ • e₂) := by
    rw [hr]; vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring
  calc w = r + (dot w e₁ • e₁ + dot w e₂ • e₂) := hw
    _ = dot r e₃ • e₃ + (dot w e₁ • e₁ + dot w e₂ • e₂) := by rw [← hrr]
    _ = dot w e₁ • e₁ + dot w e₂ • e₂ + dot w e₃ • e₃ := by
      rw [hre3]; vexpand; refine ⟨?_, ?_, ?_⟩ <;> ring

end Morley
