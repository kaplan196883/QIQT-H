/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE SPHERE GH LIMIT — finite lat-long clouds converge to the intrinsic sphere (brick S2,
sphere capstone)

Brick S2 of the SPHERE track (`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`).
Brick S1 (`QIQTH/SphereMetric.lean`) built the intrinsic sphere — the unit sphere of `ℝ³`
with the great-circle metric `dist p q = arccos ⟪p, q⟫` — as a compact metric space whose
NON-FLATNESS is a THEOREM (the midpoint obstruction: no distance-preserving map into any
real inner-product space, `sphere_no_isometric_embedding_into_inner`).  This file completes
the brick pair by exhibiting that smooth curved space as a **Gromov–Hausdorff limit of
finite point clouds**: the lat-long grids `SphereGrid m` — two poles plus `m·(m+1)` interior
grid points at latitudes `i·π/(m+1)` (`i = 1, …, m`) and azimuths `j·2π/(m+1)`
(`j = 0, …, m`) — satisfy

    toGHSpace (SphereGrid m) ⟶ toGHSpace IntrinsicSphere   (`sphereGrid_toGHSpace_tendsto_sphere`)

via the quantitative bound `ghDist (SphereGrid m) IntrinsicSphere ≤ 3π²/(4(m+1))`
(`ghDist_sphereGrid_le`): the grid embedding `gridToSphere` is an EXACT isometry
(`gridToSphere_isometry`, the grid carries the pullback metric) whose image is a
`3π²/(4(m+1))`-net of the sphere (`sphere_net`, riding S1's chord→angle bridge
`angle_le_pi_div_two_mul_chord` — latitude rounds to the nearest parallel, azimuth rounds
wrap-aware modulo `2π`, and the two poles absorb the coordinate degeneracy of the chart).
This is the program's first **SMOOTH curved-space GH limit**: after the flat cube/torus, the
CAT(0) tripod, and the cone (whose positive curvature is concentrated at ONE point), the
finite-cloud machine now reaches a space that is curved EVERYWHERE.

## Scope firewall (MANDATORY)

* **The finite clouds carry the INDUCED (pullback) metric** — they are exact isometric
  SAMPLES of the sphere, like the cone's polar grids — **NOT an intrinsic graph-geodesic
  (hop-count) metric: the intrinsic rounding-walk construction on the curved sphere is the
  CITED frontier, exactly as for the cone.**
* **What is FORMALIZED about curvature is S1's midpoint obstruction** (no inner-product
  embedding), NOT a Riemann/sectional-curvature tensor — "constant curvature `+1`
  everywhere" is the citation, not a Lean theorem.
* **The sphere and its geometry are INPUTS** — a chosen target space transported into the
  formal system; nothing here is EMERGENCE of a sphere from quantum data.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.SphereMetric
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Round

namespace QIQTH.SphereGH

open QIQTH.SphereMetric QIQTH.SphereMetric.IntrinsicSphere Filter Topology
open scoped RealInnerProductSpace

/-! ## Part 1 — the spherical-coordinate embedding vector

`sVec θ φ = (sin θ cos φ, sin θ sin φ, cos θ)` — latitude `θ` measured from the north pole,
azimuth `φ`.  Always a unit vector. -/

/-- **The spherical-coordinate unit vector** `(sin θ cos φ, sin θ sin φ, cos θ)`. -/
noncomputable def sVec (θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

@[simp] lemma sVec_apply_zero (θ φ : ℝ) : sVec θ φ 0 = Real.sin θ * Real.cos φ := rfl

@[simp] lemma sVec_apply_one (θ φ : ℝ) : sVec θ φ 1 = Real.sin θ * Real.sin φ := rfl

@[simp] lemma sVec_apply_two (θ φ : ℝ) : sVec θ φ 2 = Real.cos θ := rfl

/-- `sVec` is a unit vector (Pythagoras twice). -/
lemma norm_sVec (θ φ : ℝ) : ‖sVec θ φ‖ = 1 := by
  have h2 : ‖sVec θ φ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [sVec_apply_zero, sVec_apply_one, sVec_apply_two, Real.norm_eq_abs, sq_abs]
    have h1 := Real.sin_sq_add_cos_sq φ
    have h2 := Real.sin_sq_add_cos_sq θ
    linear_combination (Real.sin θ) ^ 2 * h1 + h2
  calc ‖sVec θ φ‖ = Real.sqrt (‖sVec θ φ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 1 := by rw [h2]
    _ = 1 := Real.sqrt_one

/-- `sVec θ` is `2π`-periodic in the azimuth (whole turns are invisible). -/
lemma sVec_add_int_mul_two_pi (θ x : ℝ) (n : ℤ) :
    sVec θ (x + (n : ℝ) * (2 * Real.pi)) = sVec θ x := by
  simp only [sVec, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-! ## Part 2 — the workhorse inner-product and chord identities -/

/-- The quadratic cosine bound `1 − cos δ ≤ δ²/2` (restated from S1, where it is private). -/
private lemma one_sub_cos_le_half_sq (δ : ℝ) : 1 - Real.cos δ ≤ δ ^ 2 / 2 := by
  have h1 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (δ / 2)
    rwa [show 2 * (δ / 2) = δ by ring] at h
  have h2 : Real.sin (δ / 2) ^ 2 ≤ (δ / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := δ / 2)
    have h3 := mul_self_le_mul_self (abs_nonneg _) h
    rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at h3
  nlinarith [h1, h2]

/-- **The spherical inner-product identity**:
`⟪sVec θ φ, sVec θ' φ'⟫ = sin θ sin θ' cos (φ − φ') + cos θ cos θ'`. -/
lemma inner_sVec (θ θ' φ φ' : ℝ) :
    ⟪sVec θ φ, sVec θ' φ'⟫ =
      Real.sin θ * Real.sin θ' * Real.cos (φ - φ') + Real.cos θ * Real.cos θ' := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [sVec_apply_zero, sVec_apply_one, sVec_apply_two, RCLike.inner_apply,
    conj_trivial]
  rw [Real.cos_sub]
  ring

/-- Same azimuth: the inner product is the cosine of the latitude difference (the two points
lie on a common meridian). -/
lemma inner_sVec_same_phi (θ θ' φ : ℝ) :
    ⟪sVec θ φ, sVec θ' φ⟫ = Real.cos (θ - θ') := by
  rw [inner_sVec, sub_self, Real.cos_zero, Real.cos_sub]
  ring

/-- Chord squared between two spherical points, via the inner product. -/
lemma chord_sq_sVec (θ θ' φ φ' : ℝ) :
    ‖sVec θ φ - sVec θ' φ'‖ ^ 2 = 2 - 2 * ⟪sVec θ φ, sVec θ' φ'⟫ := by
  rw [norm_sub_sq_real, norm_sVec, norm_sVec]
  ring

private lemma norm_le_of_sq_le_sq {v : EuclideanSpace ℝ (Fin 3)} {c : ℝ} (hc : 0 ≤ c)
    (h : ‖v‖ ^ 2 ≤ c ^ 2) : ‖v‖ ≤ c := by
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h
    _ = c := Real.sqrt_sq hc

/-- **Latitude Lipschitz bound**: moving along a meridian, the chord is at most the latitude
gap (`2 − 2cos Δθ ≤ Δθ²`). -/
lemma chord_sVec_lat_le (θ θ' φ : ℝ) : ‖sVec θ φ - sVec θ' φ‖ ≤ |θ - θ'| := by
  refine norm_le_of_sq_le_sq (abs_nonneg _) ?_
  rw [chord_sq_sVec, inner_sVec_same_phi, sq_abs]
  have h1 := one_sub_cos_le_half_sq (θ - θ')
  linarith

/-- **Azimuth Lipschitz bound**: moving along a parallel, the chord is at most the azimuth
gap (`2 sin²θ (1 − cos Δφ) ≤ Δφ²` since `sin²θ ≤ 1`). -/
lemma chord_sVec_azi_le (θ φ φ' : ℝ) : ‖sVec θ φ - sVec θ φ'‖ ≤ |φ - φ'| := by
  refine norm_le_of_sq_le_sq (abs_nonneg _) ?_
  rw [chord_sq_sVec, inner_sVec, sq_abs]
  have h1 := one_sub_cos_le_half_sq (φ - φ')
  have h2 := Real.sin_sq_add_cos_sq θ
  have h3 : Real.sin θ ^ 2 * (1 - Real.cos (φ - φ')) ≤ Real.sin θ ^ 2 * ((φ - φ') ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have h4 : Real.sin θ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos θ)]
  nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg (φ - φ')), sq_nonneg (φ - φ')]

/-- The inner product of any sphere point with the NORTH pole vector `sVec 0 0 = (0,0,1)` is
its third coordinate. -/
private lemma inner_vec_north (p : IntrinsicSphere) : ⟪p.vec, sVec 0 0⟫ = p.vec 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp [RCLike.inner_apply]

/-- The inner product of any sphere point with the SOUTH pole vector `sVec π 0 = (0,0,−1)`
is minus its third coordinate. -/
private lemma inner_vec_south (p : IntrinsicSphere) :
    ⟪p.vec, sVec Real.pi 0⟫ = -(p.vec 2) := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp [RCLike.inner_apply]

/-- The squares of the coordinates of a sphere point sum to `1`. -/
private lemma sum_sq_coords (p : IntrinsicSphere) :
    (p.vec 0) ^ 2 + (p.vec 1) ^ 2 + (p.vec 2) ^ 2 = 1 := by
  have h2 : ‖p.vec‖ ^ 2 = 1 := by rw [p.norm_vec]; norm_num
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three] at h2
  simpa [Real.norm_eq_abs, sq_abs] using h2

/-! ## Part 3 — the finite lat-long cloud and its pullback metric

Two poles (`Sum.inl false` = north, `Sum.inl true` = south) plus `m·(m+1)` interior grid
points `Sum.inr (i, j)`: latitude index `i ∈ {1, …, m}` (a `Fin (m+2)` avoiding both
endpoints), azimuth index `j ∈ {0, …, m}` (a `Fin (m+1)`, spacing `2π/(m+1)`). -/

/-- **The finite lat-long grid**: two poles plus `m·(m+1)` interior points at latitudes
`i·π/(m+1)` (`i = 1, …, m`) and azimuths `j·2π/(m+1)` (`j = 0, …, m`).  Carries the pullback
metric below. -/
def SphereGrid (m : ℕ) : Type :=
  Bool ⊕ ({i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1} × Fin (m + 1))

instance instNonemptySphereGrid (m : ℕ) : Nonempty (SphereGrid m) := ⟨Sum.inl false⟩

instance instFiniteSphereGrid (m : ℕ) : Finite (SphereGrid m) :=
  inferInstanceAs (Finite (Bool ⊕ ({i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1} × Fin (m + 1))))

/-- The latitude `i·π/(m+1) ∈ (0, π)` of the `i`-th parallel. -/
noncomputable def gridLat (m : ℕ) (i : {i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1}) : ℝ :=
  (i.1.1 : ℝ) * Real.pi / ((m : ℝ) + 1)

/-- The azimuth `j·2π/(m+1) ∈ [0, 2π)` of the `j`-th meridian. -/
noncomputable def gridAz (m : ℕ) (j : Fin (m + 1)) : ℝ :=
  (j.1 : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)

lemma gridLat_pos (m : ℕ) (i : {i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1}) :
    0 < gridLat m i := by
  have h1 : 0 < i.1.1 := Nat.pos_of_ne_zero i.2.1
  have h1' : (0 : ℝ) < (i.1.1 : ℝ) := by exact_mod_cast h1
  show (0 : ℝ) < (i.1.1 : ℝ) * Real.pi / ((m : ℝ) + 1)
  exact div_pos (mul_pos h1' Real.pi_pos) (by positivity)

lemma gridLat_lt_pi (m : ℕ) (i : {i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1}) :
    gridLat m i < Real.pi := by
  have h1 : i.1.1 ≤ m := by
    have h2 : i.1.1 < m + 2 := i.1.2
    have h3 := i.2.2
    omega
  have h1' : (i.1.1 : ℝ) < (m : ℝ) + 1 := by
    have : (i.1.1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  show (i.1.1 : ℝ) * Real.pi / ((m : ℝ) + 1) < Real.pi
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right h1' Real.pi_pos]

lemma gridLat_mem_Icc (m : ℕ) (i : {i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1}) :
    gridLat m i ∈ Set.Icc 0 Real.pi :=
  Set.mem_Icc.mpr ⟨(gridLat_pos m i).le, (gridLat_lt_pi m i).le⟩

lemma gridAz_nonneg (m : ℕ) (j : Fin (m + 1)) : 0 ≤ gridAz m j :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (by positivity)

lemma gridAz_lt_two_pi (m : ℕ) (j : Fin (m + 1)) : gridAz m j < 2 * Real.pi := by
  have hj : (j.1 : ℝ) < (m : ℝ) + 1 := by exact_mod_cast j.2
  show (j.1 : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1) < 2 * Real.pi
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- **The grid embedding** into the intrinsic sphere: the two poles to the poles, `(i, j)`
to the spherical point at latitude `i·π/(m+1)` and azimuth `j·2π/(m+1)`. -/
noncomputable def gridToSphere (m : ℕ) : SphereGrid m → IntrinsicSphere
  | Sum.inl false => ofVec (sVec 0 0) (norm_sVec 0 0)
  | Sum.inl true => ofVec (sVec Real.pi 0) (norm_sVec Real.pi 0)
  | Sum.inr (i, j) => ofVec (sVec (gridLat m i) (gridAz m j)) (norm_sVec _ _)

@[simp] lemma vec_gridToSphere_false (m : ℕ) :
    (gridToSphere m (Sum.inl false)).vec = sVec 0 0 := rfl

@[simp] lemma vec_gridToSphere_true (m : ℕ) :
    (gridToSphere m (Sum.inl true)).vec = sVec Real.pi 0 := rfl

@[simp] lemma vec_gridToSphere_inr (m : ℕ) (i : {i : Fin (m + 2) // i.1 ≠ 0 ∧ i.1 ≠ m + 1})
    (j : Fin (m + 1)) :
    (gridToSphere m (Sum.inr (i, j))).vec = sVec (gridLat m i) (gridAz m j) := rfl

/-- **The grid embedding is injective** — poles are distinguished by the third coordinate
(`cos` is injective on `[0, π]`), interior latitudes likewise, and interior azimuths by
`cos Δφ = 1` with `|Δφ| < 2π ⟹ Δφ = 0`. -/
lemma gridToSphere_injective (m : ℕ) : Function.Injective (gridToSphere m) := by
  intro x y h
  have hv := congrArg IntrinsicSphere.vec h
  rcases x with b | ⟨i, j⟩ <;> rcases y with b' | ⟨i', j'⟩
  · -- pole vs pole
    cases b <;> cases b'
    · rfl
    · simp only [vec_gridToSphere_false, vec_gridToSphere_true] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two, Real.cos_zero, Real.cos_pi] at h2
      norm_num at h2
    · simp only [vec_gridToSphere_false, vec_gridToSphere_true] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two, Real.cos_zero, Real.cos_pi] at h2
      norm_num at h2
    · rfl
  · -- pole vs interior
    cases b
    · simp only [vec_gridToSphere_false, vec_gridToSphere_inr] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two] at h2
      have h0 : (0 : ℝ) = gridLat m i' :=
        Real.injOn_cos (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
          (gridLat_mem_Icc m i') h2
      exact absurd h0.symm (gridLat_pos m i').ne'
    · simp only [vec_gridToSphere_true, vec_gridToSphere_inr] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two] at h2
      have h0 : Real.pi = gridLat m i' :=
        Real.injOn_cos (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_refl Real.pi⟩)
          (gridLat_mem_Icc m i') h2
      exact absurd h0.symm (gridLat_lt_pi m i').ne
  · -- interior vs pole (mirror)
    cases b'
    · simp only [vec_gridToSphere_false, vec_gridToSphere_inr] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two] at h2
      have h0 : gridLat m i = (0 : ℝ) :=
        Real.injOn_cos (gridLat_mem_Icc m i)
          (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩) h2
      exact absurd h0 (gridLat_pos m i).ne'
    · simp only [vec_gridToSphere_true, vec_gridToSphere_inr] at hv
      have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
      simp only [sVec_apply_two] at h2
      have h0 : gridLat m i = Real.pi :=
        Real.injOn_cos (gridLat_mem_Icc m i)
          (Set.mem_Icc.mpr ⟨Real.pi_pos.le, le_refl Real.pi⟩) h2
      exact absurd h0 (gridLat_lt_pi m i).ne
  · -- interior vs interior
    simp only [vec_gridToSphere_inr] at hv
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) hv
    simp only [sVec_apply_two] at h2
    have hlat : gridLat m i = gridLat m i' :=
      Real.injOn_cos (gridLat_mem_Icc m i) (gridLat_mem_Icc m i') h2
    have hii : i = i' := by
      have hne : Real.pi / ((m : ℝ) + 1) ≠ 0 := by positivity
      unfold gridLat at hlat
      rw [mul_div_assoc, mul_div_assoc] at hlat
      have hval := mul_right_cancel₀ hne hlat
      exact Subtype.ext (Fin.ext (by exact_mod_cast hval))
    subst hii
    have hs : 0 < Real.sin (gridLat m i) :=
      Real.sin_pos_of_pos_of_lt_pi (gridLat_pos m i) (gridLat_lt_pi m i)
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) hv
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) hv
    simp only [sVec_apply_zero, sVec_apply_one] at h0 h1
    have hcos : Real.cos (gridAz m j) = Real.cos (gridAz m j') := mul_left_cancel₀ hs.ne' h0
    have hsin : Real.sin (gridAz m j) = Real.sin (gridAz m j') := mul_left_cancel₀ hs.ne' h1
    have hone : Real.cos (gridAz m j - gridAz m j') = 1 := by
      rw [Real.cos_sub, hcos, hsin, ← sq, ← sq, add_comm]
      exact Real.sin_sq_add_cos_sq (gridAz m j')
    have hb1 := gridAz_nonneg m j
    have hb2 := gridAz_lt_two_pi m j
    have hb3 := gridAz_nonneg m j'
    have hb4 := gridAz_lt_two_pi m j'
    have hd : gridAz m j - gridAz m j' = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hone
    have hjj : j = j' := by
      have haz : gridAz m j = gridAz m j' := by linarith
      have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h2π : (2 * Real.pi) ≠ 0 := by positivity
      unfold gridAz at haz
      have h' := congrArg (fun r : ℝ => r * ((m : ℝ) + 1)) haz
      simp only [div_mul_cancel₀ _ hne] at h'
      have := mul_right_cancel₀ h2π h'
      exact Fin.ext (by exact_mod_cast this)
    rw [hjj]

/-- **The pullback metric**: the lat-long grid carries the sphere-restricted distance (the
exact cone/tripod pattern — the finite cloud is an isometric SAMPLE of the sphere, not an
intrinsic graph-geodesic space; see the scope firewall). -/
noncomputable instance instMetricSpaceSphereGrid (m : ℕ) : MetricSpace (SphereGrid m) where
  dist x y := dist (gridToSphere m x) (gridToSphere m y)
  dist_self x := dist_self (gridToSphere m x)
  dist_comm x y := dist_comm (gridToSphere m x) (gridToSphere m y)
  dist_triangle x y z :=
    dist_triangle (gridToSphere m x) (gridToSphere m y) (gridToSphere m z)
  eq_of_dist_eq_zero := by
    intro x y h
    exact gridToSphere_injective m (eq_of_dist_eq_zero h)

/-- The grid distance, unfolded. -/
lemma sphereGrid_dist_def {m : ℕ} (x y : SphereGrid m) :
    dist x y = dist (gridToSphere m x) (gridToSphere m y) := rfl

/-- **The grid embedding is an EXACT isometry** (the grid metric is the pullback). -/
theorem gridToSphere_isometry (m : ℕ) : Isometry (gridToSphere m) :=
  Isometry.of_dist_eq fun _ _ => rfl

instance instCompactSpaceSphereGrid (m : ℕ) : CompactSpace (SphereGrid m) :=
  Finite.compactSpace

/-! ## Part 4 — the grid is a `3π²/(4(m+1))`-net of the sphere

Every sphere point is reconstructed in spherical coordinates (`lat = arccos z`, azimuth
`φ = Complex.arg (x + iy)`), then rounded: latitude to the nearest of the `m+2` parallels
(the two extreme parallels snap to the POLES, absorbing the chart degeneracy), azimuth
wrap-aware to the nearest of the `m+1` meridians (the mod-`(m+1)` cast absorbs whole turns
via `2π`-periodicity).  The chord→angle bridge `angle_le_pi_div_two_mul_chord` converts the
Euclidean error `≤ π/(2(m+1)) + π/(m+1)` into the great-circle bound. -/

/-- **The net lemma.**  Every point of the intrinsic sphere is within `3π²/(4(m+1))` of an
embedded grid point. -/
theorem sphere_net (m : ℕ) (p : IntrinsicSphere) :
    ∃ x : SphereGrid m,
      dist p (gridToSphere m x) ≤ 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hsum := sum_sq_coords p
  set z : ℝ := p.vec 2 with hz_def
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p.vec 0), sq_nonneg (p.vec 1)]
  have hz_lo : -1 ≤ z := by nlinarith [sq_nonneg (z + 1)]
  have hz_hi : z ≤ 1 := by nlinarith [sq_nonneg (z - 1)]
  set lat : ℝ := Real.arccos z with hlat_def
  have hlat0 : 0 ≤ lat := Real.arccos_nonneg z
  have hlatπ : lat ≤ Real.pi := Real.arccos_le_pi z
  have hcoslat : Real.cos lat = z := Real.cos_arccos hz_lo hz_hi
  -- the RHS is nonnegative and dominates the pole bound
  have hRHS0 : (0 : ℝ) ≤ 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by positivity
  have hpole_le :
      Real.pi / (2 * ((m : ℝ) + 1)) ≤ 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hππ : (0 : ℝ) ≤ 6 * Real.pi ^ 2 - 4 * Real.pi := by
      have h := Real.two_le_pi
      nlinarith [Real.pi_pos]
    nlinarith [mul_nonneg hππ hm1.le]
  -- distances to the two poles, via the third coordinate
  have hcos_north : Real.cos (dist p (gridToSphere m (Sum.inl false))) = z := by
    rw [cos_dist, vec_gridToSphere_false, inner_vec_north p]
  have hcos_south : Real.cos (dist p (gridToSphere m (Sum.inl true))) = -z := by
    rw [cos_dist, vec_gridToSphere_true, inner_vec_south p]
  by_cases hw : p.vec 0 = 0 ∧ p.vec 1 = 0
  · -- CASE A: on the polar axis — `p` IS a pole
    have hz1 : z ^ 2 = 1 := by
      rw [hw.1, hw.2] at hsum
      simpa using hsum
    have hfac : (z - 1) * (z + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · -- z = 1 : the north pole
      have hz : z = 1 := by linarith
      refine ⟨Sum.inl false, ?_⟩
      have hc : Real.cos (dist p (gridToSphere m (Sum.inl false))) = Real.cos 0 := by
        rw [hcos_north, hz, Real.cos_zero]
      have hd : dist p (gridToSphere m (Sum.inl false)) = 0 :=
        Real.injOn_cos (Set.mem_Icc.mpr ⟨dist_nonneg, dist_le_pi _ _⟩)
          (Set.mem_Icc.mpr ⟨le_refl 0, hπ.le⟩) hc
      rw [hd]; exact hRHS0
    · -- z = −1 : the south pole
      have hz : z = -1 := by linarith
      refine ⟨Sum.inl true, ?_⟩
      have hc : Real.cos (dist p (gridToSphere m (Sum.inl true))) = Real.cos 0 := by
        rw [hcos_south, hz, Real.cos_zero]; norm_num
      have hd : dist p (gridToSphere m (Sum.inl true)) = 0 :=
        Real.injOn_cos (Set.mem_Icc.mpr ⟨dist_nonneg, dist_le_pi _ _⟩)
          (Set.mem_Icc.mpr ⟨le_refl 0, hπ.le⟩) hc
      rw [hd]; exact hRHS0
  · -- CASE B: off the axis — spherical-coordinate reconstruction
    set w : ℂ := ⟨p.vec 0, p.vec 1⟩ with hw_def
    have hw0 : w ≠ 0 := fun h =>
      hw ⟨by simpa [hw_def] using congrArg Complex.re h,
        by simpa [hw_def] using congrArg Complex.im h⟩
    have hwn0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    have hnormsq : Complex.normSq w = 1 - z ^ 2 := by
      rw [hw_def, Complex.normSq_mk]
      linear_combination hsum
    have hnormw : ‖w‖ = Real.sin lat := by
      rw [Complex.norm_def, hnormsq, hlat_def, Real.sin_arccos]
    set φ : ℝ := Complex.arg w with hφ_def
    -- THE RECONSTRUCTION: p is the spherical point at (lat, φ)
    have hre : Real.sin lat * Real.cos φ = p.vec 0 := by
      calc Real.sin lat * Real.cos φ = ‖w‖ * (w.re / ‖w‖) := by
            rw [hφ_def, Complex.cos_arg hw0, hnormw]
        _ = w.re := by rw [mul_comm, div_mul_cancel₀ _ hwn0]
        _ = p.vec 0 := by rw [hw_def]
    have him : Real.sin lat * Real.sin φ = p.vec 1 := by
      calc Real.sin lat * Real.sin φ = ‖w‖ * (w.im / ‖w‖) := by
            rw [hφ_def, Complex.sin_arg, hnormw]
        _ = w.im := by rw [mul_comm, div_mul_cancel₀ _ hwn0]
        _ = p.vec 1 := by rw [hw_def]
    have hrec : p.vec = sVec lat φ := by
      refine PiLp.ext fun i => ?_
      fin_cases i
      · exact hre.symm
      · exact him.symm
      · exact (hcoslat.trans hz_def).symm
    -- LATITUDE ROUNDING: nearest of the m+2 parallels (indices 0..m+1)
    set kz : ℤ := round (lat * ((m : ℝ) + 1) / Real.pi) with hkz_def
    have hkz0 : 0 ≤ kz := by
      rw [hkz_def, round_eq]
      refine Int.le_floor.mpr ?_
      have h0 : 0 ≤ lat * ((m : ℝ) + 1) / Real.pi := by positivity
      push_cast
      linarith
    have habs_lat := abs_sub_round (lat * ((m : ℝ) + 1) / Real.pi)
    rw [← hkz_def] at habs_lat
    have hkzle : kz ≤ (m : ℤ) + 1 := by
      have hub : lat * ((m : ℝ) + 1) / Real.pi ≤ (m : ℝ) + 1 := by
        rw [div_le_iff₀ hπ]
        calc lat * ((m : ℝ) + 1) ≤ Real.pi * ((m : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right hlatπ hm1.le
          _ = ((m : ℝ) + 1) * Real.pi := mul_comm _ _
      have h1 : (kz : ℝ) ≤ lat * ((m : ℝ) + 1) / Real.pi + 1 / 2 := by
        have h := abs_sub_le_iff.mp habs_lat
        linarith [h.2]
      have h2 : (kz : ℝ) < (m : ℝ) + 2 := by linarith
      have h3 : kz < (m : ℤ) + 2 := by exact_mod_cast h2
      omega
    set k : ℕ := kz.toNat with hk_def
    have hkR : (k : ℝ) = (kz : ℝ) := by
      rw [hk_def]; exact_mod_cast Int.toNat_of_nonneg hkz0
    have hkle : k ≤ m + 1 := by omega
    have herr_lat : |lat - (k : ℝ) * Real.pi / ((m : ℝ) + 1)|
        ≤ Real.pi / (2 * ((m : ℝ) + 1)) := by
      have hkey : lat - (k : ℝ) * Real.pi / ((m : ℝ) + 1)
          = (lat * ((m : ℝ) + 1) / Real.pi - (kz : ℝ)) * (Real.pi / ((m : ℝ) + 1)) := by
        have hm1ne : ((m : ℝ) + 1) ≠ 0 := hm1.ne'
        rw [hkR]
        field_simp
      rw [hkey, abs_mul, abs_of_pos (div_pos hπ hm1)]
      calc |lat * ((m : ℝ) + 1) / Real.pi - (kz : ℝ)| * (Real.pi / ((m : ℝ) + 1))
          ≤ 1 / 2 * (Real.pi / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right habs_lat (by positivity)
        _ = Real.pi / (2 * ((m : ℝ) + 1)) := by rw [div_mul_div_comm, one_mul]
    -- AZIMUTH ROUNDING: nearest meridian, wrap-aware
    set J : ℤ := round (φ * ((m : ℝ) + 1) / (2 * Real.pi)) with hJ_def
    have habs_az := abs_sub_round (φ * ((m : ℝ) + 1) / (2 * Real.pi))
    rw [← hJ_def] at habs_az
    have herr_az : |φ - (J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)|
        ≤ Real.pi / ((m : ℝ) + 1) := by
      have hkey : φ - (J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)
          = (φ * ((m : ℝ) + 1) / (2 * Real.pi) - (J : ℝ))
            * ((2 * Real.pi) / ((m : ℝ) + 1)) := by
        have hm1ne : ((m : ℝ) + 1) ≠ 0 := hm1.ne'
        field_simp
      rw [hkey, abs_mul,
        abs_of_pos (div_pos (by positivity : (0 : ℝ) < 2 * Real.pi) hm1)]
      calc |φ * ((m : ℝ) + 1) / (2 * Real.pi) - (J : ℝ)| * ((2 * Real.pi) / ((m : ℝ) + 1))
          ≤ 1 / 2 * ((2 * Real.pi) / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right habs_az (by positivity)
        _ = Real.pi / ((m : ℝ) + 1) := by ring
    -- the wrap: reduce J modulo m+1; whole turns are invisible to sVec
    set jn : ℕ := (J % ((m : ℤ) + 1)).toNat with hjn_def
    have hmod0 : 0 ≤ J % ((m : ℤ) + 1) := Int.emod_nonneg J (by omega)
    have hmodlt : J % ((m : ℤ) + 1) < (m : ℤ) + 1 := Int.emod_lt_of_pos J (by omega)
    have hjnlt : jn < m + 1 := by omega
    have hjnR : (jn : ℝ) = ((J % ((m : ℤ) + 1) : ℤ) : ℝ) := by
      rw [hjn_def]; exact_mod_cast Int.toNat_of_nonneg hmod0
    set q : ℤ := J / ((m : ℤ) + 1) with hq_def
    have hZ : ((m : ℤ) + 1) * q + J % ((m : ℤ) + 1) = J := by
      rw [hq_def]; exact Int.mul_ediv_add_emod J ((m : ℤ) + 1)
    have hR : ((m : ℝ) + 1) * (q : ℝ) + (jn : ℝ) = (J : ℝ) := by
      rw [hjnR]; exact_mod_cast hZ
    have hwrap : sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
          ((jn : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1))
        = sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
          ((J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)) := by
      have hqid : (J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)
          = (jn : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1) + (q : ℝ) * (2 * Real.pi) := by
        have hm1ne : ((m : ℝ) + 1) ≠ 0 := hm1.ne'
        rw [← hR]
        field_simp
        ring
      rw [hqid, sVec_add_int_mul_two_pi]
    -- CASE on the rounded latitude index
    by_cases hk0 : k = 0
    · -- snap NORTH: the point is within π/(2(m+1)) of the pole
      refine ⟨Sum.inl false, ?_⟩
      have hd : dist p (gridToSphere m (Sum.inl false)) = lat := by
        refine Real.injOn_cos (Set.mem_Icc.mpr ⟨dist_nonneg, dist_le_pi _ _⟩)
          (Set.mem_Icc.mpr ⟨hlat0, hlatπ⟩) ?_
        rw [hcos_north, hcoslat]
      have hlatle : lat ≤ Real.pi / (2 * ((m : ℝ) + 1)) := by
        have h := herr_lat
        rw [hk0] at h
        simpa [abs_of_nonneg hlat0] using h
      rw [hd]
      exact hlatle.trans hpole_le
    by_cases hkm : k = m + 1
    · -- snap SOUTH
      refine ⟨Sum.inl true, ?_⟩
      have hd : dist p (gridToSphere m (Sum.inl true)) = Real.pi - lat := by
        refine Real.injOn_cos (Set.mem_Icc.mpr ⟨dist_nonneg, dist_le_pi _ _⟩)
          (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) ?_
        rw [hcos_south, Real.cos_pi_sub, hcoslat]
      have hlatge : Real.pi - lat ≤ Real.pi / (2 * ((m : ℝ) + 1)) := by
        have h := herr_lat
        rw [hkm] at h
        have hval : ((m + 1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1) = Real.pi := by
          push_cast
          field_simp
        rw [hval, abs_sub_comm, abs_of_nonneg (by linarith)] at h
        exact h
      rw [hd]
      exact hlatge.trans hpole_le
    · -- INTERIOR: the grid point (k, jn)
      have hklt : k < m + 2 := by omega
      obtain ⟨g, hgvec⟩ : ∃ g : SphereGrid m, (gridToSphere m g).vec
          = sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
            ((jn : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)) :=
        ⟨Sum.inr (⟨⟨k, hklt⟩, ⟨hk0, hkm⟩⟩, ⟨jn, hjnlt⟩), rfl⟩
      refine ⟨g, ?_⟩
      have hb := angle_le_pi_div_two_mul_chord p (gridToSphere m g)
      rw [hgvec, hrec, hwrap] at hb
      refine hb.trans ?_
      have htri : ‖sVec lat φ - sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
            ((J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1))‖
          ≤ Real.pi / (2 * ((m : ℝ) + 1)) + Real.pi / ((m : ℝ) + 1) := by
        have h3 := dist_triangle (sVec lat φ)
          (sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) φ)
          (sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
            ((J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1)))
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h3
        have h4 := chord_sVec_lat_le lat ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) φ
        have h5 := chord_sVec_azi_le ((k : ℝ) * Real.pi / ((m : ℝ) + 1)) φ
          ((J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1))
        linarith [herr_lat, herr_az]
      calc Real.pi / 2 * ‖sVec lat φ - sVec ((k : ℝ) * Real.pi / ((m : ℝ) + 1))
            ((J : ℝ) * (2 * Real.pi) / ((m : ℝ) + 1))‖
          ≤ Real.pi / 2 * (Real.pi / (2 * ((m : ℝ) + 1)) + Real.pi / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left htri (by positivity)
        _ = 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
            have hm1ne : ((m : ℝ) + 1) ≠ 0 := hm1.ne'
            field_simp
            ring

/-! ## Part 5 — the quantitative Gromov–Hausdorff bound -/

/-- **THE S2 BOUND.**  The Gromov–Hausdorff distance between the finite lat-long grid (with
its pullback metric) and the intrinsic sphere is at most `3π²/(4(m+1))`: the grid embedding
is an EXACT isometry (`ε₂ = 0`) whose image is a `3π²/(4(m+1))`-net. -/
theorem ghDist_sphereGrid_le (m : ℕ) :
    GromovHausdorff.ghDist (SphereGrid m) IntrinsicSphere
      ≤ 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
  have key : GromovHausdorff.ghDist (SphereGrid m) IntrinsicSphere
      ≤ 0 + 0 / 2 + 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
      (s := (Set.univ : Set (SphereGrid m))) (fun z => gridToSphere m z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := sphere_net m q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (gridToSphere m x) (gridToSphere m y)| ≤ 0
      rw [sphereGrid_dist_def, sub_self, abs_zero]
  linarith

/-! ## Part 6 — the S2 capstone -/

/-- **THE S2 CAPSTONE (Gromov–Hausdorff convergence to the SPHERE).**  The finite lat-long
clouds — two poles plus `m·(m+1)` grid points, carrying the pullback metric — converge in
Gromov–Hausdorff space to the intrinsic sphere, the compact metric space that is provably
NOT flat: it admits no isometric embedding into any real inner-product space
(`SphereMetric.sphere_no_isometric_embedding_into_inner`).  The program's first SMOOTH
curved-space GH limit (curved everywhere, vs the cone's single singular point) — but note
the honesty firewall: the clouds are exact isometric SAMPLES (pullback metric), not
intrinsic graph-geodesic spaces, and the formalized curvature statement is the midpoint
obstruction, not a Riemann tensor (see the header). -/
theorem sphereGrid_toGHSpace_tendsto_sphere :
    Tendsto (fun m : ℕ => GromovHausdorff.toGHSpace (SphereGrid m)) atTop
      (𝓝 (GromovHausdorff.toGHSpace IntrinsicSphere)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : ∀ m : ℕ,
      dist (GromovHausdorff.toGHSpace (SphereGrid m))
          (GromovHausdorff.toGHSpace IntrinsicSphere)
        ≤ 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) :=
    fun m => ghDist_sphereGrid_le m
  have h1 : Tendsto (fun m : ℕ => 3 * Real.pi ^ 2 / (4 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ => 1 / (((m + 1 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    have h' := h.const_mul (3 * Real.pi ^ 2 / 4)
    rw [mul_zero] at h'
    refine h'.congr fun m => ?_
    have hm1ne : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  exact squeeze_zero (fun m => dist_nonneg) hb h1

end QIQTH.SphereGH
