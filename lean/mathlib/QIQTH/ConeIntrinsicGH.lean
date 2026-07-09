/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# THE INTRINSIC CONE GH LIMIT — positive curvature from pure hop-counting
(brick K3, intrinsic-cone capstone)

Capstone of the INTRINSIC-CONE track
(`docs/qg_roadmap/STATEWIRE2_SPHERE_INTRINSIC_CONE_PLAN.md`).  Brick K1
(`QIQTH/ConeIntrinsicGraph.lean`) built the geometric graph `coneGraph θ n ρ` on the polar
grid and the lower bound `coneDist ≤ ρ · hopcount`; brick K2 (`QIQTH/ConeIntrinsicWalk.lean`)
discharged connectivity with the unfolded-segment walk and proved the matching upper bound
`hopdist ≤ coneDist/(ρ − 2·mesh) + 1`.  This file assembles THE HEADLINE: with the radius
schedule `ρ_n = (1+θ)/√(n+1)` (microscopic in the cone, yet huge against the mesh
`≍ (1+θ)/n`), the **scaled HOP metrics** `ρ_n · dist_hop` of the geometric graphs — pure
combinatorial path-counting on finite point sets, no ambient chart — converge in Mathlib's
Gromov–Hausdorff space to the cone:

    toGHSpace (IntrinsicConeSpace θ n) ⟶ toGHSpace (Cone θ)
                                        (`coneIntrinsic_toGHSpace_tendsto_cone`)

via the quantitative bound
`ghDist (IntrinsicConeSpace θ n) (Cone θ) ≤ coneError θ n / 2 + mesh θ n`
(`ghDist_coneIntrinsic_le`), where `coneError θ n = 4·mesh/(ρ_n − 2·mesh) + ρ_n → 0`
(`coneError_tendsto_zero`).  The cone is the space whose CONCENTRATED POSITIVE CURVATURE is
a theorem (`ConeMetric.cone_no_isometric_embedding_into_inner`, deficit angle `2π − θ`): this
is the first intrinsic (graph-geodesic) limit in the program with nonzero curvature,
completing the intrinsic family {cube, torus, tripod, cone} =
{flat, flat-periodic, branching, positively-curved}.

The two-sided pinch (`coneIntrinsic_pinch`) rides K1 + K2 exactly as G3 rode G1 + G2 in the
stencil campaign; the metric-space totalization uses the effective radius
`rhoEff θ n = max (ρ_n) (3·mesh θ n)` (always `> 2·mesh`, so connectivity — and hence the
triangle inequality — holds for EVERY `n`), which collapses to the true schedule `ρ_n` for
`n ≥ 10` (`rhoEff_eq_rhoN`, riding the threshold `3·mesh < ρ_n ⟸ 3√(n+1) < n`).

## Scope firewall (HONEST)

* **The cone geometry is INSERTED through the adjacency rule** (`dist x y ≤ ρ`, the cone
  metric) — nothing about the cone is emergent from combinatorics; the combinatorics
  RECOVERS a geometry that was put in by hand.  Recovery, not emergence.
* **`θ` is an INPUT** — a chosen deficit angle, not derived.
* **The curvature is CONCENTRATED** — an Alexandrov cone point, NOT a smooth Riemann tensor,
  NOT a Riemannian manifold.  Away from the apex the cone is flat.
* **The sphere's intrinsic hop version remains the cited frontier** — this brick handles the
  cone (curvature concentrated at one point), not distributed smooth curvature.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.ConeIntrinsicWalk
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.Real.Sqrt

namespace QIQTH.ConeIntrinsicGH

open QIQTH.ConeMetric QIQTH.ConeGH QIQTH.ConeIntrinsicGraph QIQTH.ConeIntrinsicWalk
open Filter Topology

/-- A strict deficit-angle `Fact` yields the non-strict one the K1/K2/B2b instances consume
(low priority: only fires when a genuine `θ < 2π` fact is around). -/
instance (priority := 100) instFactThetaLeOfLt (θ : ℝ) [h : Fact (θ < 2 * Real.pi)] :
    Fact (θ ≤ 2 * Real.pi) := ⟨h.out.le⟩

/-! ## Part 1 — the radius schedule `ρ_n = (1+θ)/√(n+1)` and the threshold -/

/-- **The radius schedule** `ρ_n = (1+θ)/√(n+1)`: vanishing in the cone (so the limit is
intrinsic), yet asymptotically huge against the mesh `mesh θ n ≤ (1+θ)/n` (so the per-hop
snapping error `2·mesh/ρ_n → 0` and the distortion vanishes). -/
noncomputable def rhoN (θ : ℝ) (n : ℕ) : ℝ := (1 + θ) / Real.sqrt ((n : ℝ) + 1)

/-- For `n ≥ 10` the square root is beaten by a third of `n`: `√(n+1) < n/3` (equivalently
`9(n+1) < n²`) — the elementary inequality behind the threshold. -/
private lemma sqrt_lt_third (n : ℕ) (hn : 10 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) < (n : ℝ) / 3 := by
  have hnR : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine (Real.sqrt_lt' (by linarith)).mpr ?_
  nlinarith [hnR, mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 10)
    (by linarith : (0 : ℝ) ≤ (n : ℝ))]

section Schedule

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)]

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The schedule is positive. -/
lemma rhoN_pos (n : ℕ) : 0 < rhoN θ n := by
  have hθ0 : (0 : ℝ) < θ := Fact.out
  have hsqpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos (by linarith) hsqpos

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
/-- The schedule vanishes: `ρ_n → 0` — the graphs become intrinsically fine. -/
lemma rhoN_tendsto_zero : Tendsto (rhoN θ) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have h := hs.inv_tendsto_atTop.const_mul (1 + θ)
  rw [mul_zero] at h
  exact h.congr fun n => (div_eq_mul_inv (1 + θ) (Real.sqrt ((n : ℝ) + 1))).symm

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The mesh, cleared of its denominator: `mesh θ n · n ≤ 1 + θ` (K1's `mesh_le`). -/
lemma mesh_mul_le (n : ℕ) (hn : 1 ≤ n) : mesh θ n * (n : ℝ) ≤ 1 + θ := by
  have hn0 : ((n : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact h.ne'
  have h := mul_le_mul_of_nonneg_right (mesh_le θ n hn)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  rwa [div_mul_cancel₀ _ hn0] at h

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- **THE THRESHOLD.**  For `n ≥ 10` the schedule beats THREE meshes: `3·mesh θ n < ρ_n`
(via `mesh·n ≤ 1+θ` and `√(n+1) < n/3`) — strong enough both for K2 connectivity
(`2·mesh < ρ`) and for the totalized effective radius to collapse to the true schedule. -/
theorem three_mesh_lt_rhoN (n : ℕ) (hn : 10 ≤ n) : 3 * mesh θ n < rhoN θ n := by
  have hn1 : 1 ≤ n := by omega
  have hm := mesh_pos θ n
  have hsqpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsq := sqrt_lt_third n hn
  have hmn := mesh_mul_le θ n hn1
  show 3 * mesh θ n < (1 + θ) / Real.sqrt ((n : ℝ) + 1)
  rw [lt_div_iff₀ hsqpos]
  nlinarith [mul_lt_mul_of_pos_left hsq (by linarith : (0 : ℝ) < 3 * mesh θ n)]

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The K2 connectivity threshold: `2·mesh θ n < ρ_n` for `n ≥ 10`. -/
theorem two_mesh_lt_rhoN (n : ℕ) (hn : 10 ≤ n) : 2 * mesh θ n < rhoN θ n := by
  have h3 := three_mesh_lt_rhoN θ n hn
  have hm := mesh_pos θ n
  linarith

/-! ## Part 2 — the distortion error and the two-sided pinch -/

/-- **The distortion error** of the schedule: `4·mesh/(ρ_n − 2·mesh) + ρ_n` — the snapping
cost of the K2 walk (numerator `4·mesh` = the cone diameter `2` times the per-hop snapping
gap `2·mesh`) plus one trailing hop `ρ_n`. -/
noncomputable def coneError (n : ℕ) : ℝ :=
  4 * mesh θ n / (rhoN θ n - 2 * mesh θ n) + rhoN θ n

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
/-- The distortion error, unfolded. -/
lemma coneError_def (n : ℕ) :
    coneError θ n = 4 * mesh θ n / (rhoN θ n - 2 * mesh θ n) + rhoN θ n := rfl

/-- **THE K3 PINCH.**  For `n ≥ 10` the scaled hop metric `ρ_n · dist_hop` is pinched
against the cone (pullback) metric with additive error `coneError θ n`, UNIFORMLY in the
pair of grid points: K1's lower bound (each hop moves at most `ρ_n`) and K2's upper bound
(the unfolded-segment walk), the denominator cleared exactly as in the stencil G3 brick,
with the cone diameter `≤ 2` making the error uniform. -/
theorem coneIntrinsic_pinch (hθlt : θ < 2 * Real.pi) (n : ℕ) (hn : 10 ≤ n)
    (x y : PolarGrid θ n) :
    dist x y ≤ rhoN θ n * ((coneGraph θ n (rhoN θ n)).dist x y : ℝ)
    ∧ rhoN θ n * ((coneGraph θ n (rhoN θ n)).dist x y : ℝ)
        ≤ dist x y + coneError θ n := by
  have hρ2 := two_mesh_lt_rhoN θ n hn
  have hreach := coneGraph_reachable θ n (rhoN θ n) hθlt hρ2 x y
  constructor
  · exact dist_le_rho_mul_dist θ n (rhoN θ n) (rhoN_pos θ n).le hreach
  · have hup := coneGraph_dist_le θ n (rhoN θ n) hθlt hρ2 x y
    have hden : (0 : ℝ) < rhoN θ n - 2 * mesh θ n := by
      have hm := mesh_pos θ n
      linarith
    have hD2 : dist x y ≤ 2 := polarGrid_diam θ n x y
    have hρpos := rhoN_pos θ n
    have hm := mesh_pos θ n
    set k : ℝ := ((coneGraph θ n (rhoN θ n)).dist x y : ℝ) with hkdef
    -- clear the `(ρ − 2·mesh)` denominator in the K2 upper bound
    have hclear : k * (rhoN θ n - 2 * mesh θ n)
        ≤ dist x y + (rhoN θ n - 2 * mesh θ n) := by
      have h := mul_le_mul_of_nonneg_right hup hden.le
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hden.ne'] at h
    -- the G3 shape, denominator-free: multiply through by `(ρ − 2·mesh) > 0`
    have hce : coneError θ n * (rhoN θ n - 2 * mesh θ n)
        = 4 * mesh θ n + rhoN θ n * (rhoN θ n - 2 * mesh θ n) := by
      rw [coneError_def, add_mul, div_mul_cancel₀ _ hden.ne']
    have hmul := mul_le_mul_of_nonneg_left hclear hρpos.le
    have hfinal : rhoN θ n * k * (rhoN θ n - 2 * mesh θ n)
        ≤ (dist x y + coneError θ n) * (rhoN θ n - 2 * mesh θ n) := by
      rw [add_mul, hce]
      nlinarith [hmul, mul_nonneg hm.le (by linarith : (0 : ℝ) ≤ 2 - dist x y)]
    exact le_of_mul_le_mul_right hfinal hden

/-! ## Part 3 — the error vanishes -/

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- **The explicit error bound.**  For `n ≥ 10`,
`coneError θ n ≤ 4/(n/√(n+1) − 2) + ρ_n` — the `(1+θ)` cancels: the fraction
`4·mesh/(ρ − 2·mesh)` is monotone in the mesh (cross-multiplied, it reduces to
`mesh · (n/√(n+1)) ≤ ρ_n`, i.e. `mesh·n ≤ 1+θ`), and the resulting bound is θ-free in its
first summand. -/
theorem coneError_le (n : ℕ) (hn : 10 ≤ n) :
    coneError θ n ≤ 4 / ((n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2) + rhoN θ n := by
  have hn1 : 1 ≤ n := by omega
  have hm := mesh_pos θ n
  have hsqpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hden : (0 : ℝ) < rhoN θ n - 2 * mesh θ n := by
    have := two_mesh_lt_rhoN θ n hn
    linarith
  have hsq := sqrt_lt_third n hn
  have hS3 : (3 : ℝ) < (n : ℝ) / Real.sqrt ((n : ℝ) + 1) := by
    rw [lt_div_iff₀ hsqpos]
    calc (3 : ℝ) * Real.sqrt ((n : ℝ) + 1) < 3 * ((n : ℝ) / 3) :=
          mul_lt_mul_of_pos_left hsq (by norm_num)
      _ = (n : ℝ) := by ring
  have hSden : (0 : ℝ) < (n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2 := by linarith
  -- the key cancellation: `mesh · (n/√(n+1)) ≤ ρ_n`
  have hmS : mesh θ n * ((n : ℝ) / Real.sqrt ((n : ℝ) + 1)) ≤ rhoN θ n := by
    have hmn := mesh_mul_le θ n hn1
    show mesh θ n * ((n : ℝ) / Real.sqrt ((n : ℝ) + 1))
        ≤ (1 + θ) / Real.sqrt ((n : ℝ) + 1)
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hsqpos]
    exact hmn
  have hfrac : 4 * mesh θ n / (rhoN θ n - 2 * mesh θ n)
      ≤ 4 / ((n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2) := by
    rw [div_le_div_iff₀ hden hSden]
    nlinarith [hmS]
  rw [coneError_def]
  linarith

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- **The error vanishes**: `coneError θ n → 0` — the θ-free bound `4/(n/√(n+1) − 2)`
tends to zero since `n/√(n+1) ≥ √(n+1)/2 → ∞`, and `ρ_n → 0`. -/
theorem coneError_tendsto_zero : Tendsto (coneError θ) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  -- `n/√(n+1) → ∞`, from below by `√(n+1)/2`
  have hS : Tendsto (fun n : ℕ => (n : ℝ) / Real.sqrt ((n : ℝ) + 1)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hs.atTop_div_const two_pos)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsqpos : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_div_iff₀ two_pos hsqpos, Real.mul_self_sqrt (by positivity)]
    linarith
  have hS2 : Tendsto (fun n : ℕ => (n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact hS
  have h4 : Tendsto (fun n : ℕ => 4 / ((n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2))
      atTop (𝓝 0) := by
    have h := hS2.inv_tendsto_atTop.const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact h.congr fun n => (div_eq_mul_inv 4 ((n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2)).symm
  have hub : Tendsto
      (fun n : ℕ => 4 / ((n : ℝ) / Real.sqrt ((n : ℝ) + 1) - 2) + rhoN θ n)
      atTop (𝓝 0) := by
    have h := h4.add (rhoN_tendsto_zero θ)
    rwa [add_zero] at h
  refine squeeze_zero' ?_ ?_ hub
  · filter_upwards [eventually_ge_atTop 10] with n hn
    have hm := mesh_pos θ n
    have hden : (0 : ℝ) < rhoN θ n - 2 * mesh θ n := by
      have := two_mesh_lt_rhoN θ n hn
      linarith
    have hρ := rhoN_pos θ n
    have h1 : (0 : ℝ) ≤ 4 * mesh θ n / (rhoN θ n - 2 * mesh θ n) :=
      div_nonneg (by linarith) hden.le
    rw [coneError_def]
    linarith
  · filter_upwards [eventually_ge_atTop 10] with n hn
    exact coneError_le θ n hn

omit [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] in
/-- The mesh vanishes: `mesh θ n → 0` (the two shifted `1/n` summands of B2b). -/
lemma mesh_tendsto_zero : Tendsto (fun n : ℕ => mesh θ n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have h2 : Tendsto (fun n : ℕ => θ / (2 * ((n : ℝ) + 2))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 1 / (((n + 2 : ℕ)) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 2)
    have h' := h.const_mul (θ / 2)
    rw [mul_zero] at h'
    refine h'.congr fun n => ?_
    push_cast
    rw [div_mul_div_comm, mul_one]
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr fun n => (mesh_def θ n).symm

/-! ## Part 4 — the effective radius (totalization) -/

/-- **The effective radius** `max (ρ_n) (3·mesh θ n)`: always strictly above `2·mesh` (the
mesh is positive), so K2 connectivity — and hence the scaled-hop metric-space axioms — hold
for EVERY `n` with no side conditions; equal to the true schedule `ρ_n` in the limit regime
`n ≥ 10` (the threshold). -/
noncomputable def rhoEff (n : ℕ) : ℝ := max (rhoN θ n) (3 * mesh θ n)

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The effective radius is positive. -/
lemma rhoEff_pos (n : ℕ) : 0 < rhoEff θ n := by
  have hm := mesh_pos θ n
  show (0 : ℝ) < max (rhoN θ n) (3 * mesh θ n)
  exact lt_max_of_lt_right (by linarith)

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- The effective radius always clears the K2 connectivity threshold. -/
lemma two_mesh_lt_rhoEff (n : ℕ) : 2 * mesh θ n < rhoEff θ n := by
  have hm := mesh_pos θ n
  show 2 * mesh θ n < max (rhoN θ n) (3 * mesh θ n)
  exact lt_max_of_lt_right (by linarith)

omit [Fact (θ ≤ 2 * Real.pi)] in
/-- In the limit regime `n ≥ 10` the effective radius IS the schedule `ρ_n`. -/
lemma rhoEff_eq_rhoN (n : ℕ) (hn : 10 ≤ n) : rhoEff θ n = rhoN θ n :=
  max_eq_left (three_mesh_lt_rhoN θ n hn).le

end Schedule

/-! ## Part 5 — the intrinsic scaled-hop metric space -/

/-- **The intrinsic cone space**: a type synonym for the polar grid `PolarGrid θ n`,
carrying the intrinsic scaled HOP metric `rhoEff θ n · dist_hop` (the synonym keeps the
instance from clashing with the pullback metric of B2b). -/
def IntrinsicConeSpace (θ : ℝ) (n : ℕ) : Type := PolarGrid θ n

/-- View an intrinsic-cone point as a polar-grid point. -/
def IntrinsicConeSpace.pt {θ : ℝ} {n : ℕ} (x : IntrinsicConeSpace θ n) : PolarGrid θ n := x

/-- View a polar-grid point as an intrinsic-cone point. -/
def toIntrinsic {θ : ℝ} {n : ℕ} (x : PolarGrid θ n) : IntrinsicConeSpace θ n := x

instance (θ : ℝ) (n : ℕ) : Nonempty (IntrinsicConeSpace θ n) :=
  inferInstanceAs (Nonempty (PolarGrid θ n))

instance (θ : ℝ) (n : ℕ) : Finite (IntrinsicConeSpace θ n) :=
  inferInstanceAs (Finite (PolarGrid θ n))

section Intrinsic

variable (θ : ℝ) [Fact (0 < θ)] [Fact (θ < 2 * Real.pi)]

/-- **The intrinsic scaled-hop metric**: `dist x y = rhoEff θ n · hopdist x y`.  The
effective radius always clears `2·mesh`, so K2 connectivity gives the triangle inequality
(`Reachable.dist_triangle_right`) and point separation for EVERY `n` — a genuine deficit
angle `θ < 2π` is required (the K2 sector lemma). -/
noncomputable instance instMetricSpaceIntrinsicConeSpace (n : ℕ) :
    MetricSpace (IntrinsicConeSpace θ n) where
  dist x y := rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ)
  dist_self x := by
    show rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt x.pt : ℝ) = 0
    rw [SimpleGraph.dist_self]
    simp
  dist_comm x y := by
    show rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ)
      = rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist y.pt x.pt : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt z.pt : ℝ)
      ≤ rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ)
        + rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist y.pt z.pt : ℝ)
    have hreach := coneGraph_reachable θ n (rhoEff θ n)
      (Fact.out : θ < 2 * Real.pi) (two_mesh_lt_rhoEff θ n) y.pt z.pt
    have htri : (coneGraph θ n (rhoEff θ n)).dist x.pt z.pt
        ≤ (coneGraph θ n (rhoEff θ n)).dist x.pt y.pt
          + (coneGraph θ n (rhoEff θ n)).dist y.pt z.pt :=
      hreach.dist_triangle_right x.pt
    have hcast : ((coneGraph θ n (rhoEff θ n)).dist x.pt z.pt : ℝ)
        ≤ ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ)
          + ((coneGraph θ n (rhoEff θ n)).dist y.pt z.pt : ℝ) := by exact_mod_cast htri
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hcast (rhoEff_pos θ n).le
  eq_of_dist_eq_zero := by
    intro x y h
    have h' : rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ) = 0 := h
    have hg : ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ) = 0 :=
      (mul_eq_zero.mp h').resolve_left (rhoEff_pos θ n).ne'
    have hg0 : (coneGraph θ n (rhoEff θ n)).dist x.pt y.pt = 0 := by exact_mod_cast hg
    have hreach := coneGraph_reachable θ n (rhoEff θ n)
      (Fact.out : θ < 2 * Real.pi) (two_mesh_lt_rhoEff θ n) x.pt y.pt
    exact hreach.dist_eq_zero_iff.mp hg0

instance (n : ℕ) : CompactSpace (IntrinsicConeSpace θ n) := Finite.compactSpace

/-- The intrinsic scaled-hop distance, unfolded. -/
lemma intrinsicCone_dist_eq (n : ℕ) (x y : IntrinsicConeSpace θ n) :
    dist x y = rhoEff θ n * ((coneGraph θ n (rhoEff θ n)).dist x.pt y.pt : ℝ) := rfl

/-! ## Part 6 — the quantitative Gromov–Hausdorff bound -/

/-- **THE K3 BOUND.**  For `n ≥ 10`, the Gromov–Hausdorff distance between the intrinsic
scaled-hop space and the cone is at most `coneError θ n / 2 + mesh θ n`: the grid embedding
is a `coneError θ n`-approximate isometry (the pinch, with `rhoEff = ρ_n` in this regime)
whose image is a `mesh θ n`-net of the cone (B2b's net lemma). -/
theorem ghDist_coneIntrinsic_le (n : ℕ) (hn : 10 ≤ n) :
    GromovHausdorff.ghDist (IntrinsicConeSpace θ n) (Cone θ)
      ≤ coneError θ n / 2 + mesh θ n := by
  have key : GromovHausdorff.ghDist (IntrinsicConeSpace θ n) (Cone θ)
      ≤ 0 + coneError θ n / 2 + mesh θ n := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (IntrinsicConeSpace θ n)))
        (fun z => gridToCone θ n z.1.pt) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := cone_net_mesh θ n q
      exact ⟨⟨toIntrinsic x, Set.mem_univ _⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (gridToCone θ n x.pt) (gridToCone θ n y.pt)| ≤ coneError θ n
      obtain ⟨hlo, hhi⟩ :=
        coneIntrinsic_pinch θ (Fact.out : θ < 2 * Real.pi) n hn x.pt y.pt
      rw [intrinsicCone_dist_eq θ n x y, rhoEff_eq_rhoN θ n hn,
        ← polarGrid_dist_def θ x.pt y.pt, abs_of_nonneg (sub_nonneg.mpr hlo)]
      linarith
  linarith

/-! ## Part 7 — THE K3 CAPSTONE -/

/-- **THE K3 CAPSTONE (POSITIVE CURVATURE FROM PURE HOP-COUNTING).**  The intrinsic
scaled-hop metric spaces — finite point sets metrized by pure combinatorial path-counting
in the geometric graph, no ambient chart, no pullback — converge in Gromov–Hausdorff space
to the cone of total angle `θ < 2π`, the compact metric space whose apex carries
CONCENTRATED POSITIVE CURVATURE (deficit angle `2π − θ`), provably not isometrically
embeddable in any real inner-product space
(`ConeMetric.cone_no_isometric_embedding_into_inner`).  The first intrinsic
(graph-geodesic) limit in the program with nonzero curvature, completing the intrinsic
family {cube, torus, tripod, cone} = {flat, flat-periodic, branching, positively-curved}.
Honesty firewall: the cone geometry is INSERTED through the adjacency rule (recovery, not
emergence), `θ` is an input, the curvature is concentrated (Alexandrov), and the sphere's
intrinsic hop version remains the cited frontier — see the header. -/
theorem coneIntrinsic_toGHSpace_tendsto_cone :
    Tendsto (fun n : ℕ => GromovHausdorff.toGHSpace (IntrinsicConeSpace θ n)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (Cone θ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ n : ℕ in atTop,
      dist (GromovHausdorff.toGHSpace (IntrinsicConeSpace θ n))
          (GromovHausdorff.toGHSpace (Cone θ))
        ≤ coneError θ n / 2 + mesh θ n := by
    filter_upwards [eventually_ge_atTop 10] with n hn
    exact ghDist_coneIntrinsic_le θ n hn
  have hub : Tendsto (fun n : ℕ => coneError θ n / 2 + mesh θ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => coneError θ n / 2) atTop (𝓝 0) := by
      simpa using (coneError_tendsto_zero θ).div_const 2
    have h2 := h1.add (mesh_tendsto_zero θ)
    rwa [add_zero] at h2
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => dist_nonneg) hbound hub

end Intrinsic

end QIQTH.ConeIntrinsicGH
