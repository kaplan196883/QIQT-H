/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# TORUS STENCIL GH LIMIT — Gromov–Hausdorff convergence to the FLAT d-TORUS in every
dimension (brick T3, torus capstone)

Capstone of the TORUS track (`docs/qg_roadmap/STATE_TORUS_CURVATURE_PLAN.md`).  Bricks T1–T2
pinched the cyclic-stencil hop metric on the d-dimensional wrap-around lattice
`Fin d → ZMod N` against the flat continuum d-torus and proved the uniform distortion bound
`torusD_dist_sub_le` with vanishing error `torusDistortionError d N`.  This file upgrades that
*embedded, coordinatewise* comparison to the genuine INTRINSIC statement: for EVERY dimension
`d`, the finite cyclic lattices, metrized by the **scaled stencil hop metric**
`(R_N/N)·dist_hop` — abstract finite metric spaces, NOT subsets of any ambient continuum —
converge in Mathlib's Gromov–Hausdorff space to the FLAT d-TORUS
`FlatTorus d = PiLp 2 (fun _ : Fin d => AddCircle 1)`:

    toGHSpace (ScaledTorusD d N) ⟶ toGHSpace (FlatTorus d)
                                          (`torusD_toGHSpace_tendsto_flatTorus`)

via the quantitative bound
`ghDist (ScaledTorusD d N) (FlatTorus d) ≤ torusDistortionError d (N+1)/2 + margin d/(N+1)`
(`ghDist_torusD_le`), riding Mathlib's `ghDist_le_of_approx_subsets` with the lattice
embedding `embT` as the approximate isometry and wrap-aware round-to-nearest as the
`margin d/(N+1)`-net (`flatTorus_net`).  This is the SAME intrinsic graph-geodesic machine as
the cube capstone (`QIQTH/StencilDimGH.lean`, brick G4) — what changes in the LIMIT is the
GLOBAL TOPOLOGY (no boundary, nontrivial π₁), demonstrated at the same axiom-free standard.
The headline corollaries are `d = 1` (THE CIRCLE: cycle graphs converge to S¹),
`d = 2`, and `d = 3` (3D space with periodic topology).

## Scope firewall (HONEST)

* **The torus topology is INSERTED through the wrap rule (the `ZMod` cyclic structure) — NOT
  emergent topology**: the theorem shows the machine TRANSPORTS a chosen discrete topology to
  the continuum, not that topology emerges from anything.
* **The dimension `d` is an INPUT — the chosen lattice — NOT emergent**: this theorem holds
  for every `d` and says NOTHING about why physical space is 3-dimensional.
* **The limit is FLAT**: vs the cube capstone the topology changed, the curvature did NOT —
  the flat torus is not a curved Riemannian manifold.
* The edges are microscopic: `R_N = ⌊√N⌋ → ∞` in hops, yet `R_N/N → 0` in the scaled metric.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.TorusStencilWalk
import QIQTH.StencilDimGH
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

namespace QIQTH.TorusStencilGH

open QIQTH.StencilDimGraph QIQTH.TorusStencilGraph QIQTH.TorusStencilWalk QIQTH.StencilDimGH
  Filter Topology

/-! ## Part 1 — the intrinsic scaled cyclic-stencil space

The lattice size is `N + 1` throughout, so `NeZero (N + 1)` always holds and every statement
is total in `N` (for `N = 0` the lattice is the singleton `ZMod 1` per coordinate, where the
graph is trivially connected since `stencilRD ≥ margin d + 1`). -/

/-- **The scaled cyclic-stencil space**: a type synonym for the d-dimensional wrap-around
lattice `Fin d → ZMod (N + 1)`, carrying the intrinsic scaled hop metric
`(R_{N+1}/(N+1))·dist_hop` (the synonym keeps the instance from clashing with any inherited pi
metric). -/
def ScaledTorusD (d N : ℕ) : Type := Fin d → ZMod (N + 1)

/-- View a scaled-torus point as a cyclic-lattice point. -/
def ScaledTorusD.pt {d N : ℕ} (x : ScaledTorusD d N) : Fin d → ZMod (N + 1) := x

/-- View a cyclic-lattice point as a scaled-torus point. -/
def toScaledT {d N : ℕ} (x : Fin d → ZMod (N + 1)) : ScaledTorusD d N := x

instance (d N : ℕ) : Nonempty (ScaledTorusD d N) :=
  inferInstanceAs (Nonempty (Fin d → ZMod (N + 1)))

instance (d N : ℕ) : Fintype (ScaledTorusD d N) :=
  inferInstanceAs (Fintype (Fin d → ZMod (N + 1)))

instance (d N : ℕ) : DecidableEq (ScaledTorusD d N) :=
  inferInstanceAs (DecidableEq (Fin d → ZMod (N + 1)))

instance (d N : ℕ) : Finite (ScaledTorusD d N) :=
  inferInstanceAs (Finite (Fin d → ZMod (N + 1)))

/-! ## Part 2 — the intrinsic scaled cyclic-stencil metric space -/

/-- **The intrinsic scaled cyclic-stencil metric**: `dist x y = (R/(N+1)) · hopdist x y` with
`R = stencilRD d (N+1) ≥ margin d + 1`, so the cyclic stencil graph is connected
(`torusD_reachable`, brick T2) and the scaled hop metric is a genuine metric with no side
conditions — `NeZero (N + 1)` always holds. -/
noncomputable instance instMetricSpaceScaledTorusD (d N : ℕ) :
    MetricSpace (ScaledTorusD d N) where
  dist x y := ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
      * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ)
  dist_self x := by
    show ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
        * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt x.pt : ℝ) = 0
    rw [SimpleGraph.dist_self]
    simp
  dist_comm x y := by
    show ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
        * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ)
      = ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
        * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist y.pt x.pt : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
        * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt z.pt : ℝ)
      ≤ ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
          * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ)
        + ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
          * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist y.pt z.pt : ℝ)
    have htri : (torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt z.pt
        ≤ (torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt
          + (torusGraphD d (N + 1) (stencilRD d (N + 1))).dist y.pt z.pt :=
      (torusD_reachable (marginSucc_le_stencilRD d (N + 1)) y.pt z.pt).dist_triangle_right x.pt
    have hcast : ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt z.pt : ℝ)
        ≤ ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ)
          + ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist y.pt z.pt : ℝ) := by
      exact_mod_cast htri
    have hscale : (0 : ℝ) ≤ (stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) := by positivity
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hcast hscale
  eq_of_dist_eq_zero := by
    intro x y h
    have h' : ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
        * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ) = 0 := h
    have hm := marginSucc_le_stencilRD d (N + 1)
    have hRpos : (0 : ℝ) < (stencilRD d (N + 1) : ℝ) := by
      exact_mod_cast (by omega : 0 < stencilRD d (N + 1))
    have hNr : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < N + 1)
    have hscale : (0 : ℝ) < (stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ) :=
      div_pos hRpos hNr
    have hg : ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ) = 0 :=
      (mul_eq_zero.mp h').resolve_left hscale.ne'
    have hg0 : (torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt = 0 := by
      exact_mod_cast hg
    exact ((torusD_reachable (marginSucc_le_stencilRD d (N + 1)) x.pt y.pt).dist_eq_zero_iff).mp
      hg0

instance (d N : ℕ) : CompactSpace (ScaledTorusD d N) := Finite.compactSpace

/-- The scaled cyclic-stencil distance, unfolded. -/
lemma scaledTorusD_dist_eq {d N : ℕ} (x y : ScaledTorusD d N) :
    dist x y = ((stencilRD d (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
      * ((torusGraphD d (N + 1) (stencilRD d (N + 1))).dist x.pt y.pt : ℝ) := rfl

/-! ## Part 3 — the approximate isometry into the flat d-torus

The continuum target is the WHOLE flat d-torus `FlatTorus d` of brick T1 — a compact nonempty
metric space (T1's instances) — so no subtype is needed, unlike the cube. -/

/-- **The approximate isometry** `ΦembT d N : ScaledTorusD d N → FlatTorus d`: T1's lattice
embedding `embT`, coordinate `i` landing at the class of `(x i).val/(N+1)` on the unit
circle. -/
noncomputable def ΦembT (d N : ℕ) (x : ScaledTorusD d N) : FlatTorus d :=
  embT d (N + 1) x.pt

/-- The embedded distance is T1's flat-torus distance between the embedded lattice points. -/
lemma dist_ΦembT {d N : ℕ} (x y : ScaledTorusD d N) :
    dist (ΦembT d N x) (ΦembT d N y)
      = dist (embT d (N + 1) x.pt) (embT d (N + 1) y.pt) := rfl

/-! ## Part 4 — the lattice is a `margin d/(N+1)`-net of the flat torus -/

/-- **Per-coordinate rounding error on the circle.**  For any real representative `r`, the
wrap-aware round `round (M·r)` cast into `ZMod M` (the mod-`M` cast absorbs any wrapping — no
clamp, the torus has no boundary) lands within `1/(2M)` of the class of `r`: the difference
class has representative `r − round(M·r)/M` of absolute value `≤ 1/(2M) ≤ 1/2`, where the
circle norm IS the absolute value (`AddCircle.norm_coe_eq_abs_iff`, the T1 route). -/
private lemma coord_err {M : ℕ} [NeZero M] (r : ℝ) :
    dist ((r : ℝ) : AddCircle (1 : ℝ))
        (ZMod.toAddCircle ((round ((M : ℝ) * r) : ℤ) : ZMod M))
      ≤ 1 / (2 * (M : ℝ)) := by
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hround : |(M : ℝ) * r - ((round ((M : ℝ) * r) : ℤ) : ℝ)| ≤ 1 / 2 :=
    abs_sub_round ((M : ℝ) * r)
  have herr : |r - ((round ((M : ℝ) * r) : ℤ) : ℝ) / (M : ℝ)| ≤ 1 / (2 * (M : ℝ)) := by
    have key : r - ((round ((M : ℝ) * r) : ℤ) : ℝ) / (M : ℝ)
        = ((M : ℝ) * r - ((round ((M : ℝ) * r) : ℤ) : ℝ)) / (M : ℝ) := by
      field_simp
    rw [key, abs_div, abs_of_pos hM,
      show (1 : ℝ) / (2 * (M : ℝ)) = 1 / 2 / (M : ℝ) from (div_div 1 2 (M : ℝ)).symm,
      div_le_div_iff_of_pos_right hM]
    exact hround
  have hhalf : |r - ((round ((M : ℝ) * r) : ℤ) : ℝ) / (M : ℝ)| ≤ |(1 : ℝ)| / 2 := by
    have h2M : (1 : ℝ) / (2 * (M : ℝ)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le two_pos (by linarith)
    rw [abs_one]
    linarith
  rw [dist_eq_norm, ZMod.toAddCircle_intCast, ← QuotientAddGroup.mk_sub,
    (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr hhalf]
  exact herr

/-- **Per-coordinate net**: every point of the circle `AddCircle 1` is within `1/(2M)` of an
embedded `ZMod M` lattice coordinate — take the `[0,1)` representative (`AddCircle.equivIco`)
and round wrap-aware. -/
private lemma coord_net {M : ℕ} [NeZero M] (z : AddCircle (1 : ℝ)) :
    ∃ a : ZMod M, dist z (ZMod.toAddCircle a) ≤ 1 / (2 * (M : ℝ)) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, ((r : ℝ) : AddCircle (1 : ℝ)) = z :=
    ⟨(AddCircle.equivIco 1 0 z : ℝ), AddCircle.coe_equivIco⟩
  refine ⟨((round ((M : ℝ) * r) : ℤ) : ZMod M), ?_⟩
  rw [← hr]
  exact coord_err r

/-- The `d` per-coordinate circle errors of `1/(2(N+1))` combine through the L² formula to
`√d/(2(N+1)) ≤ margin d/(N+1)`. -/
private lemma dist_ΦembT_le {d N : ℕ} (p : FlatTorus d) (x : ScaledTorusD d N)
    (he : ∀ i, dist (p i) (embT d (N + 1) x.pt i) ≤ 1 / (2 * ((N + 1 : ℕ) : ℝ))) :
    dist p (ΦembT d N x) ≤ (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have hNr : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < N + 1)
  have hkey : dist p (ΦembT d N x)
      = Real.sqrt (∑ i, dist (p i) (embT d (N + 1) x.pt i) ^ 2) :=
    PiLp.dist_eq_of_L2 p (embT d (N + 1) x.pt)
  rw [hkey]
  have hterm : ∀ i : Fin d,
      dist (p i) (embT d (N + 1) x.pt i) ^ 2 ≤ (1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ 2 := by
    intro i
    have h0 : (0 : ℝ) ≤ dist (p i) (embT d (N + 1) x.pt i) := dist_nonneg
    have h1 := he i
    nlinarith
  have hsum : (∑ i, dist (p i) (embT d (N + 1) x.pt i) ^ 2)
      ≤ (d : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ 2 := by
    calc (∑ i, dist (p i) (embT d (N + 1) x.pt i) ^ 2)
        ≤ ∑ _i : Fin d, (1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (∑ i, dist (p i) (embT d (N + 1) x.pt i) ^ 2)
      ≤ Real.sqrt ((d : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ (margin d : ℝ) * (1 / (2 * ((N + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (sqrt_le_margin d) (by positivity)
    _ ≤ (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hNr]
        nlinarith [hNr.le, hm0]

/-- **The net lemma.**  Every point of the flat d-torus is within `margin d/(N+1)` of an
embedded cyclic-lattice point — take the `[0,1)` representative of each coordinate, round
wrap-aware to the nearest of `N+1` lattice positions (the mod-`(N+1)` cast absorbs the
wrap — no clamp, no boundary); the `d` per-coordinate errors of `1/(2(N+1))` combine to
`√d/(2(N+1)) ≤ margin d/(N+1)`. -/
theorem flatTorus_net (d N : ℕ) (p : FlatTorus d) :
    ∃ x : ScaledTorusD d N, dist p (ΦembT d N x) ≤ (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  choose a ha using fun i : Fin d => coord_net (M := N + 1) (p i)
  refine ⟨toScaledT a, dist_ΦembT_le p (toScaledT a) fun i => ?_⟩
  have h : dist (p i) (embT d (N + 1) a i) ≤ 1 / (2 * ((N + 1 : ℕ) : ℝ)) := by
    rw [embT_apply_eq_toAddCircle d (N + 1) a i]
    exact ha i
  exact h

/-! ## Part 5 — the quantitative Gromov–Hausdorff bound -/

/-- **THE T3 BOUND.**  For `N + 1 ≥ (margin d + 1)²`, the Gromov–Hausdorff distance between
the intrinsic scaled cyclic-stencil space and the flat d-torus is at most
`torusDistortionError d (N+1)/2 + margin d/(N+1)`: the lattice embedding `embT` is a
`torusDistortionError d (N+1)`-approximate isometry (brick T2) whose image is a
`margin d/(N+1)`-net of the torus. -/
theorem ghDist_torusD_le {d N : ℕ} (hN : (margin d + 1) ^ 2 ≤ N + 1) :
    GromovHausdorff.ghDist (ScaledTorusD d N) (FlatTorus d)
      ≤ torusDistortionError d (N + 1) / 2 + (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
  have key : GromovHausdorff.ghDist (ScaledTorusD d N) (FlatTorus d)
      ≤ 0 + torusDistortionError d (N + 1) / 2 + (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (ScaledTorusD d N))) (fun z => ΦembT d N z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := flatTorus_net d N q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (ΦembT d N x) (ΦembT d N y)| ≤ torusDistortionError d (N + 1)
      rw [dist_ΦembT, scaledTorusD_dist_eq, stencilRD_eq_sqrt hN]
      exact torusD_dist_sub_le hN x.pt y.pt
  linarith

/-! ## Part 6 — the T3 capstone -/

/-- **THE T3 CAPSTONE (Gromov–Hausdorff convergence to the FLAT d-TORUS, EVERY dimension).**
For every fixed dimension `d`, the intrinsic scaled cyclic-stencil metric spaces — abstract
finite metric spaces built from graph geodesics, with no ambient continuum — converge in
Gromov–Hausdorff space to the flat d-torus `(ℝ/ℤ)ᵈ` with the L² metric.  Same machine as the
cube capstone; what changes in the limit is the GLOBAL TOPOLOGY (no boundary, nontrivial π₁),
which is INSERTED through the wrap rule, not emergent (see the scope firewall in the
header). -/
theorem torusD_toGHSpace_tendsto_flatTorus (d : ℕ) :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD d N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (FlatTorus d))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ N : ℕ in atTop,
      dist (GromovHausdorff.toGHSpace (ScaledTorusD d N))
          (GromovHausdorff.toGHSpace (FlatTorus d))
        ≤ torusDistortionError d (N + 1) / 2 + (margin d : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop ((margin d + 1) ^ 2)] with N hN
    exact ghDist_torusD_le (le_trans hN (Nat.le_succ N))
  have hub : Tendsto (fun N : ℕ => torusDistortionError d (N + 1) / 2
      + (margin d : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
    have h1 : Tendsto (fun N : ℕ => torusDistortionError d (N + 1) / 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => torusDistortionError d (N + 1)) atTop (𝓝 0) :=
        (torusDistortionError_tendsto_zero d).comp hshift
      simpa using h0.div_const 2
    have h2 : Tendsto (fun N : ℕ => (margin d : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat.comp hshift
      have h4 : Tendsto (fun N : ℕ => (margin d : ℝ) * ((1 : ℝ) / ((N + 1 : ℕ) : ℝ))) atTop
          (𝓝 ((margin d : ℝ) * 0)) := h3.const_mul (margin d : ℝ)
      simpa [mul_one_div] using h4
    simpa using h1.add h2
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) hbound hub

/-! ## Part 7 — the headline corollaries -/

/-- **THE CIRCLE (d = 1)**: the scaled cyclic-stencil lattices on `ZMod (N+1)` — the cycle
graphs with microscopic stencil — converge in Gromov–Hausdorff space to the circle
`S¹ = ℝ/ℤ`, the 1-torus.  The simplest nontrivial-topology instance of the torus capstone. -/
theorem torus1D_toGHSpace_tendsto_circle :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD 1 N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (FlatTorus 1))) :=
  torusD_toGHSpace_tendsto_flatTorus 1

/-- The `d = 2` instance: the scaled cyclic-stencil lattices converge to the flat 2-torus. -/
theorem torus2D_toGHSpace_tendsto_flatTorus :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD 2 N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (FlatTorus 2))) :=
  torusD_toGHSpace_tendsto_flatTorus 2

/-- **THE HEADLINE (d = 3)**: the 3-dimensional scaled cyclic-stencil lattices converge in
Gromov–Hausdorff space to the flat 3-torus — 3D space with periodic topology.  (The dimension
3 and the periodic topology are both CHOSEN here, not derived.) -/
theorem torus3D_toGHSpace_tendsto_flatTorus :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD 3 N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace (FlatTorus 3))) :=
  torusD_toGHSpace_tendsto_flatTorus 3

end QIQTH.TorusStencilGH
