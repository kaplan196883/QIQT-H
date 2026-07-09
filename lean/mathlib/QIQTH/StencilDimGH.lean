/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# DIMENSION-GENERIC STENCIL GH LIMIT — Gromov–Hausdorff convergence to the Euclidean unit cube
in EVERY dimension (brick G4, campaign capstone)

Capstone of the DIMENSION-GENERIC STENCIL campaign
(`docs/qg_roadmap/DIM_GENERIC_STENCIL_PLAN.md`).  Bricks G1–G3 pinched the d-dimensional
stencil hop metric between Euclidean multiples and proved the uniform distortion bound
`scaledD_dist_sub_euclD_le` with vanishing error `distortionErrorD d N`.  This file upgrades
that *embedded, coordinatewise* comparison to the genuine INTRINSIC statement: for EVERY
dimension `d`, the finite lattices `Fin d → Fin (N+1)`, metrized by the **scaled stencil hop
metric** `(R_N/N)·dist_hop` — abstract finite metric spaces, NOT subsets of ℝᵈ — converge in
Mathlib's Gromov–Hausdorff space to the EUCLIDEAN unit cube `([0,1]ᵈ, ‖·‖₂)`:

    toGHSpace (ScaledStencilD d N) ⟶ toGHSpace ↥(unitCube d)
                                            (`stencilD_toGHSpace_tendsto_unitCube`)

via the quantitative bound
`ghDist (ScaledStencilD d N) ↥(unitCube d) ≤ distortionErrorD d N/2 + margin d/N`
(`ghDist_stencilD_le`), riding Mathlib's `ghDist_le_of_approx_subsets` with the lattice
embedding `x ↦ x/N` as the approximate isometry and coordinatewise round-to-nearest as the
`margin d/N`-net.  The physical headline `d = 3` is the explicit corollary
`stencil3D_toGHSpace_tendsto_unitCube` (and `d = 2` recovers the I4 statement).

## Scope firewall (HONEST)

* **The dimension `d` is an INPUT — the chosen lattice — NOT emergent: this theorem holds for
  every `d` and says NOTHING about why physical space is 3-dimensional.**
* **The isotropy is inserted through the stencil rule**: the Euclidean-ball edge test
  `sqDistD ≤ R²` selects the edges.  The hop metric is intrinsic and the GH limit genuinely
  Euclidean, but this is NOT isotropy emerging from a fixed local combinatorial rule
  (impossible, per `IsotropyNoGo`) and NOT isotropy emerging from dynamics (the cited wall).
* The edges are microscopic: `R_N = ⌊√N⌋ → ∞` in hops, yet `R_N/N → 0` in the scaled metric.
* The limit is the FLAT cube — not a curved Riemannian manifold; NOT emergent topology, NOT
  GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilDimDistortion
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic

namespace QIQTH.StencilDimGH

open QIQTH.StencilDimGraph QIQTH.StencilDimWalk QIQTH.StencilDimDistortion Filter Topology

/-! ## Part 1 — the stencil-radius schedule, totalized -/

/-- **The stencil-radius schedule** `R_N = max (margin d + 1) ⌊√N⌋`: equal to the microscopic
stencil `⌊√N⌋` in the limit regime `N ≥ (margin d + 1)²`, but always `≥ margin d + 1` so the
stencil graph is connected for EVERY `N` and the scaled hop metric is a genuine metric space
with no side conditions. -/
def stencilRD (d N : ℕ) : ℕ := max (margin d + 1) (Nat.sqrt N)

/-- The schedule is always `≥ margin d + 1` — connectivity (`stencilD_reachable`) always
fires. -/
lemma marginSucc_le_stencilRD (d N : ℕ) : margin d + 1 ≤ stencilRD d N := le_max_left _ _

/-- In the limit regime `N ≥ (margin d + 1)²` the schedule IS the microscopic stencil `⌊√N⌋`
of brick G3. -/
lemma stencilRD_eq_sqrt {d N : ℕ} (hN : (margin d + 1) ^ 2 ≤ N) :
    stencilRD d N = Nat.sqrt N :=
  max_eq_right (Nat.le_sqrt.mpr (by rw [← pow_two]; exact hN))

/-! ## Part 2 — the intrinsic scaled stencil metric space -/

/-- **The scaled stencil space**: a type synonym for the d-dimensional lattice
`Fin d → Fin (N+1)`, carrying the intrinsic scaled hop metric `(R_N/N)·dist_hop` (the synonym
keeps the instance from clashing with any inherited pi metric). -/
def ScaledStencilD (d N : ℕ) : Type := Fin d → Fin (N + 1)

/-- View a scaled-stencil point as a lattice point. -/
def ScaledStencilD.pt {d N : ℕ} (x : ScaledStencilD d N) : Fin d → Fin (N + 1) := x

/-- View a lattice point as a scaled-stencil point. -/
def toScaledD {d N : ℕ} (x : Fin d → Fin (N + 1)) : ScaledStencilD d N := x

instance (d N : ℕ) : Nonempty (ScaledStencilD d N) :=
  inferInstanceAs (Nonempty (Fin d → Fin (N + 1)))

instance (d N : ℕ) : Fintype (ScaledStencilD d N) :=
  inferInstanceAs (Fintype (Fin d → Fin (N + 1)))

instance (d N : ℕ) : DecidableEq (ScaledStencilD d N) :=
  inferInstanceAs (DecidableEq (Fin d → Fin (N + 1)))

instance (d N : ℕ) : Finite (ScaledStencilD d N) :=
  inferInstanceAs (Finite (Fin d → Fin (N + 1)))

/-- **The intrinsic scaled stencil metric**: `dist x y = (R_N/N) · hopdist x y`.  Connectivity
(`R_N ≥ margin d + 1`, brick G2) gives the triangle inequality and point separation; for
`N = 0` the space is a single point. -/
noncomputable instance instMetricSpaceScaledStencilD (d N : ℕ) :
    MetricSpace (ScaledStencilD d N) where
  dist x y := ((stencilRD d N : ℝ) / (N : ℝ))
      * ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ)
  dist_self x := by
    show ((stencilRD d N : ℝ) / (N : ℝ))
        * ((stencilGraphD d N (stencilRD d N)).dist x.pt x.pt : ℝ) = 0
    rw [SimpleGraph.dist_self]
    simp
  dist_comm x y := by
    show ((stencilRD d N : ℝ) / (N : ℝ))
        * ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ)
      = ((stencilRD d N : ℝ) / (N : ℝ))
        * ((stencilGraphD d N (stencilRD d N)).dist y.pt x.pt : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show ((stencilRD d N : ℝ) / (N : ℝ))
        * ((stencilGraphD d N (stencilRD d N)).dist x.pt z.pt : ℝ)
      ≤ ((stencilRD d N : ℝ) / (N : ℝ))
          * ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ)
        + ((stencilRD d N : ℝ) / (N : ℝ))
          * ((stencilGraphD d N (stencilRD d N)).dist y.pt z.pt : ℝ)
    have htri : (stencilGraphD d N (stencilRD d N)).dist x.pt z.pt
        ≤ (stencilGraphD d N (stencilRD d N)).dist x.pt y.pt
          + (stencilGraphD d N (stencilRD d N)).dist y.pt z.pt :=
      (stencilD_reachable (marginSucc_le_stencilRD d N) y.pt z.pt).dist_triangle_right x.pt
    have hcast : ((stencilGraphD d N (stencilRD d N)).dist x.pt z.pt : ℝ)
        ≤ ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ)
          + ((stencilGraphD d N (stencilRD d N)).dist y.pt z.pt : ℝ) := by exact_mod_cast htri
    have hscale : (0 : ℝ) ≤ (stencilRD d N : ℝ) / (N : ℝ) := by positivity
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hcast hscale
  eq_of_dist_eq_zero := by
    intro x y h
    have h' : ((stencilRD d N : ℝ) / (N : ℝ))
        * ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ) = 0 := h
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · haveI : Subsingleton (ScaledStencilD d 0) :=
        inferInstanceAs (Subsingleton (Fin d → Fin 1))
      exact Subsingleton.elim x y
    · have hm := marginSucc_le_stencilRD d N
      have hRpos : (0 : ℝ) < (stencilRD d N : ℝ) := by
        exact_mod_cast (by omega : 0 < stencilRD d N)
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hscale : (0 : ℝ) < (stencilRD d N : ℝ) / (N : ℝ) := by positivity
      have hg : ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ) = 0 :=
        (mul_eq_zero.mp h').resolve_left hscale.ne'
      have hg0 : (stencilGraphD d N (stencilRD d N)).dist x.pt y.pt = 0 := by exact_mod_cast hg
      have hpt : x.pt = y.pt :=
        ((stencilD_reachable (marginSucc_le_stencilRD d N) x.pt y.pt).dist_eq_zero_iff).mp hg0
      exact hpt

instance (d N : ℕ) : CompactSpace (ScaledStencilD d N) := Finite.compactSpace

/-- The scaled stencil distance, unfolded. -/
lemma scaledStencilD_dist_eq {d N : ℕ} (x y : ScaledStencilD d N) :
    dist x y = ((stencilRD d N : ℝ) / (N : ℝ))
      * ((stencilGraphD d N (stencilRD d N)).dist x.pt y.pt : ℝ) := rfl

/-! ## Part 3 — the target: the Euclidean unit cube -/

/-- **The unit cube** `[0,1]ᵈ ⊂ (ℝᵈ, ‖·‖₂)` — the continuum target, with the EUCLIDEAN
(not taxicab) metric inherited from `EuclideanSpace ℝ (Fin d)`. -/
def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {p | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1}

/-- The unit cube is closed (an intersection of coordinate preimages of `[0,1]`). -/
lemma unitCube_isClosed (d : ℕ) : IsClosed (unitCube d) := by
  have h : unitCube d = ⋂ i : Fin d,
      (fun p : EuclideanSpace ℝ (Fin d) => p i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext p
    simp only [unitCube, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (by fun_prop)

/-- The unit cube sits inside the closed ball of radius `margin d + 1`
(`‖p‖ ≤ √d ≤ margin d ≤ margin d + 1`). -/
lemma unitCube_subset_closedBall (d : ℕ) :
    unitCube d ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) ((margin d : ℝ) + 1) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  have hcoord : ∀ i : Fin d, ‖p i‖ ^ 2 ≤ 1 := by
    intro i
    have hi := hp i
    have hle : ‖p i‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [hi.1], hi.2⟩
    nlinarith [norm_nonneg (p i)]
  have hsum : (∑ i, ‖p i‖ ^ 2) ≤ (d : ℝ) := by
    calc (∑ i, ‖p i‖ ^ 2) ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖p i‖ ^ 2)
      ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt hsum
    _ ≤ (margin d : ℝ) := sqrt_le_margin d
    _ ≤ (margin d : ℝ) + 1 := by linarith

/-- **The unit cube is compact** (closed and bounded in a proper space). -/
theorem unitCube_isCompact (d : ℕ) : IsCompact (unitCube d) :=
  Metric.isCompact_of_isClosed_isBounded (unitCube_isClosed d)
    (Metric.isBounded_closedBall.subset (unitCube_subset_closedBall d))

/-- The unit cube is nonempty (it contains the origin). -/
theorem unitCube_nonempty (d : ℕ) : (unitCube d).Nonempty :=
  ⟨0, fun i => by simp⟩

instance (d : ℕ) : CompactSpace ↥(unitCube d) :=
  isCompact_iff_compactSpace.mp (unitCube_isCompact d)

instance (d : ℕ) : Nonempty ↥(unitCube d) := (unitCube_nonempty d).to_subtype

/-! ## Part 4 — the approximate isometry `x ↦ x/N` -/

private lemma coord_mem {N a : ℕ} (ha : a ≤ N) :
    (N : ℝ)⁻¹ * (a : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · obtain rfl : a = 0 := Nat.le_zero.mp ha
    simp
  · have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
    refine Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    rw [← div_eq_inv_mul, div_le_one hNr]
    exact_mod_cast ha

/-- The scaled lattice embedding lands in the unit cube. -/
lemma smul_embD_mem_unitCube {d N : ℕ} (x : Fin d → Fin (N + 1)) :
    (N : ℝ)⁻¹ • embD d N x ∈ unitCube d := by
  intro i
  show (N : ℝ)⁻¹ * ((x i : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1
  exact coord_mem (Nat.lt_succ_iff.mp (x i).isLt)

/-- **The approximate isometry** `ΦembD d N : ScaledStencilD d N → [0,1]ᵈ`, `x ↦ x/N`. -/
noncomputable def ΦembD (d N : ℕ) (x : ScaledStencilD d N) : ↥(unitCube d) :=
  ⟨(N : ℝ)⁻¹ • embD d N x.pt, smul_embD_mem_unitCube x.pt⟩

/-- The embedded distance is the scaled Euclidean lattice distance `euclD/N`.  (The hypothesis
`1 ≤ N` is kept for interface uniformity with the other bricks; Lean's `x/0 = 0` convention
happens to make the statement true for `N = 0` as well.) -/
lemma dist_ΦembD {d N : ℕ} (_hN : 1 ≤ N) (x y : ScaledStencilD d N) :
    dist (ΦembD d N x) (ΦembD d N y) = euclD d N x.pt y.pt / (N : ℝ) := by
  rw [Subtype.dist_eq]
  show dist ((N : ℝ)⁻¹ • embD d N x.pt) ((N : ℝ)⁻¹ • embD d N y.pt)
      = euclD d N x.pt y.pt / (N : ℝ)
  rw [dist_smul₀, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_mul_eq_div]
  rfl

/-! ## Part 5 — the lattice is a `margin d/N`-net of the cube -/

private lemma round_mul_mem {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    0 ≤ round ((N : ℝ) * c) ∧ round ((N : ℝ) * c) ≤ (N : ℤ) := by
  have hr := abs_le.mp (abs_sub_round ((N : ℝ) * c))
  have h0 : (0 : ℝ) ≤ (N : ℝ) * c := mul_nonneg (Nat.cast_nonneg N) hc0
  have hNc : (N : ℝ) * c ≤ (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hc1 (show (0 : ℝ) ≤ (N : ℝ) by positivity)
    simpa using this
  constructor
  · have h1 : (-1 : ℝ) < ((round ((N : ℝ) * c) : ℤ) : ℝ) := by linarith [hr.2]
    have h2 : (-1 : ℤ) < round ((N : ℝ) * c) := by exact_mod_cast h1
    omega
  · have h1 : ((round ((N : ℝ) * c) : ℤ) : ℝ) < (N : ℝ) + 1 := by linarith [hr.1]
    have h2 : round ((N : ℝ) * c) < (N : ℤ) + 1 := by exact_mod_cast h1
    omega

private lemma coord_round_err {N : ℕ} (hNr : (0 : ℝ) < (N : ℝ)) (c : ℝ)
    (hr : 0 ≤ round ((N : ℝ) * c)) :
    |c - (N : ℝ)⁻¹ * (((round ((N : ℝ) * c)).toNat : ℕ) : ℝ)| ≤ 1 / (2 * (N : ℝ)) := by
  have hne : (N : ℝ) ≠ 0 := hNr.ne'
  have hcast : (((round ((N : ℝ) * c)).toNat : ℕ) : ℝ) = ((round ((N : ℝ) * c) : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hr
  have hround : |(N : ℝ) * c - ((round ((N : ℝ) * c) : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round _
  have key : c - (N : ℝ)⁻¹ * ((round ((N : ℝ) * c) : ℤ) : ℝ)
      = ((N : ℝ) * c - ((round ((N : ℝ) * c) : ℤ) : ℝ)) / (N : ℝ) := by
    field_simp
  rw [hcast, key, abs_div, abs_of_pos hNr,
    show (1 : ℝ) / (2 * (N : ℝ)) = 1 / 2 / (N : ℝ) from (div_div 1 2 (N : ℝ)).symm,
    div_le_div_iff_of_pos_right hNr]
  exact hround

private lemma dist_ΦembD_le {d N : ℕ} (hN : 1 ≤ N) (p : ↥(unitCube d))
    (k : Fin d → ℕ) (hk : ∀ i, k i ≤ N)
    (he : ∀ i, |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)|
      ≤ 1 / (2 * (N : ℝ))) :
    dist p (ΦembD d N (toScaledD fun i => ⟨k i, Nat.lt_succ_of_le (hk i)⟩))
      ≤ (margin d : ℝ) / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkey : dist p (ΦembD d N (toScaledD fun i => ⟨k i, Nat.lt_succ_of_le (hk i)⟩))
      = Real.sqrt
          (∑ i, |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)| ^ 2) := by
    rw [Subtype.dist_eq, EuclideanSpace.dist_eq]
    congr 1
  rw [hkey]
  have hterm : ∀ i : Fin d,
      |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)| ^ 2
        ≤ (1 / (2 * (N : ℝ))) ^ 2 := fun i => by
    nlinarith [he i, abs_nonneg ((p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ))]
  have hsum : (∑ i, |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)| ^ 2)
      ≤ (d : ℝ) * (1 / (2 * (N : ℝ))) ^ 2 := by
    calc (∑ i, |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)| ^ 2)
        ≤ ∑ _i : Fin d, (1 / (2 * (N : ℝ))) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * (1 / (2 * (N : ℝ))) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hm0 : (0 : ℝ) ≤ (margin d : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (∑ i, |(p : EuclideanSpace ℝ (Fin d)) i - (N : ℝ)⁻¹ * (k i : ℝ)| ^ 2)
      ≤ Real.sqrt ((d : ℝ) * (1 / (2 * (N : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * (1 / (2 * (N : ℝ))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ (margin d : ℝ) * (1 / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right (sqrt_le_margin d) (by positivity)
    _ ≤ (margin d : ℝ) / (N : ℝ) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hNr]
        nlinarith [hNr.le, hm0]

/-- **The net lemma.**  Every point of the unit cube is within `margin d/N` of an embedded
lattice point — round each coordinate to the nearest lattice index; the `d` per-coordinate
errors of `1/(2N)` combine to `√d/(2N) ≤ margin d/N`. -/
theorem unitCubeD_net {d N : ℕ} (hN : 1 ≤ N) (p : ↥(unitCube d)) :
    ∃ x : ScaledStencilD d N, dist p (ΦembD d N x) ≤ (margin d : ℝ) / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmem : ∀ i : Fin d, (p : EuclideanSpace ℝ (Fin d)) i ∈ Set.Icc (0 : ℝ) 1 := p.2
  have hround : ∀ i : Fin d,
      0 ≤ round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin d)) i) ∧
        round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin d)) i) ≤ (N : ℤ) :=
    fun i => round_mul_mem (hmem i).1 (hmem i).2
  have hk : ∀ i : Fin d,
      (round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin d)) i)).toNat ≤ N := by
    intro i
    have := hround i
    omega
  exact ⟨toScaledD fun i =>
      ⟨(round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin d)) i)).toNat,
        Nat.lt_succ_of_le (hk i)⟩,
    dist_ΦembD_le hN p _ hk fun i => coord_round_err hNr _ (hround i).1⟩

/-! ## Part 6 — the quantitative Gromov–Hausdorff bound -/

/-- **THE G4 BOUND.**  For `N ≥ (margin d + 1)²`, the Gromov–Hausdorff distance between the
intrinsic scaled stencil space and the Euclidean unit cube is at most
`distortionErrorD d N / 2 + margin d/N`: the lattice embedding `x ↦ x/N` is a
`distortionErrorD d N`-approximate isometry (brick G3) whose image is a `margin d/N`-net of
the cube. -/
theorem ghDist_stencilD_le {d N : ℕ} (hN : (margin d + 1) ^ 2 ≤ N) :
    GromovHausdorff.ghDist (ScaledStencilD d N) ↥(unitCube d)
      ≤ distortionErrorD d N / 2 + (margin d : ℝ) / (N : ℝ) := by
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow 2 (margin d + 1) (by omega)) hN
  have key : GromovHausdorff.ghDist (ScaledStencilD d N) ↥(unitCube d)
      ≤ 0 + distortionErrorD d N / 2 + (margin d : ℝ) / (N : ℝ) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (ScaledStencilD d N))) (fun z => ΦembD d N z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := unitCubeD_net hN1 q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (ΦembD d N x) (ΦembD d N y)| ≤ distortionErrorD d N
      rw [dist_ΦembD hN1, scaledStencilD_dist_eq, stencilRD_eq_sqrt hN]
      exact scaledD_dist_sub_euclD_le hN x.pt y.pt
  linarith

/-! ## Part 7 — the G4 capstone -/

/-- **THE G4 CAPSTONE (Gromov–Hausdorff convergence to the Euclidean unit cube, EVERY
dimension).**  For every fixed dimension `d`, the intrinsic scaled stencil metric spaces —
abstract finite metric spaces built from graph geodesics, with no ambient ℝᵈ — converge in
Gromov–Hausdorff space to the EUCLIDEAN unit cube `([0,1]ᵈ, ‖·‖₂)`.  A flat d-dimensional
Euclidean continuum limit from hop-counting.  The dimension `d` is an INPUT, not emergent
(see the scope firewall in the header). -/
theorem stencilD_toGHSpace_tendsto_unitCube (d : ℕ) :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD d N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube d))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ N : ℕ in atTop,
      dist (GromovHausdorff.toGHSpace (ScaledStencilD d N))
          (GromovHausdorff.toGHSpace ↥(unitCube d))
        ≤ distortionErrorD d N / 2 + (margin d : ℝ) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop ((margin d + 1) ^ 2)] with N hN
    exact ghDist_stencilD_le hN
  have hub : Tendsto (fun N : ℕ => distortionErrorD d N / 2 + (margin d : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => distortionErrorD d N / 2) atTop (𝓝 0) := by
      simpa using (distortionErrorD_tendsto_zero d).div_const 2
    have h2 : Tendsto (fun N : ℕ => (margin d : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
      have h3 : Tendsto (fun N : ℕ => (margin d : ℝ) * (1 / (N : ℝ))) atTop
          (𝓝 ((margin d : ℝ) * 0)) :=
        tendsto_one_div_atTop_nhds_zero_nat.const_mul (margin d : ℝ)
      simpa [mul_one_div] using h3
    simpa using h1.add h2
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) hbound hub

/-! ## Part 8 — the headline corollaries -/

/-- **THE HEADLINE (d = 3)**: the 3-dimensional scaled stencil lattices converge in
Gromov–Hausdorff space to the Euclidean unit cube `[0,1]³` — the physical-space instance of
the dimension-generic capstone.  (The dimension 3 is CHOSEN here, not derived.) -/
theorem stencil3D_toGHSpace_tendsto_unitCube :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD 3 N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube 3))) :=
  stencilD_toGHSpace_tendsto_unitCube 3

/-- The `d = 2` instance — the dimension-generic capstone recovers the 2D I4 statement. -/
theorem stencil2D_toGHSpace_tendsto_unitCube :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencilD 2 N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace ↥(unitCube 2))) :=
  stencilD_toGHSpace_tendsto_unitCube 2

end QIQTH.StencilDimGH
