/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# STENCIL GH LIMIT — Gromov–Hausdorff convergence to the Euclidean unit square (brick I4, campaign capstone)

Capstone of the ISOTROPY campaign (`docs/qg_roadmap/ISOTROPY_STENCIL_PLAN.md`).  Bricks I1–I3
pinched the stencil hop metric between Euclidean multiples and proved the uniform distortion
bound `scaled_dist_sub_eucl_le` with vanishing error `distortionError N`.  This file upgrades
that *embedded, coordinatewise* comparison to the genuine INTRINSIC statement: the finite
lattices `Fin (N+1) × Fin (N+1)`, metrized by the **scaled stencil hop metric**
`(R_N/N)·dist_hop` — abstract finite metric spaces, NOT subsets of ℝ² — converge in Mathlib's
Gromov–Hausdorff space to the EUCLIDEAN unit square `([0,1]², ‖·‖₂)`:

    toGHSpace (ScaledStencil N) ⟶ toGHSpace ↥unitSquare   (`stencil_toGHSpace_tendsto_unitSquare`)

via the quantitative bound `ghDist (ScaledStencil N) ↥unitSquare ≤ distortionError N/2 + 1/N`
(`ghDist_stencil_le`), riding Mathlib's `ghDist_le_of_approx_subsets` with the lattice
embedding `x ↦ x/N` as the approximate isometry and round-to-nearest as the `1/N`-net.  A flat
Euclidean 2D continuum limit obtained from graph geodesics — the positive complement of the
no-go in `IsotropyNoGo.lean`.

## Scope firewall (HONEST)

* **The isotropy is inserted through the stencil rule**: the Euclidean disk test `sqDist ≤ R²`
  selects the edges.  The hop metric is intrinsic and the GH limit genuinely Euclidean, but
  this is NOT isotropy emerging from a fixed local combinatorial rule (impossible, per the
  no-go) and NOT isotropy emerging from dynamics (the cited wall).
* The edges are microscopic: `R_N = ⌊√N⌋ → ∞` in hops, yet `R_N/N → 0` in the scaled metric.
* The limit is the FLAT square — not a curved Riemannian manifold; NOT emergent
  dimension/topology, NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.StencilDistortion
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic

namespace QIQTH.StencilGH

open QIQTH.StencilGraph QIQTH.StencilWalk QIQTH.StencilDistortion Filter Topology

/-! ## Part 1 — the stencil-radius schedule, totalized -/

/-- **The stencil-radius schedule** `R_N = max 3 ⌊√N⌋`: equal to the microscopic stencil
`⌊√N⌋` in the limit regime `N ≥ 9`, but always `≥ 3` so the stencil graph is connected for
EVERY `N` and the scaled hop metric is a genuine metric space with no side conditions. -/
def stencilR (N : ℕ) : ℕ := max 3 (Nat.sqrt N)

/-- The schedule is always `≥ 3` — connectivity (`stencil_reachable`) always fires. -/
lemma three_le_stencilR (N : ℕ) : 3 ≤ stencilR N := le_max_left _ _

/-- In the limit regime `N ≥ 9` the schedule IS the microscopic stencil `⌊√N⌋` of brick I3. -/
lemma stencilR_eq_sqrt {N : ℕ} (hN : 9 ≤ N) : stencilR N = Nat.sqrt N :=
  max_eq_right (Nat.le_sqrt.mpr (by omega))

/-! ## Part 2 — the intrinsic scaled stencil metric space -/

/-- **The scaled stencil space**: a type synonym for the lattice `Fin (N+1) × Fin (N+1)`,
carrying the intrinsic scaled hop metric `(R_N/N)·dist_hop` (the synonym keeps the instance
from clashing with any inherited product metric). -/
def ScaledStencil (N : ℕ) : Type := Fin (N + 1) × Fin (N + 1)

/-- View a scaled-stencil point as a lattice point. -/
def ScaledStencil.pt {N : ℕ} (x : ScaledStencil N) : Fin (N + 1) × Fin (N + 1) := x

/-- View a lattice point as a scaled-stencil point. -/
def toScaled {N : ℕ} (x : Fin (N + 1) × Fin (N + 1)) : ScaledStencil N := x

instance (N : ℕ) : Nonempty (ScaledStencil N) :=
  inferInstanceAs (Nonempty (Fin (N + 1) × Fin (N + 1)))

instance (N : ℕ) : Fintype (ScaledStencil N) :=
  inferInstanceAs (Fintype (Fin (N + 1) × Fin (N + 1)))

instance (N : ℕ) : DecidableEq (ScaledStencil N) :=
  inferInstanceAs (DecidableEq (Fin (N + 1) × Fin (N + 1)))

instance (N : ℕ) : Finite (ScaledStencil N) :=
  inferInstanceAs (Finite (Fin (N + 1) × Fin (N + 1)))

/-- **The intrinsic scaled stencil metric**: `dist x y = (R_N/N) · hopdist x y`.  Connectivity
(`R_N ≥ 3`, brick I2) gives the triangle inequality and point separation; for `N = 0` the
space is a single point. -/
noncomputable instance instMetricSpaceScaledStencil (N : ℕ) :
    MetricSpace (ScaledStencil N) where
  dist x y := ((stencilR N : ℝ) / (N : ℝ))
      * ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ)
  dist_self x := by
    show ((stencilR N : ℝ) / (N : ℝ))
        * ((stencilGraph N (stencilR N)).dist x.pt x.pt : ℝ) = 0
    rw [SimpleGraph.dist_self]
    simp
  dist_comm x y := by
    show ((stencilR N : ℝ) / (N : ℝ)) * ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ)
      = ((stencilR N : ℝ) / (N : ℝ)) * ((stencilGraph N (stencilR N)).dist y.pt x.pt : ℝ)
    rw [SimpleGraph.dist_comm]
  dist_triangle x y z := by
    show ((stencilR N : ℝ) / (N : ℝ)) * ((stencilGraph N (stencilR N)).dist x.pt z.pt : ℝ)
      ≤ ((stencilR N : ℝ) / (N : ℝ)) * ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ)
        + ((stencilR N : ℝ) / (N : ℝ)) * ((stencilGraph N (stencilR N)).dist y.pt z.pt : ℝ)
    have htri : (stencilGraph N (stencilR N)).dist x.pt z.pt
        ≤ (stencilGraph N (stencilR N)).dist x.pt y.pt
          + (stencilGraph N (stencilR N)).dist y.pt z.pt :=
      (stencil_reachable (three_le_stencilR N) y.pt z.pt).dist_triangle_right x.pt
    have hcast : ((stencilGraph N (stencilR N)).dist x.pt z.pt : ℝ)
        ≤ ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ)
          + ((stencilGraph N (stencilR N)).dist y.pt z.pt : ℝ) := by exact_mod_cast htri
    have hscale : (0 : ℝ) ≤ (stencilR N : ℝ) / (N : ℝ) := by positivity
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hcast hscale
  eq_of_dist_eq_zero := by
    intro x y h
    have h' : ((stencilR N : ℝ) / (N : ℝ))
        * ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ) = 0 := h
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · haveI : Subsingleton (ScaledStencil 0) :=
        inferInstanceAs (Subsingleton (Fin 1 × Fin 1))
      exact Subsingleton.elim x y
    · have h3 := three_le_stencilR N
      have hRpos : (0 : ℝ) < (stencilR N : ℝ) := by
        exact_mod_cast (by omega : 0 < stencilR N)
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hscale : (0 : ℝ) < (stencilR N : ℝ) / (N : ℝ) := by positivity
      have hg : ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ) = 0 :=
        (mul_eq_zero.mp h').resolve_left hscale.ne'
      have hg0 : (stencilGraph N (stencilR N)).dist x.pt y.pt = 0 := by exact_mod_cast hg
      have hpt : x.pt = y.pt :=
        ((stencil_reachable (three_le_stencilR N) x.pt y.pt).dist_eq_zero_iff).mp hg0
      exact hpt

instance (N : ℕ) : CompactSpace (ScaledStencil N) := Finite.compactSpace

/-- The scaled stencil distance, unfolded. -/
lemma scaledStencil_dist_eq {N : ℕ} (x y : ScaledStencil N) :
    dist x y = ((stencilR N : ℝ) / (N : ℝ))
      * ((stencilGraph N (stencilR N)).dist x.pt y.pt : ℝ) := rfl

/-! ## Part 3 — the target: the Euclidean unit square -/

/-- **The unit square** `[0,1]² ⊂ (ℝ², ‖·‖₂)` — the continuum target, with the EUCLIDEAN
(not taxicab) metric inherited from `EuclideanSpace ℝ (Fin 2)`. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, p i ∈ Set.Icc (0 : ℝ) 1}

/-- The unit square is closed (an intersection of coordinate preimages of `[0,1]`). -/
lemma unitSquare_isClosed : IsClosed unitSquare := by
  have h : unitSquare = ⋂ i : Fin 2,
      (fun p : EuclideanSpace ℝ (Fin 2) => p i) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext p
    simp only [unitSquare, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (by fun_prop)

/-- The unit square sits inside the closed ball of radius 2. -/
lemma unitSquare_subset_closedBall :
    unitSquare ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 := by
  intro p hp
  have h0 : p 0 ∈ Set.Icc (0 : ℝ) 1 := hp 0
  have h1 : p 1 ∈ Set.Icc (0 : ℝ) 1 := hp 1
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have e0 : ‖p 0‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [h0.1], h0.2⟩
  have e1 : ‖p 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [h1.1], h1.2⟩
  calc Real.sqrt (‖p 0‖ ^ 2 + ‖p 1‖ ^ 2)
      ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (p 0), norm_nonneg (p 1)])
    _ = 2 := Real.sqrt_sq (by norm_num)

/-- **The unit square is compact** (closed and bounded in a proper space). -/
theorem unitSquare_isCompact : IsCompact unitSquare :=
  Metric.isCompact_of_isClosed_isBounded unitSquare_isClosed
    (Metric.isBounded_closedBall.subset unitSquare_subset_closedBall)

/-- The unit square is nonempty (it contains the origin). -/
theorem unitSquare_nonempty : unitSquare.Nonempty :=
  ⟨0, fun i => by simp⟩

instance : CompactSpace ↥unitSquare := isCompact_iff_compactSpace.mp unitSquare_isCompact

instance : Nonempty ↥unitSquare := unitSquare_nonempty.to_subtype

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

/-- The scaled lattice embedding lands in the unit square. -/
lemma smul_emb_mem_unitSquare {N : ℕ} (x : Fin (N + 1) × Fin (N + 1)) :
    (N : ℝ)⁻¹ • emb N x ∈ unitSquare := by
  have key : ∀ i : Fin 2, ((N : ℝ)⁻¹ • emb N x) i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Fin.forall_fin_two]
    constructor
    · show (N : ℝ)⁻¹ * ((x.1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1
      exact coord_mem (Nat.lt_succ_iff.mp x.1.isLt)
    · show (N : ℝ)⁻¹ * ((x.2 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1
      exact coord_mem (Nat.lt_succ_iff.mp x.2.isLt)
  exact key

/-- **The approximate isometry** `Φemb N : ScaledStencil N → [0,1]²`, `x ↦ x/N`. -/
noncomputable def Φemb (N : ℕ) (x : ScaledStencil N) : ↥unitSquare :=
  ⟨(N : ℝ)⁻¹ • emb N x.pt, smul_emb_mem_unitSquare x.pt⟩

/-- The embedded distance is the scaled Euclidean lattice distance `eucl/N`.  (The hypothesis
`1 ≤ N` is kept for interface uniformity with the other bricks; Lean's `x/0 = 0` convention
happens to make the statement true for `N = 0` as well.) -/
lemma dist_Φemb {N : ℕ} (_hN : 1 ≤ N) (x y : ScaledStencil N) :
    dist (Φemb N x) (Φemb N y) = eucl N x.pt y.pt / (N : ℝ) := by
  rw [Subtype.dist_eq]
  show dist ((N : ℝ)⁻¹ • emb N x.pt) ((N : ℝ)⁻¹ • emb N y.pt)
      = eucl N x.pt y.pt / (N : ℝ)
  rw [dist_smul₀, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_mul_eq_div]
  rfl

/-! ## Part 5 — the lattice is a `1/N`-net of the square -/

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

private lemma dist_Φemb_le {N : ℕ} (hN : 1 ≤ N) (p : ↥unitSquare) (k0 k1 : ℕ)
    (h0 : k0 ≤ N) (h1 : k1 ≤ N)
    (e0 : |(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)| ≤ 1 / (2 * (N : ℝ)))
    (e1 : |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)| ≤ 1 / (2 * (N : ℝ))) :
    dist p (Φemb N (toScaled (⟨k0, Nat.lt_succ_of_le h0⟩, ⟨k1, Nat.lt_succ_of_le h1⟩)))
      ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hne : (N : ℝ) ≠ 0 := hNr.ne'
  have h2ne : (2 * (N : ℝ)) ≠ 0 := by positivity
  have hkey : dist p
        (Φemb N (toScaled (⟨k0, Nat.lt_succ_of_le h0⟩, ⟨k1, Nat.lt_succ_of_le h1⟩)))
      = Real.sqrt (|(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)| ^ 2
          + |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)| ^ 2) := by
    rw [Subtype.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
    rfl
  rw [hkey]
  have habs0 : (0 : ℝ) ≤ |(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)| :=
    abs_nonneg _
  have habs1 : (0 : ℝ) ≤ |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)| :=
    abs_nonneg _
  calc Real.sqrt (|(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)| ^ 2
          + |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)| ^ 2)
      ≤ Real.sqrt ((|(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)|
          + |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg habs0 habs1])
    _ = |(p : EuclideanSpace ℝ (Fin 2)) 0 - (N : ℝ)⁻¹ * (k0 : ℝ)|
          + |(p : EuclideanSpace ℝ (Fin 2)) 1 - (N : ℝ)⁻¹ * (k1 : ℝ)| :=
        Real.sqrt_sq (by positivity)
    _ ≤ 1 / (2 * (N : ℝ)) + 1 / (2 * (N : ℝ)) := add_le_add e0 e1
    _ = 1 / (N : ℝ) := by
        field_simp
        norm_num

/-- **The net lemma.**  Every point of the unit square is within `1/N` of an embedded lattice
point — round each coordinate to the nearest lattice index. -/
theorem unitSquare_net {N : ℕ} (hN : 1 ≤ N) (p : ↥unitSquare) :
    ∃ x : ScaledStencil N, dist p (Φemb N x) ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h0 : (p : EuclideanSpace ℝ (Fin 2)) 0 ∈ Set.Icc (0 : ℝ) 1 := p.2 0
  have h1 : (p : EuclideanSpace ℝ (Fin 2)) 1 ∈ Set.Icc (0 : ℝ) 1 := p.2 1
  obtain ⟨hr00, hr0N⟩ := round_mul_mem (N := N) h0.1 h0.2
  obtain ⟨hr10, hr1N⟩ := round_mul_mem (N := N) h1.1 h1.2
  have hk0 : (round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin 2)) 0)).toNat ≤ N := by omega
  have hk1 : (round ((N : ℝ) * (p : EuclideanSpace ℝ (Fin 2)) 1)).toNat ≤ N := by omega
  exact ⟨toScaled (⟨_, Nat.lt_succ_of_le hk0⟩, ⟨_, Nat.lt_succ_of_le hk1⟩),
    dist_Φemb_le hN p _ _ hk0 hk1
      (coord_round_err hNr _ hr00) (coord_round_err hNr _ hr10)⟩

/-! ## Part 6 — the quantitative Gromov–Hausdorff bound -/

/-- **THE I4 BOUND.**  For `N ≥ 9`, the Gromov–Hausdorff distance between the intrinsic scaled
stencil space and the Euclidean unit square is at most `distortionError N / 2 + 1/N`: the
lattice embedding `x ↦ x/N` is a `distortionError N`-approximate isometry (brick I3) whose
image is a `1/N`-net of the square. -/
theorem ghDist_stencil_le {N : ℕ} (hN : 9 ≤ N) :
    GromovHausdorff.ghDist (ScaledStencil N) ↥unitSquare
      ≤ distortionError N / 2 + 1 / (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have key : GromovHausdorff.ghDist (ScaledStencil N) ↥unitSquare
      ≤ 0 + distortionError N / 2 + 1 / (N : ℝ) := by
    refine GromovHausdorff.ghDist_le_of_approx_subsets
        (s := (Set.univ : Set (ScaledStencil N))) (fun z => Φemb N z.1) ?_ ?_ ?_
    · exact fun x => ⟨x, Set.mem_univ x, le_of_eq (dist_self x)⟩
    · intro q
      obtain ⟨x, hx⟩ := unitSquare_net hN1 q
      exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
    · rintro ⟨x, _⟩ ⟨y, _⟩
      show |dist x y - dist (Φemb N x) (Φemb N y)| ≤ distortionError N
      rw [dist_Φemb hN1, scaledStencil_dist_eq, stencilR_eq_sqrt hN]
      exact scaled_dist_sub_eucl_le hN x.pt y.pt
  linarith

/-! ## Part 7 — the I4 capstone -/

/-- **THE I4 CAPSTONE (Gromov–Hausdorff convergence to the Euclidean unit square).**  The
intrinsic scaled stencil metric spaces — abstract finite metric spaces built from graph
geodesics, with no ambient plane — converge in Gromov–Hausdorff space to the EUCLIDEAN unit
square `([0,1]², ‖·‖₂)`.  A flat 2D Euclidean continuum limit from hop-counting, the positive
complement of `IsotropyNoGo.lean` (the isotropy enters through the stencil rule; see the
scope firewall in the header). -/
theorem stencil_toGHSpace_tendsto_unitSquare :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledStencil N)) atTop
      (𝓝 (GromovHausdorff.toGHSpace ↥unitSquare)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ N : ℕ in atTop,
      dist (GromovHausdorff.toGHSpace (ScaledStencil N))
          (GromovHausdorff.toGHSpace ↥unitSquare)
        ≤ distortionError N / 2 + 1 / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 9] with N hN
    exact ghDist_stencil_le hN
  have hub : Tendsto (fun N : ℕ => distortionError N / 2 + 1 / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => distortionError N / 2) atTop (𝓝 0) := by
      simpa using distortionError_tendsto_zero.div_const 2
    have h2 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h1.add h2
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) hbound hub

end QIQTH.StencilGH
