/-
  B7 (THE_TRANSPORT_AND_ACCOUNTING_PLAN.md) — STRONG CONTINUITY of the transported flow:
  `t ↦ U_t ξ` is continuous for EVERY ξ in the tower Hilbert space.

  Route (norm-free on matrices — the binding mitigations): on a pure component the squared
  seminorm distance ‖U_t x − U_s x‖² collapses (stage stability + the flow group laws) to the
  closed form `re(⟪a,a⟫ + ⟪a,a⟫ − ⟪a, σ_{−t+s}a⟫ − ⟪a, σ_{−s+t}a⟫)` (`norm_flowRaw_sub_of_sq`),
  a CONTINUOUS function of the times: the held `sigmaDiag_entry` at the strictly positive Gibbs
  weights makes every matrix entry of `σ_s a` a fixed `Complex.exp` phase times a constant
  (`cornerFlow_entry` — the ONLY entry-level access in this file; no `cpow`), so
  `s ↦ ⟪a, σ_s a⟫_C` is a finite trace of continuous entries (`continuous_gnsInner_cornerFlow`).
  Pure components give `tendsto_flowPre_of`, finite raw support + linearity give every
  pre-vector (`tendsto_flowPre_apply`), and the ε/3 density argument with the UNIFORM isometry
  `towerFlow_norm_eq` extends to the completion.

  B7 CAPSTONE `continuous_towerFlow_apply`: `t ↦ U_t ξ` is continuous — with B3, the
  transported flow is a STRONGLY CONTINUOUS one-parameter unitary group on `TowerGNS`.

  HONEST SCOPE (binding): strong continuity of the TRANSPORTED flow — no Tomita operator, no
  Δ, no J, no generator, and no Stone theorem is used or claimed anywhere in this file.

  LEAN ARCHITECTURE (the R3 lesson, binding): entry access only through the held
  `sigmaDiag_entry` + `gibbsWeight_pos`; the synonym is crossed only in application position;
  ε/δ endgames use typed `have`s (definitional-equality tolerant), never `rw` on β-redexes.
-/
import Mathlib
import QIQTH.TowerGNS.FlowCovariance
import QIQTH.TowerGNS.Germ

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The entry formula and continuity of the one-sided flow pairing -/

/-- The entry formula for the per-corner Gibbs modular flow (the held `sigmaDiag_entry` at
    the strictly positive Gibbs weights — the ONLY entry-level access in this file). -/
theorem cornerFlow_entry (C : Finset M) (t : ℝ) (a : DiamondAlg L C) (n m : Micro L C) :
    cornerFlow L ω β C t a n m
      = Complex.exp (Complex.I * t
          * ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
        * a n m :=
  sigmaDiag_entry L C (fun p => gibbsWeight L C ω β p)
    (fun p => gibbsWeight_pos L C ω β p) t a n m

/-- The flow orbit of a corner element is continuous in time, entrywise: every entry is a
    fixed `Complex.exp` phase (continuous in `t`) times a constant. -/
theorem continuous_cornerFlow_apply (C : Finset M) (a : DiamondAlg L C) :
    Continuous fun t : ℝ => cornerFlow L ω β C t a := by
  apply continuous_matrix
  intro n m
  show Continuous fun t : ℝ => cornerFlow L ω β C t a n m
  have h : (fun t : ℝ => cornerFlow L ω β C t a n m)
      = fun t : ℝ => Complex.exp (Complex.I * t
          * ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
        * a n m :=
    funext fun t => cornerFlow_entry L ω β C t a n m
  rw [h]
  exact (Complex.continuous_exp.comp
    ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).mul
    continuous_const

/-- **Continuity of the one-sided flow pairing** `s ↦ ⟪a, σ_s a⟫_C`: a finite trace of
    entrywise-continuous matrices — no operator norm, no `cpow`. -/
theorem continuous_gnsInner_cornerFlow (C : Finset M) (a : DiamondAlg L C) :
    Continuous fun s : ℝ => gnsInner L ω β C a (cornerFlow L ω β C s a) := by
  have h : (fun s : ℝ => gnsInner L ω β C a (cornerFlow L ω β C s a))
      = fun s : ℝ =>
        Matrix.trace (gibbsDensity L C ω β * (aᴴ * cornerFlow L ω β C s a)) :=
    funext fun s => gnsInner_def L ω β C a (cornerFlow L ω β C s a)
  rw [h]
  exact Continuous.matrix_trace
    (continuous_const.matrix_mul
      (continuous_const.matrix_mul (continuous_cornerFlow_apply L ω β C a)))

/-- The two-sided flow pairing collapses to the one-sided one:
    `⟪σ_t x, σ_s y⟫_C = ⟪x, σ_{−t+s} y⟫_C` (B1 pre-unitarity + the group law). -/
theorem gnsInner_cornerFlow_cornerFlow (C : Finset M) (t s : ℝ) (x y : DiamondAlg L C) :
    gnsInner L ω β C (cornerFlow L ω β C t x) (cornerFlow L ω β C s y)
      = gnsInner L ω β C x (cornerFlow L ω β C (-t + s) y) := by
  calc gnsInner L ω β C (cornerFlow L ω β C t x) (cornerFlow L ω β C s y)
      = gnsInner L ω β C (cornerFlow L ω β C (-t) (cornerFlow L ω β C t x))
          (cornerFlow L ω β C (-t) (cornerFlow L ω β C s y)) :=
        (gnsInner_cornerFlow L ω β C (-t) _ _).symm
    _ = gnsInner L ω β C x (cornerFlow L ω β C (-t + s) y) := by
        rw [cornerFlow_comp, cornerFlow_comp, neg_add_cancel, cornerFlow_zero]

/-! ### B7 item 1 — the squared seminorm distance of a flowed pure component -/

/-- The tower inner product of the flowed difference, fully collapsed to stage `C` (the germ
    pattern: `pairInner_embed` at `K := C` + `cornerEmbed_refl`, then the flow collapse). -/
theorem towerOf_cornerFlow_sub_inner (C : Finset M) (a : DiamondAlg L C) (t s : ℝ) :
    ⟪(towerOf L ω β C (cornerFlow L ω β C t a)
        - towerOf L ω β C (cornerFlow L ω β C s a) : TowerPre L ω β),
      (towerOf L ω β C (cornerFlow L ω β C t a)
        - towerOf L ω β C (cornerFlow L ω β C s a) : TowerPre L ω β)⟫_ℂ
      = gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + s) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-s + t) a) := by
  set u : TowerPre L ω β := towerOf L ω β C (cornerFlow L ω β C t a) with hu
  set v : TowerPre L ω β := towerOf L ω β C (cornerFlow L ω β C s a) with hv
  have huu : ⟪u, u⟫_ℂ = gnsInner L ω β C a a := by
    rw [hu, towerInner_of_of, pairInner_embed L ω β C C C subset_rfl subset_rfl,
      cornerEmbed_refl, gnsInner_cornerFlow]
  have huv : ⟪u, v⟫_ℂ = gnsInner L ω β C a (cornerFlow L ω β C (-t + s) a) := by
    rw [hu, hv, towerInner_of_of, pairInner_embed L ω β C C C subset_rfl subset_rfl,
      cornerEmbed_refl, cornerEmbed_refl, gnsInner_cornerFlow_cornerFlow]
  have hvu : ⟪v, u⟫_ℂ = gnsInner L ω β C a (cornerFlow L ω β C (-s + t) a) := by
    rw [hu, hv, towerInner_of_of, pairInner_embed L ω β C C C subset_rfl subset_rfl,
      cornerEmbed_refl, cornerEmbed_refl, gnsInner_cornerFlow_cornerFlow]
  have hvv : ⟪v, v⟫_ℂ = gnsInner L ω β C a a := by
    rw [hv, towerInner_of_of, pairInner_embed L ω β C C C subset_rfl subset_rfl,
      cornerEmbed_refl, gnsInner_cornerFlow]
  rw [inner_sub_sub_self, huu, huv, hvu, hvv]
  ring

/-- **B7 item 1 — the squared seminorm distance of the flowed pure component**: an explicit
    finite closed form (Gibbs pairings at collapsed times), continuous in both times. -/
theorem norm_flowRaw_sub_of_sq (C : Finset M) (a : DiamondAlg L C) (t s : ℝ) :
    ‖(towerOf L ω β C (cornerFlow L ω β C t a)
        - towerOf L ω β C (cornerFlow L ω β C s a) : TowerPre L ω β)‖ ^ 2
      = RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
          - gnsInner L ω β C a (cornerFlow L ω β C (-t + s) a)
          - gnsInner L ω β C a (cornerFlow L ω β C (-s + t) a)) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), towerOf_cornerFlow_sub_inner]

/-! ### B7 item 2 — strong continuity on pure components and pre-vectors -/

/-- **Strong continuity on a pure component**: `t ↦ flowPre_t (of C a)` is continuous into
    the seminormed pre-space — the squared distance is item 1's continuous closed form,
    vanishing at `t = t₀`. -/
theorem tendsto_flowPre_of (C : Finset M) (a : DiamondAlg L C) (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => flowPre L ω β t (towerOf L ω β C a)) (nhds t₀)
      (nhds (flowPre L ω β t₀ (towerOf L ω β C a))) := by
  have hval : ∀ t : ℝ, flowPre L ω β t (towerOf L ω β C a)
      = towerOf L ω β C (cornerFlow L ω β C t a) := fun t => flowRaw_of L ω β t C a
  simp only [hval]
  -- the continuous scalar majorant
  have hbody : Continuous fun t : ℝ => gnsInner L ω β C a a + gnsInner L ω β C a a
      - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
      - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a) := by
    have hg1 : Continuous fun t : ℝ =>
        gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a) :=
      (continuous_gnsInner_cornerFlow L ω β C a).comp (continuous_neg.add continuous_const)
    have hg2 : Continuous fun t : ℝ =>
        gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a) :=
      (continuous_gnsInner_cornerFlow L ω β C a).comp (continuous_const.add continuous_id)
    exact (continuous_const.sub hg1).sub hg2
  have hN : Continuous fun t : ℝ =>
      RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a)) :=
    RCLike.continuous_re.comp hbody
  have h1 : Filter.Tendsto (fun t : ℝ =>
      RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a))) (nhds t₀) (nhds 0) := by
    have h0 := hN.tendsto t₀
    have hval0 : RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t₀) a)) = 0 := by
      rw [neg_add_cancel, cornerFlow_zero]
      have hz : gnsInner L ω β C a a + gnsInner L ω β C a a - gnsInner L ω β C a a
          - gnsInner L ω β C a a = 0 := by ring
      rw [hz]
      exact map_zero _
    simpa only [hval0] using h0
  have h2 : Filter.Tendsto (fun t : ℝ =>
      Real.sqrt (RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a)))) (nhds t₀) (nhds 0) := by
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h3
    exact h3
  -- ε/δ transfer (typed `have`s only — never `rw` on β-redexes)
  rw [Metric.tendsto_nhds_nhds] at h2 ⊢
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := h2 ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hq : Real.sqrt (RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
      - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
      - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a))) < ε := by
    have h : dist (Real.sqrt (RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a)))) (0 : ℝ) < ε := hball ht
    rwa [Real.dist_0_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hkey : dist (towerOf L ω β C (cornerFlow L ω β C t a))
      (towerOf L ω β C (cornerFlow L ω β C t₀ a))
      = Real.sqrt (RCLike.re (gnsInner L ω β C a a + gnsInner L ω β C a a
        - gnsInner L ω β C a (cornerFlow L ω β C (-t + t₀) a)
        - gnsInner L ω β C a (cornerFlow L ω β C (-t₀ + t) a))) := by
    rw [dist_eq_norm, ← norm_flowRaw_sub_of_sq L ω β C a t t₀,
      Real.sqrt_sq (norm_nonneg _)]
  exact lt_of_eq_of_lt hkey hq

/-- **Strong continuity on every pre-vector**: finite raw support + linearity of `flowPre`
    reduce to the pure components. -/
theorem tendsto_flowPre_apply (x : TowerPre L ω β) (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => flowPre L ω β t x) (nhds t₀)
      (nhds (flowPre L ω β t₀ x)) := by
  classical
  -- peel to the raw `⨁` view (the synonym has no `DFunLike` — the R3 lesson)
  obtain ⟨y, rfl⟩ : ∃ y : ⨁ C : Finset M, DiamondAlg L C,
      (y : TowerPre L ω β) = x := ⟨x, rfl⟩
  have hrw : ∀ t : ℝ, flowPre L ω β t (y : TowerPre L ω β)
      = ∑ C ∈ DFinsupp.support y, flowPre L ω β t (towerOf L ω β C (y C)) := by
    intro t
    conv_lhs => rw [show (y : TowerPre L ω β)
        = ∑ C ∈ DFinsupp.support y, towerOf L ω β C (y C) from
      (DirectSum.sum_support_of y).symm]
    exact map_sum (flowPre L ω β t) (fun C => towerOf L ω β C (y C)) (DFinsupp.support y)
  simp only [hrw]
  exact tendsto_finsetSum _ fun C _ => tendsto_flowPre_of L ω β C (y C) t₀

/-! ### B7 CAPSTONE — strong continuity on the completion (ε/3 + the uniform isometry) -/

/-- The transported flow is a UNIFORM isometry of the distance (B6's norm preservation in
    distance form — the ε/3 workhorse). -/
theorem towerFlow_dist_eq (t : ℝ) (ξ η : TowerGNS L ω β) :
    dist (towerFlow L ω β t ξ) (towerFlow L ω β t η) = dist ξ η := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub (towerFlow L ω β t), towerFlow_norm_eq]

/-- **B7 CAPSTONE — STRONG CONTINUITY OF THE TRANSPORTED FLOW**: `t ↦ U_t ξ` is continuous
    for EVERY `ξ` in the tower Hilbert space — with B3 (one-parameter unitary group), the
    transported flow is a STRONGLY CONTINUOUS one-parameter unitary group on `TowerGNS`.
    The ε/3 assembly: a coerced pre-vector `↑x` within `ε/3` of `ξ` (density of the
    pre-space), the continuous motion of `↑x` (item 2 + continuity of the coercion), and the
    UNIFORM isometry `dist (U_t ξ) (U_t η) = dist ξ η` controlling both replacement errors. -/
theorem continuous_towerFlow_apply (ξ : TowerGNS L ω β) :
    Continuous fun t : ℝ => towerFlow L ω β t ξ := by
  rw [Metric.continuous_iff]
  intro t₀ ε hε
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := TowerPre L ω β)) ξ (ε / 3) (by linarith)
  have hcoe : Filter.Tendsto
      (fun t : ℝ => towerFlow L ω β t ((x : TowerPre L ω β) : TowerGNS L ω β)) (nhds t₀)
      (nhds (towerFlow L ω β t₀ ((x : TowerPre L ω β) : TowerGNS L ω β))) := by
    have h1 : Filter.Tendsto
        (fun t : ℝ => ((flowPre L ω β t x : TowerPre L ω β) : TowerGNS L ω β)) (nhds t₀)
        (nhds ((flowPre L ω β t₀ x : TowerPre L ω β) : TowerGNS L ω β)) :=
      ((UniformSpace.Completion.continuous_coe (α := TowerPre L ω β)).tendsto _).comp
        (tendsto_flowPre_apply L ω β x t₀)
    simpa only [towerFlow_coe] using h1
  rw [Metric.tendsto_nhds_nhds] at hcoe
  obtain ⟨δ, hδ, hball⟩ := hcoe (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h1 : dist (towerFlow L ω β t ξ)
      (towerFlow L ω β t ((x : TowerPre L ω β) : TowerGNS L ω β)) < ε / 3 := by
    rw [towerFlow_dist_eq]
    exact hx
  have h2 : dist (towerFlow L ω β t ((x : TowerPre L ω β) : TowerGNS L ω β))
      (towerFlow L ω β t₀ ((x : TowerPre L ω β) : TowerGNS L ω β)) < ε / 3 := hball ht
  have h3 : dist (towerFlow L ω β t₀ ((x : TowerPre L ω β) : TowerGNS L ω β))
      (towerFlow L ω β t₀ ξ) < ε / 3 := by
    rw [towerFlow_dist_eq, dist_comm]
    exact hx
  calc dist (towerFlow L ω β t ξ) (towerFlow L ω β t₀ ξ)
      ≤ dist (towerFlow L ω β t ξ)
          (towerFlow L ω β t ((x : TowerPre L ω β) : TowerGNS L ω β))
        + dist (towerFlow L ω β t ((x : TowerPre L ω β) : TowerGNS L ω β))
            (towerFlow L ω β t₀ ((x : TowerPre L ω β) : TowerGNS L ω β))
        + dist (towerFlow L ω β t₀ ((x : TowerPre L ω β) : TowerGNS L ω β))
            (towerFlow L ω β t₀ ξ) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring

end QIQTH.TowerGNS
