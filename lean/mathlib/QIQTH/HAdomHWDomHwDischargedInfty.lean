/-
  HAdomHWDomHwDischargedInfty — DISCHARGING the residual `hw` amplitude-smoothness carry of the
  ABSTRACT-`g` `hAdom` + `hWDom` bundle, by REBASING the D1 domination chain off the `⊤` (= `ω`,
  real-ANALYTIC) level onto the `∞` (= C^∞) level that `HuInftyRebase.hu_infty_closed` actually
  supplies.  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure regularity-plumbing / RE-EXPOSURE brick.  It removes the last free smoothness hypothesis
  (`hw`) from the `hAdom`/`hWDom` census bundle, deriving it internally from the raw geometry
  `{hg, hgi, hgpos, hChr}`.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE `⊤` vs `∞` LEDGER (character-checked against Mathlib).  In the current toolchain
     `ContDiff`'s smoothness order is `WithTop ℕ∞` with the scoped notations
        `ω = (⊤ : WithTop ℕ∞)`         (Mathlib `ContDiff/FTaylorSeries.lean:117`) — real-ANALYTIC,
        `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`  (`FTaylorSeries.lean:119`)                  — C^∞.
     These are GENUINELY DISTINCT: `∞ = some (⊤ : ℕ∞) < none = ⊤ = ω`, so `∞ ≠ ω` (a strict `<` in
     `WithTop`, NOT a defeq or a `WithTop.coe_top`-bridgeable annotation clash).  `ContDiff ℝ ω`
     genuinely means real-analytic (a convergent local power series, `ContDiff/Defs.lean:133`), a
     STRICTLY STRONGER condition than smooth.

  ── WHY `hw` AT `⊤` WAS UNREACHABLE, AND WHY IT DOES NOT MATTER.  The banked domination chain
     (`ConcreteDominations`) states its amplitude carry `hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff …)` at
     the analytic level.  Supplying that directly would require the van-Vleck folded coefficients —
     hence the transport coefficients `radialTransportSolve` — to be real-ANALYTIC in the base
     point, i.e. parametric analyticity of the ray integral `∫₀¹ sᵐ g(s•v) ds`, a theorem Mathlib
     LACKS (it has only the complex Cauchy-integral machinery, not a general analytic-family
     integral lemma).  That is the wall `HuInftyRebase` recorded (J4-174).  BUT the chain NEVER
     GENUINELY uses `ω`: its sole genuine consumption of `hw` is
        `exists_cutoff_foldedCoeff_bound` :  `(radialCutoff_contDiff a b).continuous.mul hwk.continuous`
     (`ConcreteDominations.lean:345`) — a pure `C⁰` downcast (`.continuous`).  Everything downstream
     (`gatedWitnessN1_D1_of_gateSqControl`, the gate lift, the `∃ A₀ A₁` packaging, the `hWDom`
     window slice) consumes only the EXTRACTED constant bounds, never the smoothness.  So the `⊤`
     typing is a purely cosmetic statement-level artifact.

  ── THE DISCHARGE.  This file re-derives the D1 chain from a bare CONTINUITY carry
     (`…_ofCont`, the genuine content), then feeds it the `∞`-level folded-coefficient smoothness
     that `HuInftyRebase.hw_discharged_infty ∘ hu_infty_closed` proves from `{hg, hgi, hgpos}`,
     downcast `.continuous`.  The result `hAdom_hWDom_from_gateSqControl_hwDischarged` produces the
     EXACT `hAdom`/`hWDom` bundle of `HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl`
     with the `hw` hypothesis ELIMINATED — the only surviving carry is the satisfiable
     `GateSqControl` gate certificate.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConcreteDominations
import QIQTH.HAdomHWDomFromConcreteDominations
import QIQTH.HuInftyRebase

open Set Filter Metric
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.WidthAdapters QIQTH.RNCDecay
open QIQTH.HeatResidualBound
open scoped BigOperators Topology ContDiff

namespace QIQTH.HwDischargedInfty

variable {n : ℕ}

/-! ###############################################################################
    ### PART 1 — the D1 amplitude sup from a bare CONTINUITY carry (the genuine content).
    ############################################################################### -/

/-- **`exists_cutoff_foldedCoeff_bound_ofCont` — the compact-support amplitude sup from CONTINUITY.**
    Identical content to `ConcreteDominations.exists_cutoff_foldedCoeff_bound`, but taking only the
    genuine hypothesis it actually uses: `Continuous (foldedCoeff Θ u k)` (that lemma's `⊤`-smoothness
    is immediately downcast `.continuous`).  The cutoff-folded coefficient is continuous and supported
    in `closedBall 0 b`, hence globally bounded by its EVT sup on the compact ball.  NOT `a₁ = R/6`. -/
theorem exists_cutoff_foldedCoeff_bound_ofCont (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (k : ℕ) (ha : 0 < a) (hab : a < b) (hcont : Continuous (foldedCoeff Θ u k)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v : Point n, |radialCutoff a b v * foldedCoeff Θ u k v| ≤ A := by
  have hb0 : 0 < b := lt_trans ha hab
  have hcont' : Continuous (fun v : Point n => radialCutoff a b v * foldedCoeff Θ u k v) :=
    (radialCutoff_contDiff a b).continuous.mul hcont
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Point n) b).exists_bound_of_continuousOn
    hcont'.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v => ?_⟩
  by_cases hv : v ∈ Metric.closedBall (0 : Point n) b
  · have h := hC v hv
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [mem_closedBall_zero_iff, not_le] at hv
    have hb2 : b ^ 2 ≤ rncRadialSq v := by
      have hnr : ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
      have hlt : b < rncRadial v := lt_of_lt_of_le hv hnr
      rw [← rncRadial_sq v]
      nlinarith [hlt, hb0.le]
    rw [radialCutoff_eq_zero ha hab hb2, zero_mul, abs_zero]
    exact le_max_right _ _

/-- **`exists_D1_constants_of_gateSqControl_ofCont` — the `∃ A₀ A₁` D1 packaging from CONTINUITY.**
    The `ofCont` mirror of `ConcreteDominations.exists_D1_constants_of_gateSqControl`: combines the two
    amplitude sups (`ofCont` at `k = 0, 1`) with the banked gated lift
    `gatedWitnessN1_D1_of_gateSqControl` (which consumes only the extracted bounds, no smoothness) into
    the affine-domination existential.  NOT `a₁ = R/6`. -/
theorem exists_D1_constants_of_gateSqControl_ofCont (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (W : Point n → Point n → Point n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (ha : 0 < a) (hab : a < b)
    (hcont : ∀ k, Continuous (foldedCoeff Θ u k))
    (hgate : GateSqControl K S W) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W) τ p q|
        ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  obtain ⟨A₀, hA₀, hb0⟩ := exists_cutoff_foldedCoeff_bound_ofCont Θ u a b 0 ha hab (hcont 0)
  obtain ⟨A₁, hA₁, hb1⟩ := exists_cutoff_foldedCoeff_bound_ofCont Θ u a b 1 ha hab (hcont 1)
  exact ⟨A₀, A₁, hA₀, hA₁,
    gatedWitnessN1_D1_of_gateSqControl Θ u a b W K S A₀ A₁ hA₀ hA₁ hb0 hb1 hgate⟩

/-! ###############################################################################
    ### PART 2 — `hw` DISCHARGED: the `hAdom` + `hWDom` bundle from raw geometry alone.
    ############################################################################### -/

/-- **★★★ `hAdom_hWDom_from_gateSqControl_hwDischarged` — the `hw`-FREE `hAdom` + `hWDom` bundle.**
    The EXACT conclusion of `HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl`, but with
    the residual amplitude-smoothness carry `hw` ELIMINATED: it is derived internally at the `∞`
    (C^∞) level via `HuInftyRebase.hw_discharged_infty ∘ hu_infty_closed` (from `{hg, hgi, hgpos}`),
    downcast `.continuous`, and threaded through the `ofCont` D1 chain of Part 1.  The van-Vleck
    census kernel matches the generic D1 kernel by the `def` defeq (`vanVleckGatedWitness_eq_gatedKernel`,
    `rfl`).  The sole surviving carry is the satisfiable `GateSqControl` gate certificate; the analytic
    (`ω`) level is nowhere required.  ⚠ NOT `a₁ = R/6`. -/
theorem hAdom_hWDom_from_gateSqControl_hwDischarged
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hgate : GateSqControl K S (uniformInverseChart g gi hChr hK)) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∃ CW lam : ℝ, 0 ≤ CW ∧ 0 < lam ∧
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z|
          ≤ CW * gaussDdim (lam * τ) z) := by
  -- `hw` DISCHARGED at `∞`, downcast to the CONTINUITY the D1 chain genuinely needs.
  have hcont : ∀ k, Continuous
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) :=
    fun k => (QIQTH.HuInftyRebase.hw_discharged_infty g gi hg hgpos
      (QIQTH.HuInftyRebase.hu_infty_closed g gi hg hgi hgpos) k).continuous
  -- `hAdom`: the base-point-varying binder — the D1 conclusion at the live witness (`def` defeq).
  obtain ⟨A₀, A₁, hA₀, hA₁, hdom0⟩ :=
    exists_D1_constants_of_gateSqControl_ofCont (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi))
      a b (uniformInverseChart g gi hChr hK) K S ha hab hcont hgate
  have hdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |vanVleckGatedWitness g gi hChr hK S a b τ p q|
        ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
    fun τ hτ p q => hdom0 τ p q hτ
  -- window constants for `hWDom` (mirroring the abstract-`g` instance's choice).
  refine ⟨A₀, A₁, hA₀, hA₁,
    (A₀ + A₁ * τ₀) * Real.sqrt (3 / 2) ^ n, 3 / 2,
    mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ₀.le)) (pow_nonneg (Real.sqrt_nonneg _) n),
    by norm_num, hdom, ?_⟩
  -- `hWDom`: the frozen `p = 0` window slice of `hAdom`.
  intro τ hτ hτle z
  have hz := hdom τ hτ (0 : Point n) z
  rw [zero_sub, gaussDdim_neg] at hz
  have hstep : (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n
      ≤ (A₀ + A₁ * τ₀) * Real.sqrt (3 / 2) ^ n := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) n)
    have := mul_le_mul_of_nonneg_left hτle hA₁
    linarith
  calc |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z|
        ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z := hz
    _ ≤ (A₀ + A₁ * τ₀) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z :=
        mul_le_mul_of_nonneg_right hstep (gaussDdim_nonneg _ _)

end QIQTH.HwDischargedInfty

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HwDischargedInfty
#print axioms exists_cutoff_foldedCoeff_bound_ofCont
#print axioms exists_D1_constants_of_gateSqControl_ofCont
#print axioms hAdom_hWDom_from_gateSqControl_hwDischarged
end AxiomChecks
