/-
  MixedNormalFormFull — J4-792: the FULL `∀ζ` mixed `hNormalForm` for the concrete van-Vleck witness,
  assembling the ON-gate `mTerm`-form match (J4-790) with the OFF-gate reconciliation.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the
  precise "off-gate reconciliation" step flagged as the next need at the end of J4-790: the on-gate
  match `MixedNormalFormOnGate.witnessMixed_gate_eq_mTerm` establishes the four-term `mTerm` normal form
  ONLY on the open gate (`ζ ∈ S z₀`).  The sliver rate `MixedSliverXUniform.witness_sliver2_xuniform_mixed`
  consumes its `hNormalForm` hypothesis POINTWISE at EVERY field point `ζ` (the `∫ ζ` integration variable),
  i.e. as an UNCONDITIONAL `∀ τ ∈ Ioo 0 τ₀, ∀ ζ` equality (confirmed by reading its exact type — the
  `hNormalForm` slot and its use in `MixedSliverAssembly.witness_sliver2_assembly_mixed`, `rw [hNormalForm …]`
  inside `integral_congr`).  So the on-gate match alone does NOT supply it; this file closes the `∀ζ` gap.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RECONCILIATION.  Off the gate (`ζ ∉ S z₀`) the concrete witness partial is `0` (the witness is
  hard-gated: `gatedKernel` kills the field slot outside `S z₀`).  But `mTerm0` carries a NONZERO Gaussian
  `gaussDdim τ (V ζ)`, so for the raw chart amplitude `chartFieldAmp` the four-term sum would NOT vanish
  off-gate — a mismatch.  The fix, exactly as scoped at the end of J4-790: the amplitude fields fed into the
  `mTerm` decomposition must be the **`S`-GATED** versions (vanishing off `S z₀`).  With the `Set.indicator`-
  gated amplitudes (`gateAmp`), off-gate ALL FOUR amplitudes are `0`, so every `mTerm`/`sTerm` collapses to
  `gaussDdim · … · 0 = 0`, matching the (also-`0`) witness partial.  On-gate the indicator is transparent
  (`Set.indicator_of_mem`), so the gated amplitude EQUALS `chartFieldAmp` and its field partials, and the
  four-term sum is exactly the J4-790 on-gate match.  Independently sympy-cross-checked
  (`docs/qg_roadmap/SYMBOLIC_VERIFICATION_OFFGATE_RECON.md`): off-gate `mTerm`-sum with zeroed amplitudes is
  identically `0`, and a kernel whose radial cutoff already vanishes before the gate boundary has zero second
  derivative there.

  ## THE OFF-GATE RESIDUE (the one honest carried hypothesis).  The witness partial's off-gate vanishing is
  supplied by `hOffNhd`: at every off-gate field point `ζ ∉ S z₀`, the witness is `0` on a NEIGHBORHOOD of
  `ζ`.  For `ζ` in the OPEN exterior (interior of `(S z₀)ᶜ`) this is automatic (the hard gate makes the
  witness `0` on that whole open set); at the BOUNDARY `∂(S z₀)` it holds exactly when the radial cutoff
  `radialCutoff a b (chart …)` has already killed the parametrix before the gate boundary — the geometric
  "`S z₀ ⊇ radial support`" condition that is part of the chart-surface construction.  This is the genuine
  residual, carried as a clean, satisfiable hypothesis (true e.g. when `S z₀ = Set.univ`, making the
  off-gate case vacuous, or when the witness `≡ 0`); it is NOT the conclusion.  From `hOffNhd` (a value
  germ) the file DERIVES the second-derivative vanishing via two germ-congruences
  (`pd_pd_mixed_eq_zero_of_eventuallyZero`) — genuine analytic content, not an assumption of the answer.

  Every hypothesis is a genuine per-point chart/amplitude jet (`HasDerivAt`/`PdiffAt`, the same class as
  `witnessMixed_gate_eq_mTerm`) or the off-gate germ; all are satisfiable and non-vacuous, and NONE is the
  conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedNormalFormOnGate
import QIQTH.ConvApproximants
import QIQTH.NormalFormDischarge

open Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ChartJetHessianMixed QIQTH.MixedSliverAssembly
open QIQTH.MixedNormalFormOnGate

namespace QIQTH.MixedNormalFormFull

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **`gateAmp` — the `S`-gated amplitude field.**  Restricts an amplitude `A : ℝ → Point n → ℝ` to the
    gate `S z₀`, extending by `0` off it (`Set.indicator`).  This is the amplitude the mixed normal form
    must use so that BOTH sides of `hNormalForm` vanish off the gate. -/
noncomputable def gateAmp (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) : ℝ → Point n → ℝ :=
  fun τ ζ => (S z₀).indicator (fun w => A τ w) ζ

theorem gateAmp_of_mem (S : Point n → Set (Point n)) (z₀ : Point n) (A : ℝ → Point n → ℝ)
    (τ : ℝ) {ζ : Point n} (hζ : ζ ∈ S z₀) : gateAmp S z₀ A τ ζ = A τ ζ := by
  simp only [gateAmp, Set.indicator_of_mem hζ]

theorem gateAmp_of_notMem (S : Point n → Set (Point n)) (z₀ : Point n) (A : ℝ → Point n → ℝ)
    (τ : ℝ) {ζ : Point n} (hζ : ζ ∉ S z₀) : gateAmp S z₀ A τ ζ = 0 := by
  simp only [gateAmp, Set.indicator_of_notMem hζ]

/-- **Mixed second-`pd` germ vanishing.**  If `f` is `0` on a neighborhood of `ζ`, then its mixed second
    partial `∂ⱼ∂ᵢ f` vanishes at `ζ`.  Two applications of `pd_congr_of_eventuallyEq`: on the open witness
    set `V` the inner `∂ᵢ f` is `0` pointwise (each `y ∈ V` has `f =ᶠ[𝓝 y] 0`), hence `∂ᵢ f =ᶠ[𝓝 ζ] 0`,
    hence `∂ⱼ(∂ᵢ f) ζ = 0`.  The mixed-index / general-base-point analogue of
    `NormalFormDischarge.pd_pd_congr_of_eventuallyEq`. -/
theorem pd_pd_mixed_eq_zero_of_eventuallyZero (f : Point n → ℝ) (i j : Fin n) (ζ : Point n)
    (h : ∀ᶠ w in 𝓝 ζ, f w = 0) :
    pd (fun y => pd f i y) j ζ = 0 := by
  obtain ⟨V, hVeq, hVopen, hV0⟩ := eventually_nhds_iff.mp h
  have hev : (fun y => pd f i y) =ᶠ[𝓝 ζ] (fun _ => (0 : ℝ)) := by
    refine eventually_nhds_iff.mpr ⟨V, ?_, hVopen, hV0⟩
    intro y hyV
    have hpdy : pd f i y = pd (fun _ => (0 : ℝ)) i y :=
      pd_congr_of_eventuallyEq f (fun _ => (0 : ℝ)) i y
        (eventually_nhds_iff.mpr ⟨V, hVeq, hVopen, hyV⟩)
    show pd f i y = (0 : ℝ)
    rw [hpdy, pd_const]
  rw [pd_congr_of_eventuallyEq (fun y => pd f i y) (fun _ => (0 : ℝ)) j ζ hev, pd_const]

/-- **★★ J4-792 — `witnessMixed_hNormalForm_full` — THE FULL `∀ζ` MIXED `hNormalForm`.**  For the concrete
    gated van-Vleck witness at a fixed base `z₀ ∈ K`, the mixed `∂ⱼ∂ᵢ` second field partial equals the
    FOUR-term mixed normal form at EVERY field point `ζ` and EVERY `τ ∈ Ioo 0 τ₀` — the EXACT unconditional
    `hNormalForm` shape that `MixedSliverXUniform.witness_sliver2_xuniform_mixed` consumes, with the concrete
    chart `V := uniformInverseChart … z₀`, carried jets `Pi/Pj/Q`, and the **`S`-GATED** amplitude fields
    (`gateAmp S z₀` of `chartFieldAmp` and its `i`/`j`/mixed field partials).
    ON gate (`ζ ∈ S z₀`): the gated amplitudes are transparent, and the equality IS the J4-790 on-gate match
    `witnessMixed_gate_eq_mTerm`.  OFF gate (`ζ ∉ S z₀`): the witness partial vanishes
    (`pd_pd_mixed_eq_zero_of_eventuallyZero` from the off-gate germ `hOffNhd`) and every gated amplitude
    vanishes (`gateAmp_of_notMem`), so both sides are `0`.  Carries the geometric off-gate germ `hOffNhd`
    (the chart-surface residue) and the per-point chart/amplitude jets — all satisfiable, none the
    conclusion.  NOT `a₁ = R/6`. -/
theorem witnessMixed_hNormalForm_full (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ₀ : ℝ) (z₀ : Point n) (hz₀ : z₀ ∈ K) (hSopen : IsOpen (S z₀))
    (Pi Pj Q : Point n → Point n)
    (hJetPi : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y i s) k) (Pi y k) (y i))
    (hJetPj : ∀ y k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z₀ (Function.update y j s) k) (Pj y k) (y j))
    (hJetQ : ∀ ζ : Point n, ∀ k, HasDerivAt
      (fun s : ℝ => Pi (Function.update ζ j s) k) (Q ζ k) (ζ j))
    (hAmpDi : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ y : Point n,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) i y)
    (hAmpDj : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (chartFieldAmp g gi hC hK a b τ z₀) j ζ)
    (hAmpD2 : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ ∈ S z₀,
      PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z₀) i y) j ζ)
    (hOffNhd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n, ζ ∉ S z₀ →
      ∀ᶠ w in 𝓝 ζ, vanVleckGatedWitness g gi hC hK S a b τ w z₀ = 0) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ ζ : Point n,
      pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i y) j ζ
        = mTerm0 (uniformInverseChart g gi hC hK z₀) Pi Pj Q
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) => chartFieldAmp g gi hC hK a b τ' z₀ ζ')) τ ζ
          + mTerm1 (uniformInverseChart g gi hC hK z₀) Pj
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) i ζ')) τ ζ
          + mTerm1 (uniformInverseChart g gi hC hK z₀) Pi
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (chartFieldAmp g gi hC hK a b τ' z₀) j ζ')) τ ζ
          + sTerm2 (uniformInverseChart g gi hC hK z₀)
              (gateAmp S z₀ (fun (τ' : ℝ) (ζ' : Point n) =>
                pd (fun y => pd (chartFieldAmp g gi hC hK a b τ' z₀) i y) j ζ')) τ ζ := by
  intro τ hτIoo ζ
  have hτ : 0 < τ := hτIoo.1
  by_cases hζS : ζ ∈ S z₀
  · -- ON the gate: the gated amplitudes are transparent; use the J4-790 on-gate match.
    rw [witnessMixed_gate_eq_mTerm g gi hC hK S a b i j τ hτ z₀ hz₀ hSopen ζ hζS Pi Pj Q
        hJetPi hJetPj (hJetQ ζ) (hAmpDi τ hτIoo) (hAmpDj τ hτIoo ζ hζS) (hAmpD2 τ hτIoo ζ hζS)]
    simp only [mTerm0, mTerm1, sTerm2, gateAmp, Set.indicator_of_mem hζS]
  · -- OFF the gate: witness partial is 0 (from `hOffNhd`); every gated amplitude is 0.
    rw [pd_pd_mixed_eq_zero_of_eventuallyZero
        (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z₀) i j ζ (hOffNhd τ hτIoo ζ hζS)]
    simp only [mTerm0, mTerm1, sTerm2, gateAmp, Set.indicator_of_notMem hζS,
      mul_zero, add_zero]

end QIQTH.MixedNormalFormFull

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedNormalFormFull
#print axioms witnessMixed_hNormalForm_full
#print axioms pd_pd_mixed_eq_zero_of_eventuallyZero
end AxiomChecks
