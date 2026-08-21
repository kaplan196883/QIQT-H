/-
  CensusTauDerivAnySEnvelope — J4-950: the CRUDE TIME-DERIVATIVE Gaussian envelope with the S=univ
  requirement ELIMINATED — the census-slice `∂_τ` envelope holds for ANY gate `S`, with NO
  S-membership hypothesis at all.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  real-analysis / structural threading brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing banked file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J4-949 CONCERN AND ITS RESOLUTION.  J4-949 flagged that the census far-rate assembly
  (`CensusAmplitudeSupDischarge`) still carries an over-strong gate half `hgateS`
    `∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2`
  because it routes the `∂_τ` closed form through `WitnessTimeDerivEnvelope.witnessTimeDeriv_domination`,
  whose `hgate` hypothesis universally quantifies the FIELD point `w.2.1`.  Since `w.2.1` ranges over ALL
  of `Point n` with no guard, that forces `S q = univ` for every `q ∈ K` — the SAME quantifier-order
  over-statement audited (and fixed for the MEASURABILITY surface) at J4-231/232
  (`HgateSatAudit`/`GatedRepSFix`).

  ## THIS IS **NOT** A cp466-STYLE VACUITY TRAP.  The census only ever evaluates the `∂_τ` kernel at the
  FIXED field point `0` (`deriv (fun r ↦ vanVleckGatedWitness … r 0 z)`).  The genuine mathematical need is
  the CENSUS GATE `0 ∈ S z`, which is fully satisfiable by a PROPER (non-`univ`) gate.  The banked
  `CensusTauDerivGateSplit.censusTauDeriv_gateSplit` already proves the field-point-`0` everywhere identity
  with **NO** `hgate` carry and for **ANY** `S`: OFF the joint gate (`z ∉ K` ∨ `0 ∉ S z`) the gated kernel
  is identically `0`, so `deriv = 0` = the gated representative; the S-membership is discharged by that
  off-gate split, NEVER forced to `univ`.  Unlike cp466 — where `hframeK` (flat metric on all of `K`) was
  MATHEMATICALLY incompatible with curvature `κ ≠ 0`, collapsing the construction — here `0 ∈ S z` places
  NO constraint on the geometry; a proper flow-ball gate satisfies it.

  ## WHAT LANDS (the concrete elimination of S=univ for the DOMINATION consumer).
    • `witnessTimeDeriv_domination_anyS` — the on-ball crude `∂_τ` envelope
        `|deriv (fun r ↦ Wit r 0 z) τ| ≤ C·τ⁻¹·gaussDdim (4·D.lam·τ) z`   (`z ∈ K`, `‖z‖ < D.r`)
      with **NO S-gate hypothesis** (ANY `S`).  Route: apply the banked `witnessTimeDeriv_domination` at
      `S := univ` (its over-strong `hgate` is TRIVIALLY dischargeable for `univ` — `Set.mem_univ` +
      the banked unconditional `chartFieldAmp_hasDerivAt_tau`), then transfer to arbitrary `S` by
      `censusTauDeriv_gateSplit`: on the gate `0 ∈ S z` both derivatives equal the SAME S-independent
      closed form; off it (`0 ∉ S z`) the derivative is `0` and the bound is trivial.
    • `witnessTimeDeriv_domination_global_anyS` — the `∀ z` extension, carrying ONLY the honest support
      fact `hSupp` (`z ∈ K`, `0 ∈ S z ⟹ ‖z‖ < D.r`; the same input as the banked `_global`), again with
      **NO S-membership `hgate`**.
    • `census_anyS_env_satisfiable_properGate` — non-vacuity at a PROPER gate `S := ball 0 1 ≠ univ`
      (`0 ∈ S z` yet `S z ≠ univ`, `n > 0`): the full hypothesis bundle is jointly satisfiable with a
      non-`univ` gate, DIRECTLY refuting the cp466 analogy.

  ## HONEST STATUS.  The over-strong `hgateS`/`S=univ` carry is ELIMINATED for the crude `∂_τ` domination
  envelope: `witnessTimeDeriv_domination_global_anyS` is a strictly-more-general drop-in for the banked
  `witnessTimeDeriv_domination_global` with the `hgate` hypothesis REMOVED (any `S`).  Re-threading the
  live census consumers (`CensusOnGateEnvelopeThreaded`, `WitnessBoundDHpardiffWired`,
  `CensusAmplitudeSupDischarge`) onto this any-`S` envelope is a mechanical supplier substitution (they
  take the envelope as an opaque hypothesis), deferred to keep this brick isolated.  `hDuhamel`/`hDConv`
  remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessTimeDerivEnvelope
import QIQTH.CensusTauDerivGateSplit

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.GaussianWidthTransfer QIQTH.InverseChartNormalJets
open QIQTH.GatedTauDerivRep QIQTH.OnGateJets
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.VanVleck
open QIQTH.WitnessTimeDerivEnvelope QIQTH.CensusTauDerivGateSplit
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusTauDerivAnySEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the on-ball crude `∂_τ` envelope with the S=univ requirement ELIMINATED.
    ############################################################################### -/

/-- **★★★ `witnessTimeDeriv_domination_anyS` — the crude `∂_τ` envelope, ANY `S`, NO gate hypothesis.**
    For the concrete gated van-Vleck witness at the fixed field point `0`, a width-gate record `D`, a
    time cap `τ₀`, and the zeroth amplitude sup-bounds (`hAmp0` on `chartFieldAmp`, `hCfield` on the
    affine slope `censusAmpTauDeriv`), there is an explicit `C > 0` with, uniformly over `0 < τ ≤ τ₀`
    and every gate base `z ∈ K`, `‖z‖ < D.r`,
        `|deriv (fun r ↦ Wit r 0 z) τ| ≤ C · τ⁻¹ · gaussDdim (4·D.lam·τ) z`.
    Crucially this holds for **ANY** `S : Point n → Set (Point n)` with NO S-membership hypothesis
    (eliminating the over-strong `hgate`/`S=univ` carry of the banked `witnessTimeDeriv_domination`):
    the banked envelope is applied at `S := univ`, then transferred to arbitrary `S` via the banked
    census-slice split `censusTauDeriv_gateSplit` (on the gate both derivatives equal the same
    S-independent closed form; off it the derivative is `0`).  NOT `a₁ = R/6`. -/
theorem witnessTimeDeriv_domination_anyS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M') :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ|
        ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z := by
  -- the `univ`-instance amplitude slope field: exactly `chartFieldAmp_hasDerivAt_tau`'s derivative value.
  set Cf : Point n → Point n → ℝ := fun z p =>
    radialCutoff a b (uniformInverseChart g gi hC hK z p)
      * (vanVleck g (uniformInverseChart g gi hC hK z p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK z p))
    with hCfdef
  have hCf0 : ∀ z : Point n, Cf z 0 = censusAmpTauDeriv g gi hC hK a b z := fun z => rfl
  -- the banked envelope at `S := univ` (over-strong `hgate` is trivial for `univ`).
  obtain ⟨C, hCpos, hbnd⟩ :=
    witnessTimeDeriv_domination hn g gi hC hK (fun _ => Set.univ) a b D τ₀ M M'
      hτ₀ hM hM' Cf
      (by
        intro w _ _
        exact ⟨Set.mem_univ _,
          QIQTH.OnGateJets.chartFieldAmp_hasDerivAt_tau g gi hC hK a b w.2.2 w.2.1 w.1⟩)
      hAmp0
      (by
        intro z hz hzr
        rw [hCf0]; exact hCfield z hz hzr)
  refine ⟨C, hCpos, ?_⟩
  intro τ hτ hτ0 z hzK hzr
  by_cases h0S : (0 : Point n) ∈ S z
  · -- ON the census gate: transfer to the `univ` derivative (same S-independent closed form).
    have heq : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ
        = deriv (fun u => vanVleckGatedWitness g gi hC hK (fun _ => Set.univ) a b u 0 z) τ := by
      rw [censusTauDeriv_gateSplit hn g gi hC hK S a b z τ,
          censusTauDeriv_gateSplit hn g gi hC hK (fun _ => Set.univ) a b z τ,
          if_pos ⟨hzK, h0S⟩, if_pos ⟨hzK, Set.mem_univ _⟩]
    rw [heq]
    exact hbnd τ hτ hτ0 z hzK hzr
  · -- OFF the census gate: the derivative is `0`, bound trivial.
    have hzero : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ = 0 := by
      rw [censusTauDeriv_gateSplit hn g gi hC hK S a b z τ, if_neg (fun h => h0S h.2)]
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg hCpos.le (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### §B — the GLOBAL-`z` extension, ANY `S`, NO gate hypothesis (only the honest `hSupp`).
    ############################################################################### -/

/-- **★★★ `witnessTimeDeriv_domination_global_anyS` — the crude `∂_τ` envelope for ALL `z`, ANY `S`.**
    Extends `witnessTimeDeriv_domination_anyS` off the gate ball, carrying ONLY the honest support fact
    `hSupp` (`z ∈ K`, `0 ∈ S z ⟹ ‖z‖ < D.r`; the SAME input as the banked
    `WitnessTimeDerivEnvelope.witnessTimeDeriv_domination_global`), with the over-strong `hgate`/`S=univ`
    carry REMOVED entirely (ANY `S`).  Off the census gate (`z ∉ K` or `0 ∉ S z`) the derivative is `0`
    (`censusTauDeriv_gateSplit`); on it, `hSupp` places `z` inside the gate ball and the on-ball bound
    applies.  This is a strictly-more-general drop-in for the banked `_global`.  NOT `a₁ = R/6`. -/
theorem witnessTimeDeriv_domination_global_anyS (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
      |deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ|
        ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z := by
  obtain ⟨C, hCpos, hbound⟩ :=
    witnessTimeDeriv_domination_anyS hn g gi hC hK S a b D τ₀ M M' hτ₀ hM hM' hAmp0 hCfield
  refine ⟨C, hCpos, ?_⟩
  intro τ hτ hτ0 z
  by_cases hzK : z ∈ K
  · by_cases h0S : (0 : Point n) ∈ S z
    · exact hbound τ hτ hτ0 z hzK (hSupp z hzK h0S)
    · have hzero : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ = 0 := by
        rw [censusTauDeriv_gateSplit hn g gi hC hK S a b z τ, if_neg (fun h => h0S h.2)]
      rw [hzero, abs_zero]
      exact mul_nonneg (mul_nonneg hCpos.le (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)
  · have hzero : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ = 0 := by
      rw [censusTauDeriv_gateSplit hn g gi hC hK S a b z τ, if_neg (fun h => hzK h.1)]
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg hCpos.le (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### §C — NON-VACUITY at a PROPER gate `S ≠ univ` (the anti-cp466 witness).
    ############################################################################### -/

/-- **★★ `census_anyS_env_satisfiable_properGate` — the bundle is satisfiable at a PROPER (non-`univ`)
    gate.**  For any geometry `(g, gi, hC)` at the singleton `K := {0}` (compact, nonempty) with `n > 0`,
    the gate `S z := Metric.ball 0 1` is PROPER (`S 0 ≠ Set.univ`, exhibiting the far point `2`) yet
    `0 ∈ S z`, and the full hypothesis bundle of `witnessTimeDeriv_domination_global_anyS` (`hAmp0`,
    `hCfield`, `hSupp`) is jointly satisfiable.  So the any-`S` envelope fires at a PROPER gate — S is
    NOT forced to `univ`.  This DIRECTLY refutes the cp466 analogy: unlike `hframeK` (flat-on-`K` forcing
    `K = {0}` by geometric incompatibility), the census gate `0 ∈ S z` imposes no geometric constraint.
    NOT `a₁ = R/6`. -/
theorem census_anyS_env_satisfiable_properGate (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (a b : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ),
      (0 : Point n) ∈ K ∧ 0 < τ₀ ∧ 0 ≤ M ∧ 0 ≤ M' ∧
      (∀ z, (0 : Point n) ∈ S z) ∧ (∀ z, S z ≠ Set.univ) ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK a b z| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  refine ⟨({0} : Set (Point n)), hK0, fun _ => Metric.ball (0 : Point n) 1,
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ },
    1, |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0|,
    |censusAmpTauDeriv g gi hC hK0 a b 0|,
    Set.mem_singleton_iff.mpr rfl, one_pos, by positivity, abs_nonneg _, ?_, ?_, ?_, ?_, ?_⟩
  · -- `0 ∈ S z`: `0 ∈ ball 0 1`.
    intro z; exact Metric.mem_ball_self one_pos
  · -- PROPER: `ball 0 1 ≠ univ`, via the far point `fun _ => 2` (norm `≥ 2 ≥ 1`).
    intro z
    rw [ne_eq, Set.eq_univ_iff_forall, not_forall]
    refine ⟨(fun _ => (2 : ℝ)), ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, not_lt]
    have hi : ‖(fun _ => (2 : ℝ) : Point n) (⟨0, hn⟩ : Fin n)‖
        ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ :=
      norm_le_pi_norm (fun _ => (2 : ℝ) : Point n) (⟨0, hn⟩ : Fin n)
    simp only [Real.norm_eq_abs] at hi
    norm_num at hi
    linarith
  · -- hAmp0: only `z = 0`; affine-in-τ bound with `τ ≤ 1`.
    intro τ hτ hτ1 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    have haff : chartFieldAmp g gi hC hK0 a b τ 0 0
        = chartFieldAmp g gi hC hK0 a b 0 0 0 + censusAmpTauDeriv g gi hC hK0 a b 0 * τ := by
      simp only [chartFieldAmp, censusAmpTauDeriv]; ring
    rw [haff]
    calc |chartFieldAmp g gi hC hK0 a b 0 0 0 + censusAmpTauDeriv g gi hC hK0 a b 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0 * τ| :=
          abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0| * 1 := by
          have : |censusAmpTauDeriv g gi hC hK0 a b 0| * τ
              ≤ |censusAmpTauDeriv g gi hC hK0 a b 0| * 1 :=
            mul_le_mul_of_nonneg_left hτ1 (abs_nonneg _)
          linarith
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0| + |censusAmpTauDeriv g gi hC hK0 a b 0| := by
          rw [mul_one]
  · -- hCfield: only `z = 0`; `|·| ≤ |·|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _
  · -- hSupp: `z = 0`, `‖0‖ = 0 < 1 = D.r`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    show ‖(0 : Point n)‖ < 1
    rw [norm_zero]; exact one_pos

end QIQTH.CensusTauDerivAnySEnvelope

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusTauDerivAnySEnvelope
#print axioms witnessTimeDeriv_domination_anyS
#print axioms witnessTimeDeriv_domination_global_anyS
#print axioms census_anyS_env_satisfiable_properGate
end AxiomChecks
