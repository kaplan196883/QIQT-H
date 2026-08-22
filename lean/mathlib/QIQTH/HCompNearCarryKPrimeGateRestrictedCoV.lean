/-
  HCompNearCarryKPrimeGateRestrictedCoV — J4-1029: discharging residual (r1) of
  `HCompNearCarryKPrimeBaseFieldCoV` (J4-1010) — replacing BRICK 2's opaque `hfac` hypothesis by an
  explicit ON-GATE (`z ∈ K`) jet-bundle hypothesis, and a genuinely gate-restricted CoV domain
  `S'' := S' ∩ interior K ⊆ K`, so BRICK 1 becomes literally APPLICABLE pointwise across the WHOLE
  change-of-variables domain (not merely a hypothesis asserting so).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT / GAP THIS CLOSES.  `HCompNearCarryKPrimeBaseFieldCoV.kPrime_baseField_CoV_of_factorization`
  (BRICK 2, J4-1010) produced the CoV identity on an IFT-selected open set `S'` (Mathlib's
  `HasStrictFDerivAt.toOpenPartialHomeomorph` source) CONDITIONAL on `hfac : ∀ z ∈ S', kPrime(...) =
  gaussDdim(...) * Bfac z` — a bare hypothesis, NOT discharged, because BRICK 1
  (`kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`) is ON-GATE (`hz : z ∈ K`), while `S'` is an
  ARBITRARY IFT neighbourhood with no guarantee `S' ⊆ K`.  This was residual (r1) (mismatch of `S'` vs
  the gate `K`) and residual (r2) ("BRICK 1's on-gate jet bundle uniformly over `S'`") of J4-1010's own
  honest-scope firewall, restated verbatim in J4-1028's residual list.

  ## WHAT LANDS (Sol `gpt-5.6-sol`, high, 2026-08-23, plan-reviewed before Lean; endorsed EXACTLY this
  scope — "bank the restricted-neighbourhood CoV wrapper and pointwise BRICK-1 assembly under an
  explicit uniform jet-bundle assumption", flagged the FULL jet bundle (r2) as a genuinely large,
  multi-file derivative-existence development — NOT attempted here, see honesty firewall).
    • `kPrime_baseField_CoV_of_jetBundle_gateRestricted` — takes `x ∈ interior K` and an ON-GATE
      (`∀ z ∈ K`, not merely `∀ z ∈ S'`) jet bundle — the EXACT hypothesis list BRICK 1 itself needs,
      now parametrized over `z` — and returns:
        - a genuinely gate-restricted open CoV domain `S'' := S' ∩ interior K`, WITH `S'' ⊆ K` proved
          (via `interior_subset`), closing r1 outright (previously `S'` carried no such inclusion);
        - the literal CoV identity `∫ z in S'', kPrime(...) = ∫ w in W''S'', gaussDdim * (Bfac∘V / |det|)`,
          with `hfac` DISCHARGED (not assumed) by pointwise BRICK 1 application at each `z ∈ S''`
          (using `z ∈ S'' ⟹ z ∈ K` via `interior_subset`), replacing BRICK 2's opaque hypothesis by a
          genuine composition.
    Route: re-derive M1–M4 directly from `BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK`
    (NOT via BRICK 2's own `S'`-level packaging, since M1–M4 restrict cleanly to subsets — `InjOn.mono`,
    `HasFDerivWithinAt.mono`, pointwise facts trivially inherited — while the ALREADY-INSTANTIATED CoV
    identity on `S'` does not), intersect with `interior K`, restrict M1–M4 to `S''`, and re-invoke
    `ChartGaussianChangeVar.chart_gaussian_change_variables` directly on `S''`.

  ## WHAT THIS FILE DOES **NOT** DO (honest scope; do NOT over-claim).
    (a) It does NOT discharge the jet bundle itself (r2) — i.e. it does NOT prove that
        `witnessFieldDeriv`/`uniformInverseChart`/`chartFieldAmp` actually HAVE the required
        derivatives (`hd`, `hJetVi`, `hJetVj`, `hJetQ`, `hAmpj1`, `hAmpi1`, `hAmp2`) for every `z ∈ K` —
        that remains a genuinely separate, and per Sol's assessment, LARGE (comparable in size to the
        5-dispatch J4-1024..1028 chain) construction effort: new smoothness/derivative-identification
        lemmas for the concrete chart maps at a GENERAL base point `z`, currently supplied nowhere in
        the campaign (checked: no existing consumer of BRICK 1 —
        `HCompNearCarryChartSurfaceWired`/`HCompNearCarryHsMixedHeatHessMultBridge`/
        `ReversalLinkBallIntegral` — discharges this bundle concretely; the campaign's GLOBAL
        bound+Lipschitz work, J4-1024–1028, is a DIFFERENT, weaker kind of fact — continuity-type
        regularity, not derivative EXISTENCE with a specified closed-form derivative value).
    (b) It does NOT touch `Bfac`'s other three summands beyond the shape BRICK 1 already produces (this
        file reuses BRICK 1's `Bfac` VERBATIM; the `grⱼ·∂ⱼA`/`grᵢ·∂ᵢA`/`∂ⱼ∂ᵢA` sub-pieces remain exactly
        as far along as J4-1010/1027/1028 left them, i.e. NOT independently regularized here).
    (c) `fb` (the far carry) remains SEPARATELY open, untouched.
    (d) Residuals r3 (`ball x ρ` vs `S''`), r4 (`W''S''` vs `ball 0 R`), r5 (slot-reversal `U z x` vs
        `U x z` vs `terminalVelAt`), r6 (antisymmetrization producing the near-isometry DIFFERENCE, not
        a single Gaussian) are UNCHANGED and untouched by this file.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeBaseFieldCoV

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryKPrimeGateRestrictedCoV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★ `kPrime_baseField_CoV_of_jetBundle_gateRestricted` — J4-1029, residual r1 CLOSED.**
Given `x ∈ interior K` and an ON-GATE (`∀ z ∈ K`) jet bundle — the exact hypothesis list BRICK 1
(`HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`) needs,
parametrized over `z` — produces a genuinely gate-restricted open CoV domain `S'' ⊆ K` and the literal
`kPrime` change-of-variables identity, with the factorization hypothesis DISCHARGED (not assumed) by
pointwise BRICK 1 application.  Residual r2 (deriving the jet bundle itself) remains OPEN — see file
firewall.  NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_gateRestricted
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) {x : Point n} (hxint : x ∈ interior K)
    (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z ∈ K, IsOpen (S z)) (hxmem : ∀ z ∈ K, x ∈ S z) (hτ : 0 < t - s)
    (hd : ∀ z ∈ K, DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (hJetVi : ∀ z ∈ K, ∀ y k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y j σ) k) (PI z y k) (y j))
    (hJetVj : ∀ z ∈ K, ∀ y k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ z y k) (y i))
    (hJetQ : ∀ z ∈ K, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ z (Function.update x j σ) k) (Q z k) (x j))
    (hAmpj1 : ∀ z ∈ K, ∀ y, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
    (hAmpi1 : ∀ z ∈ K, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x)
    (hAmp2 : ∀ z ∈ K, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) :
    ∃ (S'' : Set (Point n)) (V : Point n → Point n),
      IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∧
      (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
        = ∫ w in (fun p => uniformInverseChart g gi hC hK p x) '' S'',
            gaussDdim (t - s) w
              * ((fun z =>
                    leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
                      * (((∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                              * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                              / (4 * (t - s) ^ 2)
                            - ((∑ k, PI z x k * PJ z x k)
                                + (∑ k, uniformInverseChart g gi hC hK z x k * Q z k))
                              / (2 * (t - s)))
                            * chartFieldAmp g gi hC hK a b (t - s) z x
                          + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                                / (2 * (t - s)))
                              * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
                          + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                                / (2 * (t - s)))
                              * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
                          + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x))
                  (V w)
                  / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p x) (V w)).det|) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p x with hWdef
  set Bfac : Point n → ℝ := fun z =>
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        * (((∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                / (4 * (t - s) ^ 2)
              - ((∑ k, PI z x k * PJ z x k)
                  + (∑ k, uniformInverseChart g gi hC hK z x k * Q z k))
                / (2 * (t - s)))
              * chartFieldAmp g gi hC hK a b (t - s) z x
            + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                  / (2 * (t - s)))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
            + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                  / (2 * (t - s)))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
            + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) with hBfacdef
  -- Step A: the raw M1–M4 data on the IFT set `S'` (Bfac/τ-independent).
  obtain ⟨S', V, hS'open, hxS', hinj, hVeq, hfd, hJpos⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint
  -- Step B: gate-restrict to `S'' := S' ∩ interior K ⊆ K`.
  set S'' : Set (Point n) := S' ∩ interior K with hS''def
  have hS''open : IsOpen S'' := hS'open.inter isOpen_interior
  have hxS'' : x ∈ S'' := ⟨hxS', hxint⟩
  have hS''subK : S'' ⊆ K := fun z hz => interior_subset hz.2
  have hS''subS' : S'' ⊆ S' := Set.inter_subset_left
  -- Step C: restrict M1–M4 from `S'` to `S''`.
  have hinj'' : Set.InjOn W S'' := hinj.mono hS''subS'
  have hVeq'' : ∀ p ∈ S'', V (W p) = p := fun p hp => hVeq p (hS''subS' hp)
  have hfd'' : ∀ z ∈ S'', HasFDerivWithinAt W (fderiv ℝ W z) S'' z :=
    fun z hz => (hfd z (hS''subS' hz)).mono hS''subS'
  have hJpos'' : ∀ z ∈ S'', 0 < |(fderiv ℝ W z).det| := fun z hz => hJpos z (hS''subS' hz)
  have hS''meas : MeasurableSet S'' := hS''open.measurableSet
  -- Step D: invoke the abstract CoV corollary directly on `S''`.
  have hCoV :=
    QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables (t - s) S'' W V
      (fun z => fderiv ℝ W z) (fun z => |(fderiv ℝ W z).det|) Bfac hS''meas hfd'' hinj'' hVeq''
      (fun z _ => rfl) hJpos''
  -- Step E: discharge the factorization pointwise across `S''` via BRICK 1.
  have hfac : ∀ z ∈ S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
      = gaussDdim (t - s) (W z) * Bfac z := by
    intro z hz
    have hzK : z ∈ K := hS''subK hz
    have := QIQTH.HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp
      g gi hC hK S a b i j t s x z hzK (hSopen z hzK) (hxmem z hzK) hτ (hd z hzK)
      (PI z) (PJ z) (Q z) (hJetVi z hzK) (hJetVj z hzK) (hJetQ z hzK)
      (hAmpj1 z hzK) (hAmpi1 z hzK) (hAmp2 z hzK)
    simpa [hWdef, hBfacdef] using this
  have hcong : (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = ∫ z in S'', gaussDdim (t - s) (W z) * Bfac z :=
    setIntegral_congr_fun hS''meas hfac
  refine ⟨S'', V, hS''open, hxS'', hS''subK, ?_⟩
  rw [hcong]
  simpa [hWdef, hBfacdef] using hCoV

end QIQTH.HCompNearCarryKPrimeGateRestrictedCoV

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryKPrimeGateRestrictedCoV
#print axioms kPrime_baseField_CoV_of_jetBundle_gateRestricted
end AxiomChecks
