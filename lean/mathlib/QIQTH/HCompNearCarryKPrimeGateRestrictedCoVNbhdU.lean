/-
  HCompNearCarryKPrimeGateRestrictedCoVNbhdU — J4-1043: the U-SHRUNK port of J4-1031
  (`HCompNearCarryKPrimeGateRestrictedCoVNbhd.kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd`),
  quantifying every jet/amp/coverage hypothesis over `z ∈ K ∩ U` for an EXPLICIT, CALLER-SUPPLIED open
  neighbourhood `U ∋ x`, instead of over all of `z ∈ K`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  hypothesis-WEAKENING port: every conclusion is IDENTICAL in shape to J4-1031's, only the antecedent
  jet/amp/coverage hypotheses are relaxed from `∀ z ∈ K` to `∀ z ∈ K ∩ U` for an explicit open `U ∋ x`
  supplied by the CALLER (not existentially produced inside this proof). No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited (NEW FILE).  Does NOT discharge `hxmem` (still an open hypothesis here, merely narrower) — it
  proves the WRAPPER's interface can be shrunk to `K ∩ U`, which is the shape J4-1042's LOCAL coverage
  fact (`uniformFlowExp_local_coverage_ball`, coverage on `K ∩ Metric.ball x R`, NOT all of `K`) can
  actually discharge.

  ── WHY THIS IS A NEW FILE, NOT A ONE-LINE CALL.  J4-1042 (`HxmemLocalSharpReachCoverage`) found that
  `hxmem`'s real analytic content only needs to hold on a neighbourhood of `x`, not literally all of `K`
  — but it explicitly could NOT plug this into J4-1031/1032 as-is, because those theorems' STATED TYPES
  fix every jet/amp/coverage binder at `∀ z ∈ K`.  Lean cannot accept a weaker hypothesis at a call site
  when the callee's own binder says `∀ z ∈ K`: shrinking the *set of z's the caller must supply data for*
  requires literally re-stating the wrapper with a narrower binder.  (Confirmed against gpt-5.6-sol high
  before writing any Lean: not a mechanical drop-in; a new U-parameterized statement is the right shape,
  reusing J4-1031's OWN Steps 1–2 lemmas unchanged — only Step 3's wrapper needs the binder to move from
  `K` to `K ∩ U`.)

  ── WHAT CHANGES VS J4-1031, PRECISELY.  J4-1031's proof of the wrapper theorem
  `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd` runs:
    Step A: `BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint` — gives
      IFT-open `S' ∋ x`.  Uses ONLY `hxint`; does NOT touch `hxmem`/hJetVi/etc. UNCHANGED here.
    Step B: `S'' := S' ∩ interior K`.  HERE we instead set `S'' := S' ∩ interior K ∩ U` (additionally
      intersecting with the caller-supplied open `U`) — still open, still `x ∈ S''` (since `x ∈ S'`,
      `x ∈ interior K` from `hxint`, and `x ∈ U` from the new hypothesis `hxU`), and now `S'' ⊆ K ∩ U`.
    Step C: restrict the M1–M4 data from `S'` to `S''` via `.mono` — IDENTICAL, since `S'' ⊆ S'`
      regardless of the extra `∩ U`.
    Step D: the abstract CoV corollary on `S''` — IDENTICAL.
    Step E: the pointwise factorization `hfac : ∀ z ∈ S'', …` — for `z ∈ S''`, `hS''subKU hz : z ∈ K ∩ U`
      (instead of J4-1031's `hS''subK hz : z ∈ K`), which is EXACTLY what the now-`K ∩ U`-quantified
      `hJetVi/hJetVj/hJetQ/hAmpj1/hAmpi1/hAmp2/hxmem/hd` (all supplied by the caller only for `z ∈ K ∩ U`)
      need to be instantiated.  Step 1/2's underlying pointwise lemmas
      (`kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd`, J4-1031, REUSED UNCHANGED — imported,
      not re-proved) only ever needed data AT a single `z`, so shrinking the caller's binder from `K` to
      `K ∩ U` does not touch them at all.

  `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd
import QIQTH.BaseSlotM1M4Assembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★ `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU`.**  The `K ∩ U`-shrunk port of
    J4-1031's `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd`: identical conclusion shape (the
    same literal `kPrime` CoV identity, `S''` now additionally constrained `S'' ⊆ K ∩ U`), but EVERY
    jet/amp/coverage/differentiability hypothesis is quantified only over `z ∈ K ∩ U` for the explicit,
    caller-supplied open `U ∋ x`, instead of over all of `z ∈ K`.  Reuses J4-1031's Step-1/2 pointwise
    lemma UNCHANGED (imported, not re-proved) and `BaseSlotM1M4Assembly`'s IFT data UNCHANGED (it never
    depended on `hxmem` or `U` to begin with).  NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) {x : Point n} (hxint : x ∈ interior K)
    (U : Set (Point n)) (hUopen : IsOpen U) (hxU : x ∈ U)
    (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z ∈ K ∩ U, IsOpen (S z)) (hxmem : ∀ z ∈ K ∩ U, x ∈ S z) (hτ : 0 < t - s)
    (hd : ∀ z ∈ K ∩ U, DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (hJetVi : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k) (PI z x k) (x j))
    (hJetVj : ∀ z ∈ K ∩ U, ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ z y k) (y i))
    (hJetQ : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ z (Function.update x j σ) k) (Q z k) (x j))
    (hAmpj1 : ∀ z ∈ K ∩ U, ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
    (hAmpi1 : ∀ z ∈ K ∩ U, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x)
    (hAmp2 : ∀ z ∈ K ∩ U, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) :
    ∃ (S'' : Set (Point n)) (V : Point n → Point n),
      IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∩ U ∧
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
                * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k) / (4 * (t - s) ^ 2)
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
  -- Step A: the raw M1–M4 data on the IFT set `S'` (Bfac/τ-independent). UNCHANGED from J4-1031.
  obtain ⟨S', V, hS'open, hxS', hinj, hVeq, hfd, hJpos⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint
  -- Step B: gate-restrict to `S'' := S' ∩ interior K ∩ U ⊆ K ∩ U`. (The `∩ U` is the new shrink.)
  set S'' : Set (Point n) := S' ∩ interior K ∩ U with hS''def
  have hS''open : IsOpen S'' := (hS'open.inter isOpen_interior).inter hUopen
  have hxS'' : x ∈ S'' := ⟨⟨hxS', hxint⟩, hxU⟩
  have hS''subKU : S'' ⊆ K ∩ U := fun z hz => ⟨interior_subset hz.1.2, hz.2⟩
  have hS''subS' : S'' ⊆ S' := fun z hz => hz.1.1
  -- Step C: restrict M1–M4 from `S'` to `S''`. UNCHANGED (only depends on `S'' ⊆ S'`).
  have hinj'' : Set.InjOn W S'' := hinj.mono hS''subS'
  have hVeq'' : ∀ p ∈ S'', V (W p) = p := fun p hp => hVeq p (hS''subS' hp)
  have hfd'' : ∀ z ∈ S'', HasFDerivWithinAt W (fderiv ℝ W z) S'' z :=
    fun z hz => (hfd z (hS''subS' hz)).mono hS''subS'
  have hJpos'' : ∀ z ∈ S'', 0 < |(fderiv ℝ W z).det| := fun z hz => hJpos z (hS''subS' hz)
  have hS''meas : MeasurableSet S'' := hS''open.measurableSet
  -- Step D: invoke the abstract CoV corollary directly on `S''`. UNCHANGED.
  have hCoV :=
    QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables (t - s) S'' W V
      (fun z => fderiv ℝ W z) (fun z => |(fderiv ℝ W z).det|) Bfac hS''meas hfd'' hinj'' hVeq''
      (fun z _ => rfl) hJpos''
  -- Step E: discharge the factorization pointwise across `S''`, now via `K ∩ U`-quantified hypotheses.
  have hfac : ∀ z ∈ S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
      = gaussDdim (t - s) (W z) * Bfac z := by
    intro z hz
    have hzKU : z ∈ K ∩ U := hS''subKU hz
    have := QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd
      g gi hC hK S a b i j t s x z hzKU.1 (hSopen z hzKU) (hxmem z hzKU) hτ (hd z hzKU)
      (PI z) (PJ z) (Q z) (hJetVi z hzKU) (hJetVj z hzKU) (hJetQ z hzKU)
      (hAmpj1 z hzKU) (hAmpi1 z hzKU) (hAmp2 z hzKU)
    simpa [hWdef, hBfacdef] using this
  have hcong : (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = ∫ z in S'', gaussDdim (t - s) (W z) * Bfac z :=
    setIntegral_congr_fun hS''meas hfac
  refine ⟨S'', V, hS''open, hxS'', hS''subKU, ?_⟩
  rw [hcong]
  simpa [hWdef, hBfacdef] using hCoV

end QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU
#print axioms kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU
end AxiomChecks
