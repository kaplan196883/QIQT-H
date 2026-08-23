/-
  HCompNearCarryFullLocalDischarge — J4-1046: composes J4-1044's `hxmem`-free jet-bundle discharge
  (`HCompNearCarryJetBundleLocalCoverageDischarge`) with J4-1045's `hd`-free discharge method
  (`HCompNearCarryHdLocalCoverageDischarge`), reusing the SAME `hxmem` witness (sourced once from
  J4-1042's `uniformFlowExp_local_coverage_ball`) for BOTH, to produce — for the FIRST time in this
  chain — the FULL literal `kPrime` CoV identity with **BOTH** `hxmem` AND `hd` eliminated as free
  hypotheses, on the common shrunk domain `K ∩ Metric.ball x R`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES.  J4-1044 discharged `hxmem` (via J4-1042's local coverage) and the six jet/
  amp hypotheses (via J4-1032's `hcarField2_hgate_concrete`) on `K ∩ Metric.ball x R`, but still left
  `hd` as an EXTERNAL hypothesis on that same domain. J4-1045 separately showed `hd` ITSELF can be
  derived (via `ConcreteGateAssembly.reachableGate_concrete` + `OnGateFieldRegularity.
  gatedWitness_contDiffAt_field` + `HFdCoreContinuityClosed.pd_contDiffAt_one_of_two`) from the SAME
  kind of `hxmem` witness, but as a STANDALONE theorem, never fed into J4-1043's `K ∩ U` wrapper
  alongside J4-1044's jet-bundle discharge.

  This file derives ONE shared `hxmem` witness (`x ∈ S z` for `z ∈ K ∩ Metric.ball x R`, from J4-1042)
  and feeds it into BOTH consumers: J4-1032's `hcarField2_hgate_concrete` (jet-bundle + `hSopen`, as in
  J4-1044) AND `reachableGate_concrete` + the field-regularity chain (`hd`, as in J4-1045), then supplies
  ALL of `hSopen, hxmem, hd`, and the six jet/amp hypotheses to J4-1043's `K ∩ U` wrapper
  (`kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU`) with `U := Metric.ball x R`. The resulting
  theorem's conclusion is the literal `kPrime` CoV identity on some `S'' ⊆ K ∩ Metric.ball x R`, with
  **NEITHER `hxmem` NOR `hd` appearing as a hypothesis of the final theorem** — both are internally
  derived. Confirmed GO by gpt-5.6-sol (high) before writing this file: the composition reuses the SAME
  proof term for the shared `hxmem` witness in both consumers (safe by proof irrelevance — Lean only
  needs the propositions to match, not the derivations), and the two source lemmas' differing `c`
  side-conditions (`b < c < δ₀` from `hcarField2_hgate_concrete`, `0 < c < δ₀'` from
  `reachableGate_concrete`, `0 < c ≤ ρ₀ ∧ C_L·c < 1` from the local coverage lemma) are jointly
  existentially quantified as pure bookkeeping (sympy-checked satisfiable for generic positive
  constants in `docs/qg_roadmap/rnc_sympy/j4_1046_c_bookkeeping_check.py` — no hidden contradiction).

  ── WHAT THIS DOES **NOT** DO.  It does NOT discharge `hxint` (still assumed: `x ∈ interior K`). It
  does NOT discharge `hτ` (still assumed: `0 < t - s`). It does NOT claim `r6`, `nb`, or `hcomp` is
  closed: the delivered domain `S'' ⊆ K ∩ Metric.ball x R` is STRICTLY SMALLER than all of `K` — points
  of `K` outside this ball still have no discharge of ANY of these hypotheses, and per cp988–991,
  `hxmem`'s GENERAL discharge on all of `K` remains DEFINITIVELY CLOSED OFF (this file does not revisit
  that). It does NOT attempt r6's own remaining 4-lemma composition (per cp1008: pointwise domination
  for a CoV-transported coefficient, matched CoV for the reference term, signed-vs-majorant bound from
  containment, a τ-integration mismatch to reconcile) — this file supplies exactly the "literal
  integrand Lipschitz" / literal-CoV-identity ingredient cp1009 flagged as missing (the one place
  `hxmem` entered r6's chain), on the shrunk domain, but the OTHER three composition lemmas r6 needs
  (linking this identity to `J4-1012/1013/1014/1020/1022/1023/1016`) are NOT built here. `Bfac`'s other
  3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU
import QIQTH.HxmemLocalSharpReachCoverage
import QIQTH.Field2NbhdReshape
import QIQTH.ConcreteGateAssembly
import QIQTH.OnGateFieldRegularity
import QIQTH.HFdCoreContinuityClosed
import QIQTH.ExpMap

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ConcreteGateAssembly QIQTH.OnGateFieldRegularity QIQTH.HFdCoreContinuityClosed
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryFullLocalDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge`.**  The FULL literal `kPrime` CoV
    identity with **BOTH** `hxmem` AND `hd` eliminated as free hypotheses: both are internally derived
    on the shrunk domain `K ∩ Metric.ball x R` from a single shared coverage witness (J4-1042), fed
    respectively into J4-1032's jet-bundle brick and the `reachableGate_concrete` + field-regularity
    chain (J4-1045's method), then both supplied to J4-1043's `K ∩ U` wrapper with `U := Metric.ball x R`.
    The ONLY hypotheses beyond radius/metric-regularity bookkeeping are `hxint` and `hτ`. NOT
    `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i j : Fin n) (t s : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∃ δ₀' > (0 : ℝ), ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧
    ∀ c : ℝ, b < c → c < δ₀ → 0 < c → c < δ₀' → c ≤ ρ₀ → C_L * c < 1 →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∀ {x : Point n}, x ∈ interior K →
    ∃ R > (0 : ℝ),
    ∀ (hτ : 0 < t - s),
    ∃ (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
      (S'' : Set (Point n)) (V : Point n → Point n),
      IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∩ Metric.ball x R ∧
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
  obtain ⟨δ₀, hδ₀, hspecA⟩ :=
    QIQTH.Field2NbhdReshape.hcarField2_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  obtain ⟨δ₀', hδ₀', hspecC⟩ := QIQTH.ConcreteGateAssembly.reachableGate_concrete g gi hC hK
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hloccov⟩ :=
    QIQTH.HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball g gi hC hK
  refine ⟨δ₀, hδ₀, δ₀', hδ₀', ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hbc hcδ hc0 hcδ' hcρ hCLc S hSeq x hxint
  obtain ⟨PI_c, PJ_c, Q_c, hbigA⟩ := hspecA c hbc hcδ S hSeq j i
  obtain ⟨R, hR, hcov⟩ := hloccov c hc0 hcρ hCLc x
  refine ⟨R, hR, ?_⟩
  intro hτ
  set U : Set (Point n) := Metric.ball x R with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self hR
  -- The ONE shared `hxmem` witness, derived (not assumed), fed into BOTH downstream consumers below.
  have hxmem : ∀ z ∈ K ∩ U, x ∈ S z := by
    intro z hz
    rw [hSeq]
    exact hcov z hz.1 hz.2
  -- Consumer 1 (J4-1044's method): jet-bundle + hSopen, via `hcarField2_hgate_concrete`.
  have hSopen : ∀ z ∈ K ∩ U, IsOpen (S z) := by
    intro z hz
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).1
  have hJetVi : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k)
      (PI_c z x k) (x j) := by
    intro z hz k
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.1 x (hxmem z hz) k
  have hJetVj : ∀ z ∈ K ∩ U, ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k)
      (PJ_c z y k) (y i) := by
    intro z hz y hy k
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.1 y hy k
  set Qf : Point n → Fin n → ℝ := fun z k => Q_c z x k with hQfdef
  have hJetQ : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ_c z (Function.update x j σ) k) (Qf z k) (x j) := by
    intro z hz k
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.1 k
  have hAmpj1 : ∀ z ∈ K ∩ U, ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y := by
    intro z hz y hy
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.1 y hy
  have hAmpi1 : ∀ z ∈ K ∩ U, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x := by
    intro z hz
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.2.1
  have hAmp2 : ∀ z ∈ K ∩ U, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x := by
    intro z hz
    exact (hbigA (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.2.2
  -- Consumer 2 (J4-1045's method): `hd`, via `reachableGate_concrete` + field-regularity chain,
  -- reusing the SAME `hxmem` witness (safe by proof irrelevance — only the proposition matters).
  have hd : ∀ z ∈ K ∩ U, DifferentiableAt ℝ
      (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x := by
    intro z hz
    have hzK : z ∈ K := hz.1
    have hxSz : x ∈ S z := hxmem z hz
    obtain ⟨hSopenz, _hLI, hReach⟩ := hspecC c hc0 hcδ' z hzK
    have hSeqOpen : IsOpen (S z) := by rw [hSeq]; exact hSopenz
    have hxSz' : x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by
      rw [hSeq] at hxSz; exact hxSz
    obtain ⟨_hReachx, hWC2⟩ := hReach x hxSz'
    have hCD2 : ContDiffAt ℝ 2
        (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x :=
      QIQTH.OnGateFieldRegularity.gatedWitness_contDiffAt_field g gi hC hK S a b (t - s) z x
        hzK hxSz hSeqOpen hWC2 hg hgpos hu
    have hC1 : ContDiffAt ℝ 1
        (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i y) x :=
      QIQTH.HFdCoreContinuityClosed.pd_contDiffAt_one_of_two
        (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x hCD2
    have hDiff : DifferentiableAt ℝ
        (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i y) x :=
      hC1.differentiableAt (by norm_num)
    simpa [witnessFieldDeriv] using hDiff
  obtain ⟨S'', V, hS''open, hxS'', hS''subKU, hCoV⟩ :=
    QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU.kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU
      g gi hC hK S a b i j t s hxint U hUopen hxU PI_c PJ_c Qf hSopen hxmem hτ hd
      hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2
  exact ⟨PI_c, PJ_c, Qf, S'', V, hS''open, hxS'', hS''subKU, hCoV⟩

end QIQTH.HCompNearCarryFullLocalDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryFullLocalDischarge
#print axioms kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge
end AxiomChecks
