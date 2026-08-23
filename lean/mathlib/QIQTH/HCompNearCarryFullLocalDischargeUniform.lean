/-
  HCompNearCarryFullLocalDischargeUniform — J4-1050: a UNIFORM-IN-RADIUS strengthening of J4-1046's
  `kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge`.  J4-1046 delivered the full literal `kPrime`
  CoV identity (both `hxmem` and `hd` internally derived) on a domain `S'' ⊆ K ∩ Metric.ball x R`, for a
  SPECIFIC `R` produced as a one-shot existential.  cp1016/J4-1049 flagged that this `R`/`S''` had no
  `.mono`-style restriction principle to a smaller ball on record.  This file traces J4-1046's proof
  line-by-line and shows the "one-shot" nature is a PACKAGING artifact, not architectural: every
  ingredient downstream of the coverage radius `R` is pointwise-in-`z` (`z ∈ K`, `x ∈ S z`), so it
  restricts for free to any smaller ball; only the coverage fact `hcov` itself needs `Metric.ball_subset_
  ball`. This file re-derives the SAME conclusion shape uniformly for EVERY `0 < R' ≤ R`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES.  Re-derives J4-1046's outer existentials (`δ₀, δ₀', ρ₀, C_L, c, S, x, R`)
  IDENTICALLY (they are genuinely single-shot bookkeeping, unaffected by this change), and — for the
  FIRST time in this chain — additionally quantifies over `∀ R' : ℝ, 0 < R' → R' ≤ R → …`, producing,
  for EVERY such `R'`, a (possibly different, freshly re-derived) full literal `kPrime` CoV identity on
  some `S'' ⊆ K ∩ Metric.ball x R'`, with NEITHER `hxmem` NOR `hd` free.  The re-derivation reuses:
    • the SAME `PI_c, PJ_c, Q_c, hbigA` (from `hspecA`, obtained BEFORE `R`/`R'` are introduced — these
      are already universally quantified over ALL `z ∈ K` given `x ∈ S z`, so they never depended on any
      ball radius to begin with);
    • the SAME coverage fact `hcov : ∀ z ∈ K, z ∈ Metric.ball x R → x ∈ S z` (from J4-1042's
      `uniformFlowExp_local_coverage_ball`), composed with `Metric.ball_subset_ball` (`R' ≤ R` gives
      `Metric.ball x R' ⊆ Metric.ball x R`) to derive `hxmem'` on `K ∩ Metric.ball x R'`;
    • the IDENTICAL proof recipes for `hSopen, hJetVi, hJetVj, hJetQ, hAmpj1, hAmpi1, hAmp2, hd` — each
      of these, in J4-1046, is derived from `hbigA`/`hspecC` using ONLY `z ∈ K` and `x ∈ S z` (never any
      other set-level fact about the ball `U`), so the SAME proof terms discharge them for `U' :=
      Metric.ball x R'` verbatim (confirmed by direct line-by-line trace, and independently by
      gpt-5.6-sol high consulted BEFORE writing this file: "GO … your monotonicity argument is sound …
      there is no hidden dependence in the earlier existential witnesses");
    • J4-1043's `K ∩ U` wrapper `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU`, called AGAIN
      with `U := Metric.ball x R'` (this wrapper takes `U` as a genuine caller-supplied free parameter,
      not tied to any specific existential — confirmed from its own signature, which quantifies every
      jet/amp/coverage hypothesis over `∀ z ∈ K ∩ U` for an ARBITRARY open `U ∋ x` the caller supplies).
  Sol also flagged one genuine trap to check: whether the wrapper's OWN Step A (`BaseSlotM1M4Assembly.
  uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint`) secretly depends on `U`. Direct
  inspection of its call site confirms it does NOT — it is called with ONLY `g gi hC hK hxint`, no `U`
  argument at all, so it is safe to call the wrapper repeatedly at different `U' := Metric.ball x R'`.

  ── WHAT THIS DOES **NOT** DO.  It does NOT discharge `hxint` or `hτ` (still assumed, exactly as in
  J4-1046). It does NOT claim `r6`, `nb`, or `hcomp` is closed. It does NOT literally identify the `S'',
  V, PI, PJ, Q` across different `R'` as being ONE FIXED tuple (each `R'` gets its own fresh call to the
  wrapper) — it delivers "for every `R'` a valid instance", which is exactly the shape needed to feed a
  FUTURE common-radius merge (mirroring `ChartEvalSlotRadiusMerge`'s `nb_common_chart_radius`), but does
  NOT itself build that merge with J4-1012/1013/1014's radii. `hxmem`'s GENERAL discharge on all of `K`
  remains DEFINITIVELY CLOSED OFF (cp988–991, unchanged — this file only ever works on `K ∩ (a ball)`).
  `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on
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

namespace QIQTH.HCompNearCarryFullLocalDischargeUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge_uniform`.**  The UNIFORM-IN-RADIUS
    strengthening of J4-1046: the SAME full literal `kPrime` CoV identity (both `hxmem` and `hd`
    internally derived, no `sorry`), now delivered for EVERY `0 < R' ≤ R` (not just the specific `R`
    the coverage existential happened to produce), on `S'' ⊆ K ∩ Metric.ball x R'`. NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge_uniform
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
    ∀ R' : ℝ, 0 < R' → R' ≤ R →
    ∃ (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
      (S'' : Set (Point n)) (V : Point n → Point n),
      IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∩ Metric.ball x R' ∧
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
  intro hτ R' hR'0 hR'R
  set U : Set (Point n) := Metric.ball x R' with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self hR'0
  have hballsub : Metric.ball x R' ⊆ Metric.ball x R := Metric.ball_subset_ball hR'R
  -- The ONE shared `hxmem` witness on the SMALLER ball, derived (not assumed) from the SAME `hcov`
  -- as J4-1046's, composed with `Metric.ball_subset_ball` — fed into BOTH downstream consumers below.
  have hxmem : ∀ z ∈ K ∩ U, x ∈ S z := by
    intro z hz
    rw [hSeq]
    exact hcov z hz.1 (hballsub hz.2)
  -- Consumer 1 (J4-1044's method): jet-bundle + hSopen, via `hcarField2_hgate_concrete`. Verbatim as
  -- in J4-1046 — only ever uses `z ∈ K` and `x ∈ S z`, never any other property of `U`.
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
  -- reusing the SAME `hxmem` witness. Verbatim as in J4-1046 — only ever uses `z ∈ K` and `x ∈ S z`.
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

end QIQTH.HCompNearCarryFullLocalDischargeUniform

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryFullLocalDischargeUniform
#print axioms kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge_uniform
end AxiomChecks
