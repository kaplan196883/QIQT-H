/-
  HCompNearCarryJetBundleConcreteGateDischarge — J4-1032: the JET-BUNDLE piece of J4-1031's shrunk
  interface (`hJetVi`/`hJetVj`/`hJetQ`/`hAmpj1`/`hAmpi1`/`hAmp2`) FULLY DISCHARGED at the CONCRETE
  flow-ball gate `S z = uniformFlowExp z '' Metric.ball 0 c`, by directly reusing the ALREADY-BANKED
  J4-237 brick `Field2NbhdReshape.hcarField2_hgate_concrete` (with the index pair swapped `(j, i)`
  instead of `(i, j)`) rather than the newly-built `GeneralBaseJetsMixed` (J4-1030).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── THE COMPOSITION FINDING (this dispatch's audit, checked BEFORE writing any Lean).  J4-1031
  (`HCompNearCarryKPrimeGateRestrictedCoVNbhd.kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd`)
  shrank its jet-bundle antecedent to
    `hJetVi : ∀ z ∈ K, ∀ k, HasDerivAt (… update x j σ …) (PI z x k) (x j)`               (single point `x`)
    `hJetVj : ∀ z ∈ K, ∀ y ∈ S z, ∀ k, HasDerivAt (… update y i σ …) (PJ z y k) (y i)`     (open gate `S z`)
    `hJetQ  : ∀ z ∈ K, ∀ k, HasDerivAt (fun σ ↦ PJ z (update x j σ) k) (Q z k) (x j)`
    `hAmpj1/hAmpi1/hAmp2` — three matching `PdiffAt` clauses on the same gate/point pattern.
  J4-1030 (`GeneralBaseJetsMixed`) supplies jets only in a NON-CONSTRUCTIVE `∀ᶠ x in 𝓝 0` neighbourhood
  of the LITERAL FIELD-COORDINATE ORIGIN `0` (via `ContDiffAt.fderiv_right` at the CENTRE only), with no
  extractable radius — so comparing that neighbourhood against the concrete geometric gate `S z` (an
  explicit flow-ball image) is NOT mechanically checkable; J4-1030's own firewall already flags this as
  unresolved ("does not establish that one fixed x is reachable from every z ∈ K").

  Tracing `Field2NbhdReshape.hcarField2_hgate_concrete` (J4-237, ALREADY BANKED, PRE-DATING both
  J4-1030 and J4-1031) instead: it is STRICTLY STRONGER than J4-1030 for this purpose — it supplies
  first/second field-jets at EVERY point `y` of the CONCRETE gate `S z` (via
  `ChartFieldC2General.chartField_contDiffAt_reachable_uniform`, uniform reachability, not just the
  origin), in EXACTLY the `∀ y ∈ S z` shape J4-1031 wants, for a GENERIC index pair `(i, j)`. Comparing
  term-by-term (this dispatch's own trace, not asserted from memory):
    hcarField2(i', j') at `w = (τ, p, z)`, `p ∈ S z`, unlocks 7 conjuncts:
      (1) `IsOpen (S z)`
      (2) `∀ y ∈ S z, ∀ k, HasDerivAt (… update y i' …) (Pifield z y k) (y i')`
      (3) `∀ y ∈ S z, ∀ k, HasDerivAt (… update y j' …) (Pjfield z y k) (y j')`
      (4) `∀ k, HasDerivAt (fun s ↦ Pjfield z (update p i' s) k) (Qfield z p k) (p i')`
      (5) `∀ y ∈ S z, PdiffAt (amp) j' y`
      (6) `PdiffAt (amp) i' p`
      (7) `PdiffAt (fun y ↦ pd (amp) j' y) i' p`
  Instantiating with the SWAPPED pair `(i' , j') := (j, i)` and `p := x` (using `hxmem : x ∈ S z`)
  reproduces J4-1031's SIX hypotheses EXACTLY, term for term:
    (2) with `y := x` ⟹ `hJetVi` (direction `j`, at `x`);   (3) ⟹ `hJetVj` (direction `i`, `∀ y ∈ S z`);
    (4) ⟹ `hJetQ` (differentiates the direction-`i` jet along `j` at `x`);
    (5) ⟹ `hAmpj1`;   (6) ⟹ `hAmpi1`;   (7) ⟹ `hAmp2`.
  `(1)` also supplies `hSopen` (via `z ∈ S z` from `uniformFlowExp_zero`, unconditionally for `z ∈ K`).

  ── THE UPSHOT.  `GeneralBaseJetsMixed` (J4-1030) turns out to be REDUNDANT for this particular
  composition — the piece that actually closes J4-1031's jet-bundle antecedent at the concrete gate was
  ALREADY BANKED (J4-237, before this whole `nb`-chain dispatch sequence even started), just never
  wired to the NEWER `HCompNearCarry*` consumer.  This file performs that wiring, producing a THEOREM
  whose remaining hypotheses are ONLY: the concrete-gate radius bookkeeping (`ha, hab, hbc, hcδ`), the
  standard metric-regularity carries (`hg, hgpos, hu`), `hxint` (field point in `interior K`), the
  literal `hτ` and `hd` (differentiability of `witnessFieldDeriv`, UNTOUCHED — a separate, pre-existing
  antecedent of J4-1029/1031 this dispatch does not attempt), and — crucially — `hxmem : ∀ z ∈ K, x ∈
  S z`.  `hxmem` is exactly the "chart-coverage" geometric fact cp985 flagged as the true remaining
  blocker (reachability of ONE fixed field point `x` from EVERY base point `z ∈ K`'s own chart, within
  radius `c`) — it is NOT discharged here, and NOT trivial (it is a genuine covering/surjectivity claim
  about the flow map, the target of cp985's `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`
  diagnosis). Consulted gpt-5.6-sol (high) BEFORE writing Lean: confirmed the swapped-index composition
  is sound, term-for-term, no Mathlib pitfall, and that `hxmem`/`hd` are the correct, honest, remaining
  residue (not further reducible by this composition).

  `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd
import QIQTH.Field2NbhdReshape
import QIQTH.ExpMap

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryJetBundleConcreteGateDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `kPrime_baseField_CoV_of_jetBundle_gateRestricted_concreteGate`.**  J4-1031's jet-bundle
    antecedent (`hJetVi/hJetVj/hJetQ/hAmpj1/hAmpi1/hAmp2`) and `hSopen` are FULLY DISCHARGED, at the
    concrete flow-ball gate `S z = uniformFlowExp z '' Metric.ball 0 c`, by
    `Field2NbhdReshape.hcarField2_hgate_concrete` called with the index pair SWAPPED to `(j, i)`.  The
    ONLY remaining hypotheses (beyond radius/metric-regularity bookkeeping) are `hxint`, `hxmem` (the
    genuine chart-coverage fact — reachability of `x` from every `z ∈ K`'s gate, STILL OPEN), `hτ`, and
    `hd` (untouched, pre-existing). Concludes the SAME literal CoV identity as J4-1029/J4-1031 (`PI`,
    `PJ`, `Q`, `S''`, `V` now existentially delivered). NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_gateRestricted_concreteGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i j : Fin n) (t s : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∀ {x : Point n}, x ∈ interior K →
    ∀ (hxmem : ∀ z ∈ K, x ∈ S z) (hτ : 0 < t - s)
      (hd : ∀ z ∈ K, DifferentiableAt ℝ
          (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x),
    ∃ (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
      (S'' : Set (Point n)) (V : Point n → Point n),
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
  obtain ⟨δ₀, hδ₀, hspec⟩ :=
    QIQTH.Field2NbhdReshape.hcarField2_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq x hxint hxmem hτ hd
  obtain ⟨PI_c, PJ_c, Q_c, hbig⟩ := hspec c hbc hcδ S hSeq j i
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hSopen : ∀ z ∈ K, IsOpen (S z) := by
    intro z hz
    have hzS : z ∈ S z := by
      rw [hSeq]
      exact ⟨0, Metric.mem_ball_self hc0, QIQTH.ExpMap.uniformFlowExp_zero g gi hC hK z hz⟩
    exact (hbig (t - s, z, z) hz hτ hzS).1
  have hJetVi : ∀ z ∈ K, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k)
      (PI_c z x k) (x j) := by
    intro z hz k
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.1 x (hxmem z hz) k
  have hJetVj : ∀ z ∈ K, ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k)
      (PJ_c z y k) (y i) := by
    intro z hz y hy k
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.2.1 y hy k
  set Qf : Point n → Fin n → ℝ := fun z k => Q_c z x k with hQfdef
  have hJetQ : ∀ z ∈ K, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ_c z (Function.update x j σ) k) (Qf z k) (x j) := by
    intro z hz k
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.2.2.1 k
  have hAmpj1 : ∀ z ∈ K, ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y := by
    intro z hz y hy
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.2.2.2.1 y hy
  have hAmpi1 : ∀ z ∈ K, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x := by
    intro z hz
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.2.2.2.2.1
  have hAmp2 : ∀ z ∈ K, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x := by
    intro z hz
    exact (hbig (t - s, x, z) hz hτ (hxmem z hz)).2.2.2.2.2.2
  obtain ⟨S'', V, hS''open, hxS'', hS''subK, hCoV⟩ :=
    QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd.kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd
      g gi hC hK S a b i j t s hxint PI_c PJ_c Qf hSopen hxmem hτ hd
      hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2
  exact ⟨PI_c, PJ_c, Qf, S'', V, hS''open, hxS'', hS''subK, hCoV⟩

end QIQTH.HCompNearCarryJetBundleConcreteGateDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryJetBundleConcreteGateDischarge
#print axioms kPrime_baseField_CoV_of_jetBundle_gateRestricted_concreteGate
end AxiomChecks
