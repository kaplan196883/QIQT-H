/-
  HCompNearCarryJetBundleLocalCoverageDischarge — J4-1044: composes the `K ∩ U`-shrunk wrapper
  (J4-1043, `HCompNearCarryKPrimeGateRestrictedCoVNbhdU`) with the LOCAL sharp-reach coverage fact
  (J4-1042, `HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball`) to produce, for the FIRST
  time in this chain, a theorem in which `hxmem` is **NOT an external hypothesis at all** — it is
  DERIVED, for `U := Metric.ball x R` (the sharp-reach radius), from already-banked analytic facts
  alone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES.  Three already-banked pieces are composed for the first time:
    (1) J4-1043 (`HCompNearCarryKPrimeGateRestrictedCoVNbhdU`) — the wrapper theorem whose jet/amp/
        coverage hypotheses are quantified over `z ∈ K ∩ U` for an EXPLICIT open `U ∋ x`, not all `K`.
    (2) J4-1032's brick `Field2NbhdReshape.hcarField2_hgate_concrete` (ALREADY BANKED) — discharges the
        six jet/amp hypotheses AND `hSopen`, for EVERY `z` at which `x ∈ S z` already holds (index pair
        swapped `(j, i)`, exactly as in J4-1032).
    (3) J4-1042 (`HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball`) — supplies
        `x ∈ S z` (`hxmem`) for every `z ∈ K ∩ Metric.ball x R`, `R := (1 - C_L·c)·(3·c/4) > 0`, WITHOUT
        any hypothesis beyond `hC`/`IsCompact K` (no re-derivation of `K`, no circularity).
  Setting `U := Metric.ball x R` in (1) and discharging its `hxmem` via (3) closes the loop: `hxmem` no
  longer appears as a hypothesis of the composed theorem below — the ONLY remaining hypotheses are the
  concrete-gate radius/metric-regularity bookkeeping (as in J4-1032), `hxint`, `hτ`, and the untouched,
  pre-existing `hd` (differentiability of `witnessFieldDeriv`, restricted to `z ∈ K ∩ Metric.ball x R`
  rather than all of `K` — itself now a STRICTLY SMALLER obligation than J4-1032's).

  ── WHAT THIS DOES **NOT** DO.  It does NOT discharge `hd` (still an open, pre-existing antecedent,
  now on a smaller domain). It does NOT discharge `hxint` (still assumed). It does NOT claim r6 or `nb`
  is closed: the CoV domain `S''` this theorem existentially delivers is `S'' ⊆ K ∩ Metric.ball x R`,
  smaller yet again than J4-1031/1032's `S'' ⊆ K` — the theorem's SCOPE is narrower, but WITHIN that
  scope, `hxmem` (the "genuine chart-coverage fact" J4-1032 flagged as the true remaining blocker) is
  GENUINELY GONE as a free hypothesis for this shrunk domain. `Bfac`'s other 3 summands and `fb` remain
  untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT
  `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU
import QIQTH.HxmemLocalSharpReachCoverage
import QIQTH.Field2NbhdReshape
import QIQTH.ExpMap

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.ExpMap QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryJetBundleLocalCoverageDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★★ `kPrime_baseField_CoV_of_jetBundle_localCoverage`.**  The composed theorem: `hxmem` is
    **DERIVED** (via J4-1042's `uniformFlowExp_local_coverage_ball`) for `z` ranging over
    `K ∩ Metric.ball x R`, `R := (1 - C_L·c)·(3·c/4) > 0`, rather than assumed. The six jet/amp
    hypotheses and `hSopen` are discharged (via J4-1032's already-banked `hcarField2_hgate_concrete`,
    index pair swapped `(j, i)`) for exactly that same shrunk domain, then fed into J4-1043's `K ∩ U`
    wrapper with `U := Metric.ball x R`. The ONLY hypotheses beyond radius/metric-regularity bookkeeping
    are `hxint`, `hτ`, and `hd` (untouched, pre-existing, now only required on `K ∩ Metric.ball x R`).
    NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_localCoverage
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (i j : Fin n) (t s : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∃ ρ₀ > (0 : ℝ), ∃ C_L : ℝ, 0 ≤ C_L ∧
    ∀ c : ℝ, b < c → c < δ₀ → 0 < c → c ≤ ρ₀ → C_L * c < 1 →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
    ∀ {x : Point n}, x ∈ interior K →
    ∃ R > (0 : ℝ),
    ∀ (hτ : 0 < t - s)
      (hd : ∀ z ∈ K ∩ Metric.ball x R, DifferentiableAt ℝ
          (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x),
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
  obtain ⟨δ₀, hδ₀, hspec⟩ :=
    QIQTH.Field2NbhdReshape.hcarField2_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hloccov⟩ :=
    QIQTH.HxmemLocalSharpReachCoverage.uniformFlowExp_local_coverage_ball g gi hC hK
  refine ⟨δ₀, hδ₀, ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro c hbc hcδ hc0 hcρ hCLc S hSeq x hxint
  obtain ⟨PI_c, PJ_c, Q_c, hbig⟩ := hspec c hbc hcδ S hSeq j i
  -- The local coverage fact, specialized at this fixed `x`: coverage on `K ∩ Metric.ball x R`.
  obtain ⟨R, hR, hcov⟩ := hloccov c hc0 hcρ hCLc x
  refine ⟨R, hR, ?_⟩
  intro hτ hd
  set U : Set (Point n) := Metric.ball x R with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hxU : x ∈ U := Metric.mem_ball_self hR
  -- `hxmem`, restricted to `K ∩ U`, is DERIVED (not assumed) from the local coverage fact.
  have hxmem : ∀ z ∈ K ∩ U, x ∈ S z := by
    intro z hz
    rw [hSeq]
    exact hcov z hz.1 hz.2
  have hSopen : ∀ z ∈ K ∩ U, IsOpen (S z) := by
    intro z hz
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).1
  have hJetVi : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k)
      (PI_c z x k) (x j) := by
    intro z hz k
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.1 x (hxmem z hz) k
  have hJetVj : ∀ z ∈ K ∩ U, ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k)
      (PJ_c z y k) (y i) := by
    intro z hz y hy k
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.1 y hy k
  set Qf : Point n → Fin n → ℝ := fun z k => Q_c z x k with hQfdef
  have hJetQ : ∀ z ∈ K ∩ U, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ_c z (Function.update x j σ) k) (Qf z k) (x j) := by
    intro z hz k
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.1 k
  have hAmpj1 : ∀ z ∈ K ∩ U, ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y := by
    intro z hz y hy
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.1 y hy
  have hAmpi1 : ∀ z ∈ K ∩ U, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x := by
    intro z hz
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.2.1
  have hAmp2 : ∀ z ∈ K ∩ U, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x := by
    intro z hz
    exact (hbig (t - s, x, z) hz.1 hτ (hxmem z hz)).2.2.2.2.2.2
  have hd' : ∀ z ∈ K ∩ U, DifferentiableAt ℝ
      (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x := hd
  obtain ⟨S'', V, hS''open, hxS'', hS''subKU, hCoV⟩ :=
    QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhdU.kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhdU
      g gi hC hK S a b i j t s hxint U hUopen hxU PI_c PJ_c Qf hSopen hxmem hτ hd'
      hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2
  exact ⟨PI_c, PJ_c, Qf, S'', V, hS''open, hxS'', hS''subKU, hCoV⟩

end QIQTH.HCompNearCarryJetBundleLocalCoverageDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryJetBundleLocalCoverageDischarge
#print axioms kPrime_baseField_CoV_of_jetBundle_localCoverage
end AxiomChecks
