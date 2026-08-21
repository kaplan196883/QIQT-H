/-
  MixedEnvelopeFullyInhabitedCurved — THE FULL JOINT INHABITATION of
  `MixedDirectionsFieldHessianEnvelope` (the FOURTH named hypothesis of the `hCConv` reduction) at the
  genuinely-curved witness `g^κ = curvedRNCMetric κ` (`κ < 0`, `1 ≤ n`, `K = {0}`), resolving the
  quantifier-order obstruction via the `(a,b)`-free `hFd` reach `HFdRequant.hFd_fully_closed_requant`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick jointly INHABITS
  ONE named input of the `hCConv` reduction (`MixedDirectionsFieldHessianEnvelope`) at the SPECIFIC
  degenerate witness `K = {0}` and at a gate produced by the genuine width-2 heat-kernel machinery.  It
  does NOT close `hCConv` (which additionally needs the general-`K` case and the OTHER census members of
  `fderivBulkInt_hasFDerivAt`), and does NOT bear on `hDuhamel`/`hDConv` (still the J3 opaque-chart
  Gauss-lemma bottleneck).  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RESOLUTION (the quantifier-order obstruction, now closed).

  The five envelope fields close individually at `K = {0}`: `hbint`/`hzmass`/`hkint`/`hLevi` hold for
  ANY gate parameters (null-support / tautological at the null singleton), while `hFd` needs
  `c < δ₀(a,b)`.  The obstruction was that the gate-parameter producer
  `gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` returns `∃ a b C c` with `c < ε`, choosing `a,b`
  ITSELF, so `ε := δ₀(a,b)` was circular.  `HFdRequant.hFd_fully_closed_requant` exposes an `(a,b)`-FREE
  reach `δ⋆`; prescribing `ε := δ⋆` into `curvedRNC_heatOp_dom_pkg_prescribed` (which is exactly that
  producer, assembled for `g^κ`) yields gate parameters `0 < a < b < c < δ⋆` at which `hFd` fires, AND
  which carry the genuine width-2 Gaussian heat-kernel domination.  All five fields then hold at the
  COMMON gate.

  ## HONEST CAVEAT (degenerate `K`).  As with J4-984/J4-985, at `K = {0}` the field-Hessian envelope
  `BF` is a.e. ZERO off the null singleton, so the joint inhabitation is null-support driven: `hbint`,
  `hzmass`, `hkint`'s measurability are integrals/measurability of a.e.-zero integrands.  The gate is
  genuinely curved and producer-compatible, but the curved geometry does no substantive analytic work in
  the estimates themselves.  This is a real closure of the named input AT THIS WITNESS, not a general-`K`
  result.  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.MixedEnvelopeFullyInhabitedCurved`).
    • `eqZero_ae_of_support_subset_singleton` — support in a null singleton ⟹ a.e. `0`.
    • `integrable_of_support_subset_singleton`, `aestronglyMeasurable_of_support_subset_singleton`.
    • `kPrime_eqZero_of_base_notMem_K` — `kPrime` vanishes off `K` (‖·‖ ≤ `BL·BF = 0`).
    • `mixedEnvelope_fully_inhabited_curved` — ★★★ the joint inhabitant with the width-2 domination.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HFdRequant
import QIQTH.MixedDirectionsFieldHessianEnvelope
import QIQTH.HZMassFullyClosedCurved
import QIQTH.HkintReducedToHbint
import QIQTH.CurvedA1ReachAlign

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.FderivBulkConcrete
open QIQTH.MixedDirFieldHessianEnvelope
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.MixedEnvelopeFullyInhabitedCurved

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — null-singleton support helpers.
    ############################################################################### -/

/-- A function whose support is contained in a singleton `{p}` is a.e. `0` w.r.t. an atomless measure. -/
theorem eqZero_ae_of_support_subset_singleton
    {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ] [Zero E]
    (f : α → E) (p : α) (hsupp : Function.support f ⊆ {p}) :
    f =ᵐ[μ] (fun _ => 0) := by
  have hnull : μ ({p} : Set α) = 0 := measure_singleton p
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  exact hsupp (by simpa [Function.mem_support] using hx)

/-- A real function supported in a null singleton is integrable. -/
theorem integrable_of_support_subset_singleton
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    (f : α → ℝ) (p : α) (hsupp : Function.support f ⊆ {p}) :
    Integrable f μ :=
  (integrable_zero α ℝ μ).congr (eqZero_ae_of_support_subset_singleton f p hsupp).symm

/-- A function supported in a null singleton, valued in a normed space, is a.e.-strongly-measurable. -/
theorem aestronglyMeasurable_of_support_subset_singleton
    {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NoAtoms μ]
    [TopologicalSpace E] [Zero E]
    (f : α → E) (p : α) (hsupp : Function.support f ⊆ {p}) :
    AEStronglyMeasurable f μ :=
  aestronglyMeasurable_const.congr (eqZero_ae_of_support_subset_singleton f p hsupp).symm

/-! ###############################################################################
    ### §2 — `kPrime` vanishes off `K` (so its support sits in the null singleton).
    ############################################################################### -/

/-- **`kPrime_eqZero_of_base_notMem_K`.**  For a base point `z ∉ K` the field-Hessian kernel `kPrime`
    vanishes: `‖kPrime … x z‖ ≤ |leviSeries …| · 0 = 0` (the field-Hessian `fderiv` is `0` off `K`), so
    `kPrime … x z = 0`.  This places `z ↦ kPrime … x z` in the null singleton support. -/
theorem kPrime_eqZero_of_base_notMem_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t s : ℝ) (x z : Point n) (hz : z ∉ K) :
    kPrime g gi hC hK S a b i t s x z = 0 := by
  have hF : ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖ ≤ 0 := by
    rw [QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
      g gi hC hK S a b i (t - s) z hz x, norm_zero]
  have hnorm := QIQTH.HkintReducedToHbint.kPrime_norm_le_product g gi hC hK S a b i t s x z
    (|leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|) 0 (le_refl _) hF
  rw [mul_zero] at hnorm
  exact norm_le_zero_iff.mp hnorm

/-! ###############################################################################
    ### §3 — ★★★ THE JOINT INHABITANT at the genuinely-curved `K = {0}` witness.
    ############################################################################### -/

/-- **★★★ `mixedEnvelope_fully_inhabited_curved`.**  THE FULL JOINT INHABITATION of
    `MixedDirectionsFieldHessianEnvelope` at the genuinely-curved witness `g^κ = curvedRNCMetric κ`
    (`κ < 0`, `1 ≤ n`, `K = {0}`), GIVEN only the mainline-standard carried geometric inputs
    {`hChr`, `hw`, `hu`} and a capped-window witness `hepspos : 0 < t − εₘ` (and any `T > 0`).

    The obstruction is resolved by prescribing the `(a,b)`-free `hFd` reach `δ⋆`
    (`HFdRequant.hFd_fully_closed_requant`) into `curvedRNC_heatOp_dom_pkg_prescribed`: this yields gate
    parameters `0 < a < b < c < δ⋆`, at which
      • the genuine width-2 Gaussian heat-kernel domination holds (`hdom`), AND
      • all five envelope fields hold at the COMMON flow-ball gate `S = φ_·'' ball 0 c`
        (`BL := |leviSeries …|`, `BF := ⨆ x ‖fderiv …‖`, envelope constant `0`).

    DEGENERATE-`K` CAVEAT (honest, cf. J4-984/985): at `K = {0}` the field-Hessian `BF` is a.e. `0` off
    the null singleton, so `hbint`/`hzmass`/`hkint` are null-support driven; the curved geometry does no
    substantive analytic work in the estimates.  This is a genuine closure of the named input AT THIS
    witness, not a general-`K` result.  NON-VACUOUS: the width-2 domination conjunct and the flow-ball
    gate are the genuine curved heat-parametrix objects; none of the antecedents is unsatisfiable.
    NOT `a₁ = R/6`. -/
theorem mixedEnvelope_fully_inhabited_curved (κ : ℝ) (hκ : κ < 0) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (i : Fin n) (t : ℝ) (m : ℕ) (hepspos : 0 < t - epsSeq m) (T : ℝ) (hT : 0 < T) :
    ∃ a b c Cdom : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 ≤ Cdom ∧
      -- the genuine width-2 heat-kernel domination at the produced curved gate:
      (∀ (t' : ℝ), ∀ (τ : ℝ), ∀ (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
                (QIQTH.A1R6CoreAtGate.constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b) τ p q|
          ≤ (Cdom * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) ∧
      -- the FULL joint inhabitation of the fourth named `hCConv` hypothesis at the same gate:
      ∃ BL BF : ℝ → Point n → ℝ,
        MixedDirectionsFieldHessianEnvelope (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
          (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
            '' Metric.ball (0 : Point n) c) a b i t m 0 BL BF := by
  classical
  have hn0 : 0 < n := by omega
  haveI : Inhabited (Fin n) := ⟨⟨0, hn0⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  -- the metric premises for `g^κ`.
  have hg : ∀ (a b : Fin n), ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgpos : ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric κ v) :=
    fun v => curvedRNCMetric_det_pos κ hκ.le v
  -- 1. the `(a,b)`-free `hFd` reach `δ⋆`.
  obtain ⟨δstar, hδstar, hFdreq⟩ :=
    QIQTH.HFdRequant.hFd_fully_closed_requant (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) hg hgpos hu
  -- 2. gate parameters at radius `c < δ⋆` from the width-2 producer.
  obtain ⟨a, b, Cdom, c, ha, hab, hCdom, hbc, hcδstar, hdom, -⟩ :=
    QIQTH.CurvedA1ReachAlign.curvedRNC_heatOp_dom_pkg_prescribed κ hκ hChr hw T δstar hδstar
  -- the common flow-ball gate.
  set S : Point n → Set (Point n) :=
    (fun z => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) z
      '' Metric.ball (0 : Point n) c) with hSdef
  -- the explicit Levi magnitude and field-Hessian envelopes.
  set BF : ℝ → Point n → ℝ := fun s z =>
    ⨆ x : Point n, ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (t - s) y z) x‖
    with hBFdef
  set BL : ℝ → Point n → ℝ := fun s z =>
    |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)) s z 0|
    with hBLdef
  refine ⟨a, b, c, Cdom, ha, hab, hbc, hCdom, hdom, BL, BF, ?_⟩
  -- ── the five fields ──────────────────────────────────────────────────────────────────────────
  -- hLevi : tautological (BL is the |leviSeries| itself).
  have hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b)) s z 0|
          ≤ BL s z :=
    ae_of_all volume (fun s _ => ae_of_all volume (fun z => le_refl _))
  -- hFd : the field-Hessian `⨆`-bound at the produced gate (`c < δ⋆`).
  have hFd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (t - s) y z) x‖
          ≤ BF s z :=
    hFdreq a b ha hab i t m c hbc hcδstar S hSdef
  -- hbint : the product dominator `BL·BF` is supported in the null singleton `{0}`, hence integrable.
  have hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z * BF s z) volume := by
    refine ae_of_all volume (fun s _ => ?_)
    have hsupp := productEnvelope_support_subset_K (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i (t - s) BL s
    have hsupp' : Function.support (fun z => BL s z * BF s z) ⊆ ({(0 : Point n)} : Set (Point n)) := by
      simpa [hBFdef] using hsupp
    exact integrable_of_support_subset_singleton (μ := (volume : Measure (Point n)))
      (fun z => BL s z * BF s z) (0 : Point n) hsupp'
  -- hmeas : `kPrime` is a.e.-zero (null-singleton support), hence a.e.-strongly-measurable.
  have hmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x : Point n,
        AEStronglyMeasurable (fun z => kPrime (curvedRNCMetric κ) (curvedRNCInv κ) hChr
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z)
          volume := by
    refine ae_of_all volume (fun s _ x => ?_)
    refine aestronglyMeasurable_of_support_subset_singleton (μ := (volume : Measure (Point n)))
      (fun z => kPrime (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z)
      (0 : Point n) ?_
    intro z hz
    by_contra hzK
    have hz0 : kPrime (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z = 0 :=
      kPrime_eqZero_of_base_notMem_K (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z
        (by simpa [Set.mem_singleton_iff] using hzK)
    exact hz (by simpa [Function.mem_support] using hz0)
  -- hkint : downstream of `hbint` (J4-875) with the null-support measurability.
  have hkint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ x : Point n, Integrable (fun z => kPrime (curvedRNCMetric κ) (curvedRNCInv κ) hChr
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t s x z)
        volume :=
    QIQTH.HkintReducedToHbint.hkint_reduces_to_hbint_concrete (curvedRNCMetric κ) (curvedRNCInv κ)
      hChr (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) S a b i t m BL BF
      hbint hmeas hLevi hFd
  -- hzmass : the null-support `z`-mass bound `∫z BL·BF = 0 ≤ 0·(t−s)⁻¹` (J4-985, envelope constant `0`).
  have hzmass : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      (∫ z, BL s z * BF s z) ≤ (0 : ℝ) * (t - s)⁻¹ :=
    QIQTH.HZMassFullyClosedCurved.hzmass_fully_closed_curved κ hκ hn hChr i t m 0 (le_refl 0)
      hepspos a b c BL
  exact ⟨hLevi, hFd, hkint, hbint, hzmass⟩

end QIQTH.MixedEnvelopeFullyInhabitedCurved

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedEnvelopeFullyInhabitedCurved
#print axioms eqZero_ae_of_support_subset_singleton
#print axioms integrable_of_support_subset_singleton
#print axioms aestronglyMeasurable_of_support_subset_singleton
#print axioms kPrime_eqZero_of_base_notMem_K
#print axioms mixedEnvelope_fully_inhabited_curved
end AxiomChecks
