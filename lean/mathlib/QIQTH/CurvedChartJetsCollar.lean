/-
  CurvedChartJetsCollar — J4-557: collar-localize the chart-jet residue's first-jet member.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## THE TRACE (what this brick decides).
  J4-556 flagged `hGlobalJet` — the GLOBAL `∀ x` first `i`-jet of `uniformInverseChart` — as the sole
  surviving substrate terminal of the curved chart-jet residue `CurvedChartJets.curved_hjets_residual`,
  because the concrete chart's spec exposes `ContDiffAt ℝ 2` only NEAR IMAGE POINTS, not the ambient
  `∀ x`.  This brick TRACES the amplitude consumers of that first-jet field and finds it is FALSE
  GENERALITY:

    `AmplitudeDataOnCollar.hD2HexpandOn_concrete`  (the collar D2 consumer of `hjets`)
      → `AmplitudeDataOnCollar.witnessSecondXDeriv_expand_bridge_rho`
        → `ChartJetHessian.gaussComp_amp_center_decomp`  (the TERMINAL Leibniz consumer)
          → `ChartJetHessian.gaussComp_amp_pd_pd` / `gaussComp_pd_pd`.

  In `gaussComp_pd_pd` / `gaussComp_amp_pd_pd` the ambient `∀ x` first jet `hV1` is used at ambient
  generality in EXACTLY ONE place: the `funext` step `hinner`/`hGinner` that expresses the inner first
  partial `∂ᵢ(gaussDdim ∘ V)` as a GLOBAL function equality before the outer `∂ᵢ` differentiates it.
  Every OTHER use of `hV1` is at the single centre point `x₀ = 0`.  But `pd = deriv` is a LOCAL (germ)
  operator: a `funext` (global equality) is strictly stronger than the `=ᶠ[𝓝 0]` (near-centre equality)
  the outer partial actually reads.  The near-centre first jet is BANKED
  (`GeneralBaseJets.chartField_firstJet_nhds_of_contDiffAt`, from the honest `ContDiffAt ℝ 2 (V_z) 0`
  carry).  So the ambient `∀ x` demand is a proof-convenience over-reach, not a genuine requirement.

  ## WHAT LANDS HERE (all satisfiable, none the conclusion, no vacuity).
    • `gaussComp_pd_pd_nhds` / `gaussComp_amp_pd_pd_nhds` / `gaussComp_amp_center_decomp_nhds`
        — ★★ the TERMINAL Leibniz consumer re-proved from the `=ᶠ[𝓝 0]` (near-centre) first jet instead
        of the ambient `∀ x` jet.  The ONLY change from the banked proofs is that the `funext hinner`
        step becomes a `pd_congr_of_eventuallyEq` on the `=ᶠ[𝓝 0]` inner-partial equality; everything
        else is verbatim the banked centre computation.  This is the SOUNDNESS PROOF that the collar /
        near-centre first jet genuinely suffices for the terminal consumer.
    • `witnessSecondXDeriv_expand_bridge_rho_nhds` / `hD2HexpandOn_concrete_nhds`
        — ★ the collar D2 bridge (the exact `hD2Hexpand` field of the collar amplitude bundle) produced
        from the near-centre first jet — i.e. the WHOLE consumer of `hGlobalJet` re-plumbed onto the
        BANKED jet.  `hGlobalJet` is dropped.
    • `curved_collarFirstJet_banked`
        — the near-centre first jet for the concrete CURVED chart `g^K = curvedRNCMetric κ` IS banked,
        via `chartField_firstJet_nhds_of_contDiffAt` from `ContDiffAt ℝ 2 (W z) 0` — a genuine
        geometric fact for `g^K` (κ < 0, Ric ≠ 0), NOT a re-labelled `hGlobalJet`.
    • `curved_hjets_residual_collar` / `_intro`
        — the REFACTORED residue ledger carrying the BANKED near-centre first jet `hCollarJet` in place
        of the ambient `hGlobalJet`.  `hGlobalJet` is REMOVED from the residue.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Dropping `hGlobalJet` removes ONE substrate terminal from the
  chart-jet residue — a genuine advance — but does NOT make a₁ = R/6 unconditional: `hsrc`,
  `hOffCollarTail`, the general-base centre identities, the convergence trio and the measurability
  census all remain.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedChartJets
import QIQTH.D2HExpandRecon
import QIQTH.GeneralBaseJets

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar
open QIQTH.AmpGeometryBundle QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — a germ transfer for `PdiffAt` at the centre.
    ############################################################################### -/

/-- **`pdiffAt_of_eventuallyEq`.**  Coordinate-`i` differentiability at the centre `0` depends only on
    the germ: if `f =ᶠ[𝓝 0] h` and `h` is `PdiffAt` at `0`, so is `f`.  Pull the eventual equality back
    along the continuous coordinate line `t ↦ update 0 i t` and apply `DifferentiableAt.congr_of_
    eventuallyEq`.  Elementary, geometry-free.  ⚠ NOT `a₁ = R/6`. -/
theorem pdiffAt_of_eventuallyEq {f h : Point n → ℝ} {i : Fin n}
    (hfh : f =ᶠ[𝓝 (0 : Point n)] h) (hh : PdiffAt h i (0 : Point n)) :
    PdiffAt f i (0 : Point n) := by
  have htend : Filter.Tendsto (fun t : ℝ => Function.update (0 : Point n) i t)
      (𝓝 ((0 : Point n) i)) (𝓝 (0 : Point n)) := by
    have h1 : ContinuousAt (Function.update (0 : Point n) i) ((0 : Point n) i) :=
      (hasDerivAt_update (0 : Point n) i ((0 : Point n) i)).continuousAt
    have h2 : (Function.update (0 : Point n) i) ((0 : Point n) i) = (0 : Point n) :=
      Function.update_eq_self i (0 : Point n)
    rw [ContinuousAt, h2] at h1; exact h1
  have hline : (fun t : ℝ => f (Function.update (0 : Point n) i t))
      =ᶠ[𝓝 ((0 : Point n) i)] (fun t : ℝ => h (Function.update (0 : Point n) i t)) :=
    htend.eventually hfh
  exact hh.congr_of_eventuallyEq hline

/-! ###############################################################################
    ### §1 — ★★ the terminal Leibniz consumer, re-proved from the near-centre first jet.
    ############################################################################### -/

/-- **★★ `gaussComp_pd_pd_nhds`.**  The composed-Gaussian second coordinate partial at the centre,
    from the NEAR-CENTRE first jet `hV1 : ∀ᶠ x in 𝓝 0, …` (instead of the ambient `∀ x` form of
    `gaussComp_pd_pd`).  The inner-partial normal form is only needed as a `=ᶠ[𝓝 0]` equality (the
    outer `pd` reads a germ), so `funext` is replaced by `pd_congr_of_eventuallyEq`; the centre
    computation is verbatim.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_nhds (V : Point n → Point n) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (hV1 : ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) i y) i (0 : Point n)
      = gaussDdim τ (V 0)
        * ((∑ k, V 0 k * P 0 k) ^ 2 / (4 * τ ^ 2)
            - ((∑ k, P 0 k ^ 2) + (∑ k, V 0 k * Q k)) / (2 * τ)) := by
  have hV10 : ∀ k, HasDerivAt
      (fun s : ℝ => V (Function.update (0 : Point n) i s) k) (P 0 k) ((0 : Point n) i) :=
    hV1.self_of_nhds
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      =ᶠ[𝓝 (0 : Point n)] (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) := by
    filter_upwards [hV1] with y hy
    exact gaussComp_pd V (P y) τ hτ i y hy
  rw [QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq _ _ i (0 : Point n) hinner]
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) i (0 : Point n) :=
    (gaussComp_hasDerivAt_line V (P 0) τ hτ i (0 : Point n) hV10).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ
      (fun s : ℝ => V (Function.update (0 : Point n) i s) k) ((0 : Point n) i) :=
    fun k => (hV10 k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) ((0 : Point n) i) :=
    fun k => (hP1 k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) i (0 : Point n) := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update (0 : Point n) i s) k
          * P (Function.update (0 : Point n) i s) k) ((0 : Point n) i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i (0 : Point n) := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update (0 : Point n) i s) k
          * P (Function.update (0 : Point n) i s) k) / (2 * τ)) ((0 : Point n) i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  rw [pd_mul (fun y => gaussDdim τ (V y)) (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i
        (0 : Point n) hGf hhf,
      gaussComp_pd V (P 0) τ hτ i (0 : Point n) hV10,
      pd_neg_div_const (fun y => ∑ k, V y k * P y k) (2 * τ) i (0 : Point n) hsumPdiff]
  have hpdsum : pd (fun y => ∑ k, V y k * P y k) i (0 : Point n)
      = ∑ k, (P 0 k * P 0 k + V 0 k * Q k) := by
    rw [pd_sum (Finset.univ) (fun k y => V y k * P y k) i (0 : Point n)
        (fun k _ => (hdV k).mul (hdP k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pd_mul (fun y => V y k) (fun y => P y k) i (0 : Point n) (hdV k) (hdP k)]
    have h1 : pd (fun y => V y k) i (0 : Point n) = P 0 k := by
      simp only [pd]; exact (hV10 k).deriv
    have h2 : pd (fun y => P y k) i (0 : Point n) = Q k := by
      simp only [pd]; exact (hP1 k).deriv
    rw [h1, h2]
  rw [hpdsum, Finset.sum_add_distrib]
  have hsq : (∑ k, P 0 k * P 0 k) = ∑ k, P 0 k ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsq]
  have hτ' : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-- **★★ `gaussComp_amp_pd_pd_nhds`.**  The amplitude-weighted composed-Gaussian second partial at the
    centre, from the NEAR-CENTRE first jet.  The two `∀ x` funext steps of `gaussComp_amp_pd_pd` (the
    inner-Gaussian partial and the `A`-Leibniz split) become `=ᶠ[𝓝 0]` equalities; the germ transfer
    `pdiffAt_of_eventuallyEq` supplies the outer `PdiffAt` of the inner partial; the centre computation
    is verbatim.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussComp_amp_pd_pd_nhds (V : Point n → Point n) (A : Point n → ℝ)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (hV1 : ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y) i (0 : Point n)
      = gaussDdim τ (V 0)
          * ((∑ k, V 0 k * P 0 k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P 0 k ^ 2) + (∑ k, V 0 k * Q k)) / (2 * τ)) * A 0
        + 2 * (gaussDdim τ (V 0) * (-(∑ k, V 0 k * P 0 k) / (2 * τ))) * pd A i 0
        + gaussDdim τ (V 0) * pd (fun y => pd A i y) i 0 := by
  have hV10 : ∀ k, HasDerivAt
      (fun s : ℝ => V (Function.update (0 : Point n) i s) k) (P 0 k) ((0 : Point n) i) :=
    hV1.self_of_nhds
  have hGf : PdiffAt (fun z => gaussDdim τ (V z)) i (0 : Point n) :=
    (gaussComp_hasDerivAt_line V (P 0) τ hτ i (0 : Point n) hV10).differentiableAt
  have hGinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      =ᶠ[𝓝 (0 : Point n)] (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) := by
    filter_upwards [hV1] with y hy
    exact gaussComp_pd V (P y) τ hτ i y hy
  have hGfP_ev : ∀ᶠ y in 𝓝 (0 : Point n), PdiffAt (fun z => gaussDdim τ (V z)) i y := by
    filter_upwards [hV1] with y hy
    exact (gaussComp_hasDerivAt_line V (P y) τ hτ i y hy).differentiableAt
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i (0 : Point n) := by
    have hdV : ∀ k, DifferentiableAt ℝ
        (fun s : ℝ => V (Function.update (0 : Point n) i s) k) ((0 : Point n) i) :=
      fun k => (hV10 k).differentiableAt
    have hdP : ∀ k, DifferentiableAt ℝ
        (fun s : ℝ => P (Function.update (0 : Point n) i s) k) ((0 : Point n) i) :=
      fun k => (hP1 k).differentiableAt
    have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) i (0 : Point n) := by
      show DifferentiableAt ℝ
          (fun s : ℝ => ∑ k, V (Function.update (0 : Point n) i s) k
            * P (Function.update (0 : Point n) i s) k) ((0 : Point n) i)
      exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update (0 : Point n) i s) k
          * P (Function.update (0 : Point n) i s) k) / (2 * τ)) ((0 : Point n) i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  have hpdGf_pdiff : PdiffAt (fun y => pd (fun z => gaussDdim τ (V z)) i y) i (0 : Point n) :=
    pdiffAt_of_eventuallyEq hGinner (hGf.mul hhf)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y)
      =ᶠ[𝓝 (0 : Point n)] (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y
          + gaussDdim τ (V y) * pd A i y) := by
    filter_upwards [hGfP_ev] with y hy
    exact pd_mul (fun z => gaussDdim τ (V z)) A i y hy (hA1 y)
  rw [QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq _ _ i (0 : Point n) hinner]
  rw [pd_add (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y)
        (fun y => gaussDdim τ (V y) * pd A i y) i (0 : Point n)
        (hpdGf_pdiff.mul (hA1 (0 : Point n))) (hGf.mul hA2),
      pd_mul (fun y => pd (fun z => gaussDdim τ (V z)) i y) A i (0 : Point n) hpdGf_pdiff
        (hA1 (0 : Point n)),
      pd_mul (fun y => gaussDdim τ (V y)) (fun y => pd A i y) i (0 : Point n) hGf hA2]
  rw [gaussComp_pd_pd_nhds V P Q τ hτ i hV1 hP1,
      gaussComp_pd V (P 0) τ hτ i (0 : Point n) hV10]
  ring

/-- **★★ `gaussComp_amp_center_decomp_nhds`.**  The centre three-piece decomposition (the exact form
    consumed by the D2 bridge) from the NEAR-CENTRE first jet — a pure regrouping of
    `gaussComp_amp_pd_pd_nhds`.  This is the terminal Leibniz consumer of the chart first jet, now shown
    to accept the BANKED `=ᶠ[𝓝 0]` jet in place of the ambient `∀ x` jet.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussComp_amp_center_decomp_nhds (V : Point n → Point n) (A : Point n → ℝ)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (hV1 : ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y) i (0 : Point n)
      = gaussDdim τ (V 0)
          * ((∑ k, V 0 k * P 0 k) ^ 2 / (4 * τ ^ 2) - (∑ k, P 0 k ^ 2) / (2 * τ)) * A 0
      + gaussDdim τ (V 0) * (-(∑ k, V 0 k * Q k) / (2 * τ)) * A 0
      + (2 * (gaussDdim τ (V 0) * (-(∑ k, V 0 k * P 0 k) / (2 * τ))) * pd A i 0
          + gaussDdim τ (V 0) * pd (fun y => pd A i y) i 0) := by
  rw [gaussComp_amp_pd_pd_nhds V A P Q τ hτ i hV1 hP1 hA1 hA2]
  ring

/-! ###############################################################################
    ### §2 — ★ the collar D2 bridge, produced from the near-centre first jet.
    ############################################################################### -/

/-- **★ `witnessSecondXDeriv_expand_bridge_rho_nhds`.**  The corrected (ρ-scaled) D2 bridge — the exact
    `hD2Hexpand` shape of the collar amplitude bundle — produced from the NEAR-CENTRE first jet.
    Verbatim `witnessSecondXDeriv_expand_bridge_rho` but with the ambient `∀ x` first jet replaced by
    the `=ᶠ[𝓝 0]` form, discharged through `gaussComp_amp_center_decomp_nhds`.  This re-plumbs the WHOLE
    consumer of `hGlobalJet` onto the banked near-centre jet.  ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_expand_bridge_rho_nhds
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (V : Point n → Point n) (A : Point n → ℝ) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (ρval : ℝ)
    (hrep : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
              =ᶠ[nhds (0 : Point n)] (fun x' => gaussDdim τ (V x') * A x'))
    (hV1 : ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n))
    (hV0ρ : gaussDdim τ (V 0) = ρval * gaussDdim τ z)
    (hVP : ∑ k, V 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, V 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (ρval * A 0)
        + z i / (2 * τ) * gaussDdim τ z * (ρval * (-2 * pd A i 0))
        + gaussDdim τ z * (ρval * pd (fun y => pd A i y) i 0) := by
  unfold witnessSecondXDeriv
  rw [QIQTH.D2HExpandRecon.pd_pd_congr_of_eventuallyEq
        (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
        (fun x' => gaussDdim τ (V x') * A x') i (0 : Point n) hrep,
      gaussComp_amp_center_decomp_nhds V A P Q τ hτ i hV1 hP1 hA1 hA2,
      hV0ρ, hVP, hPsq, hVQ]
  have hτ' : τ ≠ 0 := hτ.ne'
  have h2τ : (2 : ℝ) * τ ≠ 0 := by positivity
  have h4τ : (4 : ℝ) * τ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **★ `hD2HexpandOn_concrete_nhds`.**  The collar D2 bridge at the TRUE chart, produced from the
    NEAR-CENTRE first jet `hV1nhds` (banked) instead of the ambient `∀ x` jet.  Identical conclusion to
    `hD2HexpandOn_concrete`; the ambient first-jet demand is DROPPED.  ⚠ NOT `a₁ = R/6`. -/
theorem hD2HexpandOn_concrete_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hV1 : ∀ᶠ x in 𝓝 (0 : Point n), ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z
            * (rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0)
        + z i / (2 * τ) * gaussDdim τ z
            * (rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0))
        + gaussDdim τ z
            * (rhoRatio g gi hC hK τ z
                * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) :=
  witnessSecondXDeriv_expand_bridge_rho_nhds g gi hC hK S a b i τ hτ z
    (uniformInverseChart g gi hC hK z) (chartAmp g gi hC hK a b τ z) P Q
    (rhoRatio g gi hC hK τ z)
    (vanVleckGatedWitness_germ_factor g gi hC hK S a b τ z hz hSopen h0)
    hV1 hP1 hA1 hA2
    (gauss_ratio_rho g gi hC hK τ hτ z)
    hVP hPsq hVQ

end QIQTH.HeatResidualBound

/-! ###############################################################################
    ### §3 — the CURVED collar first jet is banked, and the refactored residue ledger.
    ############################################################################### -/

namespace QIQTH.CurvedChartJets

open QIQTH.HeatResidualBound QIQTH.CurvedRNCGaussWitness
open QIQTH.CurvedRNCGaugeBundle

variable {n : ℕ}

/-- **★ `curved_collarFirstJet_banked`.**  For the concrete genuinely-curved chart
    `W z = uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) …`, the NEAR-CENTRE first jet — the
    exact `=ᶠ[𝓝 0]` form that `hD2HexpandOn_concrete_nhds` consumes — is BANKED from the honest
    `ContDiffAt ℝ 2 (W z) 0` carry, via `chartField_firstJet_nhds_of_contDiffAt`.  This is a genuine
    geometric fact for `g^K` (κ < 0, Ric ≠ 0), NOT a re-labelled ambient `hGlobalJet`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem curved_collarFirstJet_banked (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2
      (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) (0 : Point n)) :
    ∀ᶠ x in 𝓝 (0 : Point n), ∀ k,
      HasDerivAt (fun s : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
        (Function.update x i s) k)
        (fderiv ℝ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z) x
          (Pi.single i (1 : ℝ)) k) (x i) :=
  chartField_firstJet_nhds_of_contDiffAt (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z i hreg

/-- **`curved_hjets_residual_collar`.**  The REFACTORED curved chart-jet residue ledger: the ambient
    `∀ x` first jet `hGlobalJet` of `curved_hjets_residual` is REPLACED by the BANKED near-centre first
    jet `hCollarJet` (`curved_collarFirstJet_banked`).  The three general-base centre identities are
    unchanged.  This drops `hGlobalJet` from the residue — the `∀ x` demand was false generality, as
    `gaussComp_amp_center_decomp_nhds` / `hD2HexpandOn_concrete_nhds` prove the terminal consumer accepts
    the near-centre jet.  ⚠ NOT `a₁ = R/6`; CONDITIONAL on exactly this (banked-first-jet) residue. -/
def curved_hjets_residual_collar (hCollarJet hCentreVP hCentrePsq hCentreVQ : Prop) : Prop :=
  hCollarJet ∧ hCentreVP ∧ hCentrePsq ∧ hCentreVQ

/-- The refactored collar residue ledger is a genuine conjunction projector (non-vacuous plumbing
    witness).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hjets_residual_collar_intro
    {hCollarJet hCentreVP hCentrePsq hCentreVQ : Prop}
    (h1 : hCollarJet) (h2 : hCentreVP) (h3 : hCentrePsq) (h4 : hCentreVQ) :
    curved_hjets_residual_collar hCollarJet hCentreVP hCentrePsq hCentreVQ :=
  ⟨h1, h2, h3, h4⟩

end QIQTH.CurvedChartJets

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.pdiffAt_of_eventuallyEq
#print axioms QIQTH.HeatResidualBound.gaussComp_pd_pd_nhds
#print axioms QIQTH.HeatResidualBound.gaussComp_amp_pd_pd_nhds
#print axioms QIQTH.HeatResidualBound.gaussComp_amp_center_decomp_nhds
#print axioms QIQTH.HeatResidualBound.witnessSecondXDeriv_expand_bridge_rho_nhds
#print axioms QIQTH.HeatResidualBound.hD2HexpandOn_concrete_nhds
#print axioms QIQTH.CurvedChartJets.curved_collarFirstJet_banked
#print axioms QIQTH.CurvedChartJets.curved_hjets_residual_collar_intro
