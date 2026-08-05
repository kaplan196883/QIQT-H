/-
  Field2NbhdReshape — J4-237: the hcarField2 NEIGHBOURHOOD RESHAPE (residue (1) of the v7 supplier block).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is the
  SOUNDNESS RESHAPE of the mixed (general-index) second-field-`pd` supplier existential `hcarField2`.
  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.  No
  existing file is edited.

  ── THE DISEASE (J4-236 finding).  `GatedRepSFix.witnessMixed2_eq_gatedMixed2RepProdS`'s `hgate`
  demands the FIRST-jet chart families GLOBALLY in the field point `y`:
      `∀ y k, HasDerivAt (fun s => W z (update y i s) k) (Pifield z y k) (y i)`   (and the `j` family),
  over ALL `y ∈ Point n`.  Off the flow image the inverse chart `W z` is `.choose` junk with no
  differentiability, so the GLOBAL-`C¹` carry is UNSATISFIABLE at the concrete proper flow-ball gate —
  the same over-strong-packaging disease as the J4-231 vacuity, one layer deeper.

  ── THE MINIMAL-QUANTIFIER FINDING.  The mixed second pd `pd_i (pd_j f) p` is the `i`-line derivative
  at `p` of the FUNCTION `y ↦ pd_j f y`.  `deriv` is LOCAL: it consumes `pd_j f` only on a neighbourhood
  of `p`.  Tracing `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`: the ONLY global-`y` uses are the two
  `funext` steps (`hGinner`, `hinner`) and the inner `funext` of `gaussComp_pd_pd_mixed` — each an
  equality of FUNCTIONS.  Weakening them to an `EventuallyEq` at `p` (valid on the OPEN gate `S z ∋ p`,
  where `W z` is `C²` at every reachable point) and closing the outer `pd` through
  `pd_congr_of_eventuallyEq` / `PdiffAt_congr_nhds` REMOVES the global requirement:  the `j` first-jet
  family and the `j`-amplitude `PdiffAt` family are needed only `∀ y ∈ S z`; the `i` first-jet, the
  mixed second jet `Q`, and the `i`/mixed amplitude data are needed only AT `p`.

  ── WHAT LANDS.
    §A — `gaussComp_pd_pd_mixed_nbhd` / `gaussComp_amp_pd_pd_mixed_nbhd` — the nbhd (open `U ∋ x₀`)
         ports of the mixed Leibniz–Gaussian normal forms:  the `j`-line jet family `hVj` and the
         `j`-amplitude `hAj1` are consumed only `∀ x ∈ U`; the `i`-line jet `hVi`, mixed second jet `hQ`
         and `i`/mixed amplitude data only at `x₀`.
    §B — `witnessMixed_gate_eq_nbhd` — the on-gate mixed order-2 formula with the `j`-families weakened
         to `∀ y ∈ S z`.
    §C — `witnessMixed2_eq_gatedMixed2RepProdS_nbhd` — ★ the reshaped everywhere identity: the same
         `GatedRepSFix` mixed identity, `hgate`'s `∀-y` jet families weakened to `∀ y ∈ S w.2.2`.
    §D — `secondFieldPd_prod_measurable_v5` / `secondFieldPd_prod_stronglyMeasurable_v5` — the v5 hcar
         shape (weakened `hgate`), re-threaded through the reshaped identity + the UNCHANGED
         `GatedRepSFix.gatedMixed2RepProdS_measurable`.
    §E — `chartFieldSecondJet_hasDerivAt` (general-`p` second field jet) + ★ `hcarField2_hgate_concrete`
         — the weakened `hgate` SATISFIED at the concrete flow-ball gate, from the C²-at-reachable-points
         first/second jets and amplitude regularity.
    §F — `concreteGate_carriers_discharged_v4` — the J4-236 v3 bundle EXTENDED with the field2 block.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OnGateJets
import QIQTH.GatedRepSFix
import QIQTH.ChartJetHessianMixed
import QIQTH.ChartFieldC2General
import QIQTH.GeneralBaseJets
import QIQTH.LaplaceBeltramiFiniteReg

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.InnerKernelJointMeas QIQTH.ExpMap QIQTH.VanVleck
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.RadialDistance
open scoped Topology BigOperators ContDiff

namespace QIQTH.Field2NbhdReshape

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the NEIGHBOURHOOD (open `U ∋ x₀`) mixed Leibniz–Gaussian normal forms.
    ############################################################################### -/

/-- **§A — nbhd mixed second coordinate partial of the composed Gaussian.**  Faithful port of
    `ChartJetHessianMixed.gaussComp_pd_pd_mixed` with the `j`-line jet family `hVj` consumed only
    `∀ x ∈ U` (open `U ∋ x₀`) — the single global `funext` (`hinner`) is replaced by an `EventuallyEq`
    on `U` and closed through `pd_congr_of_eventuallyEq`.  The `i`-line jet `hVi` and the mixed second
    jet `hQ` are needed only at `x₀`.  NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_mixed_nbhd (V : Point n → Point n)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (U : Set (Point n)) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hVi : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x₀ i s) k) (Pi x₀ k) (x₀ i))
    (hVj : ∀ x ∈ U, ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x j s) k) (Pj x k) (x j))
    (hQ : ∀ k, HasDerivAt (fun s : ℝ => Pj (Function.update x₀ i s) k) (Q k) (x₀ i)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) j y) i x₀
      = gaussDdim τ (V x₀)
        * ((∑ k, V x₀ k * Pi x₀ k) * (∑ k, V x₀ k * Pj x₀ k) / (4 * τ ^ 2)
            - ((∑ k, Pi x₀ k * Pj x₀ k) + (∑ k, V x₀ k * Q k)) / (2 * τ)) := by
  have hinner_ev : (fun y => pd (fun z => gaussDdim τ (V z)) j y)
      =ᶠ[𝓝 x₀] (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * Pj y k) / (2 * τ))) := by
    filter_upwards [hU.mem_nhds hx₀] with y hy
    exact gaussComp_pd V (Pj y) τ hτ j y (fun k => hVj y hy k)
  rw [QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq _ _ i x₀ hinner_ev]
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) i x₀ :=
    (gaussComp_hasDerivAt_line V (Pi x₀) τ hτ i x₀ (fun k => hVi k)).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hVi k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => Pj (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hQ k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * Pj y k) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) (x₀ i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  rw [pd_mul (fun y => gaussDdim τ (V y)) (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ hGf hhf,
      gaussComp_pd V (Pi x₀) τ hτ i x₀ (fun k => hVi k),
      pd_neg_div_const (fun y => ∑ k, V y k * Pj y k) (2 * τ) i x₀ hsumPdiff]
  have hpdsum : pd (fun y => ∑ k, V y k * Pj y k) i x₀
      = ∑ k, (Pi x₀ k * Pj x₀ k + V x₀ k * Q k) := by
    rw [pd_sum (Finset.univ) (fun k y => V y k * Pj y k) i x₀
        (fun k _ => (hdV k).mul (hdP k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pd_mul (fun y => V y k) (fun y => Pj y k) i x₀ (hdV k) (hdP k)]
    have h1 : pd (fun y => V y k) i x₀ = Pi x₀ k := by simp only [pd]; exact (hVi k).deriv
    have h2 : pd (fun y => Pj y k) i x₀ = Q k := by simp only [pd]; exact (hQ k).deriv
    rw [h1, h2]
  rw [hpdsum, Finset.sum_add_distrib]
  have hτ' : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-- **§A — nbhd mixed Leibniz normal form for the amplitude-weighted composed Gaussian.**  Faithful
    port of `ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed` with the `j`-line jet family `hVj` and the
    `j`-amplitude family `hAj1` consumed only `∀ x ∈ U`.  The two global `funext`s become `EventuallyEq`s
    on `U`; the `pd`-of-`gauss·A` at `x₀` (a LOCAL fact) is recovered via `PdiffAt_congr_nhds`.
    NOT `a₁ = R/6`. -/
theorem gaussComp_amp_pd_pd_mixed_nbhd (V : Point n → Point n) (A : Point n → ℝ)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (U : Set (Point n)) (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hVi : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x₀ i s) k) (Pi x₀ k) (x₀ i))
    (hVj : ∀ x ∈ U, ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x j s) k) (Pj x k) (x j))
    (hQ : ∀ k, HasDerivAt (fun s : ℝ => Pj (Function.update x₀ i s) k) (Q k) (x₀ i))
    (hAj1 : ∀ x ∈ U, PdiffAt A j x)
    (hAi1 : PdiffAt A i x₀)
    (hA2 : PdiffAt (fun y => pd A j y) i x₀) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) j y) i x₀
      = gaussDdim τ (V x₀)
          * ((∑ k, V x₀ k * Pi x₀ k) * (∑ k, V x₀ k * Pj x₀ k) / (4 * τ ^ 2)
              - ((∑ k, Pi x₀ k * Pj x₀ k) + (∑ k, V x₀ k * Q k)) / (2 * τ)) * A x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * Pj x₀ k) / (2 * τ))) * pd A i x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * Pi x₀ k) / (2 * τ))) * pd A j x₀
        + gaussDdim τ (V x₀) * pd (fun y => pd A j y) i x₀ := by
  have hGfPj : ∀ x ∈ U, PdiffAt (fun z => gaussDdim τ (V z)) j x :=
    fun x hx => (gaussComp_hasDerivAt_line V (Pj x) τ hτ j x (fun k => hVj x hx k)).differentiableAt
  have hGfPi : PdiffAt (fun z => gaussDdim τ (V z)) i x₀ :=
    (gaussComp_hasDerivAt_line V (Pi x₀) τ hτ i x₀ (fun k => hVi k)).differentiableAt
  have hGinner_ev : (fun y => pd (fun z => gaussDdim τ (V z)) j y)
      =ᶠ[𝓝 x₀] (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * Pj y k) / (2 * τ))) := by
    filter_upwards [hU.mem_nhds hx₀] with y hy
    exact gaussComp_pd V (Pj y) τ hτ j y (fun k => hVj y hy k)
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hVi k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => Pj (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hQ k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * Pj y k) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) (x₀ i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * Pj y k) / (2 * τ)) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * Pj (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  have hpdGf_pdiff : PdiffAt (fun y => pd (fun z => gaussDdim τ (V z)) j y) i x₀ :=
    QIQTH.LaplaceBeltrami.PdiffAt_congr_nhds i x₀ hGinner_ev (hGfPi.mul hhf)
  have hinner_ev : (fun y => pd (fun z => gaussDdim τ (V z) * A z) j y)
      =ᶠ[𝓝 x₀] (fun y => pd (fun z => gaussDdim τ (V z)) j y * A y
          + gaussDdim τ (V y) * pd A j y) := by
    filter_upwards [hU.mem_nhds hx₀] with y hy
    exact pd_mul (fun z => gaussDdim τ (V z)) A j y (hGfPj y hy) (hAj1 y hy)
  rw [QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq _ _ i x₀ hinner_ev]
  rw [pd_add (fun y => pd (fun z => gaussDdim τ (V z)) j y * A y)
        (fun y => gaussDdim τ (V y) * pd A j y) i x₀
        (hpdGf_pdiff.mul hAi1) (hGfPi.mul hA2),
      pd_mul (fun y => pd (fun z => gaussDdim τ (V z)) j y) A i x₀ hpdGf_pdiff hAi1,
      pd_mul (fun y => gaussDdim τ (V y)) (fun y => pd A j y) i x₀ hGfPi hA2]
  rw [gaussComp_pd_pd_mixed_nbhd V Pi Pj Q τ hτ i j x₀ U hU hx₀ hVi hVj hQ,
      gaussComp_pd V (Pj x₀) τ hτ j x₀ (fun k => hVj x₀ hx₀ k),
      gaussComp_pd V (Pi x₀) τ hτ i x₀ (fun k => hVi k)]
  ring

/-! ###############################################################################
    ### §B — the on-gate mixed order-2 formula with the `j`-families weakened to `∀ y ∈ S z`.
    ############################################################################### -/

/-- **★ §B — `witnessMixed_gate_eq_nbhd`.**  Nbhd port of `ChartJetHessianMixed.witnessMixed_gate_eq`:
    the on-gate OFF-DIAGONAL second field-`pd` of the gated van-Vleck witness equals the mixed
    Leibniz–Gaussian normal form, with the `j`-line chart jet family `hJetVj` and the `j`-amplitude
    family `hAmpj1` consumed only `∀ y ∈ S z` (the OPEN gate `∋ p`), and the `i`-line jet, mixed second
    jet and `i`/mixed amplitude data only at `p`.  Route: the on-gate nbhd factorisation of the witness
    (`vanVleckGatedWitness_gate_apply` on the open `S z`), `pd_pd_congr_at_mixed`, then
    `gaussComp_amp_pd_pd_mixed_nbhd` with `U = S z`.  NOT `a₁ = R/6`. -/
theorem witnessMixed_gate_eq_nbhd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pi Pj : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pi p k) (p i))
    (hJetVj : ∀ x ∈ S z, ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x j s) k) (Pj x k) (x j))
    (hJetQ : ∀ k, HasDerivAt
      (fun s : ℝ => Pj (Function.update p i s) k) (Q k) (p i))
    (hAmpj1 : ∀ x ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b τ z) j x)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p) :
    pd (fun y => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) j y) i p
      = gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * ((∑ k, uniformInverseChart g gi hC hK z p k * Pi p k)
                * (∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (4 * τ ^ 2)
              - ((∑ k, Pi p k * Pj p k)
                  + (∑ k, uniformInverseChart g gi hC hK z p k * Q k)) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z p
        + (gaussDdim τ (uniformInverseChart g gi hC hK z p)
              * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pj p k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) i p
        + (gaussDdim τ (uniformInverseChart g gi hC hK z p)
              * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pi p k) / (2 * τ)))
            * pd (chartFieldAmp g gi hC hK a b τ z) j p
        + gaussDdim τ (uniformInverseChart g gi hC hK z p)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) j y) i p := by
  have hev : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      =ᶠ[𝓝 p]
      (fun x' : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * chartFieldAmp g gi hC hK a b τ z x') := by
    refine eventually_nhds_iff.mpr ⟨S z, ?_, hSopen, hp⟩
    intro x' hx'
    show vanVleckGatedWitness g gi hC hK S a b τ x' z
        = gaussDdim τ (uniformInverseChart g gi hC hK z x') * chartFieldAmp g gi hC hK a b τ z x'
    rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz hx']
    simp only [chartFieldAmp]
    ring
  rw [QIQTH.ChartJetHessianMixed.pd_pd_congr_at_mixed
        (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z)
        (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * chartFieldAmp g gi hC hK a b τ z x') i j p hev,
      gaussComp_amp_pd_pd_mixed_nbhd (uniformInverseChart g gi hC hK z)
        (chartFieldAmp g gi hC hK a b τ z) Pi Pj Q τ hτ i j p (S z) hSopen hp
        hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]

/-! ###############################################################################
    ### §C — ★ the RESHAPED everywhere identity (weakened `hgate`, `∀ y ∈ S w.2.2`).
    ############################################################################### -/

/-- **★ §C — `witnessMixed2_eq_gatedMixed2RepProdS_nbhd`.**  The same everywhere identity as
    `GatedRepSFix.witnessMixed2_eq_gatedMixed2RepProdS` (raw off-diagonal second field-`pd` of the
    concrete witness `=` the FULL-gate re-gated general-index representative `gatedMixed2RepProdS`),
    with `hgate`'s two `∀-y` chart jet families AND the `∀-y` `j`-amplitude family WEAKENED to
    `∀ y ∈ S w.2.2` — the honest satisfiable quantifier (the OPEN gate is exactly where the chart is
    `C²`).  The off-gate / nonpos branches are unchanged; the on-gate branch calls the nbhd formula
    `witnessMixed_gate_eq_nbhd` (instantiating the `∀ y ∈ S z` families and the at-`p` jets).  The
    off-`S` vanishing `hOffS2` is the same radialCutoff-support carrier.  NOT `a₁ = R/6`. -/
theorem witnessMixed2_eq_gatedMixed2RepProdS_nbhd (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0) :
    ∀ w : ℝ × Point n × Point n,
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
        = QIQTH.GatedRepSFix.gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield w := by
  intro w
  simp only [QIQTH.GatedRepSFix.gatedMixed2RepProdS]
  by_cases hzKS : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
  · obtain ⟨hzK, hpS⟩ := hzKS
    rw [Set.indicator_of_mem
      (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from ⟨hzK, hpS⟩)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hjetVi, hjetVj, hjetQ, hampj, hampi, hamp2⟩ := hgate w hzK hτ hpS
      exact witnessMixed_gate_eq_nbhd g gi hC hK S a b i j w.1 hτ w.2.2 hzK hSopen w.2.1 hpS
        (Pifield w.2.2) (Pjfield w.2.2) (Qfield w.2.2 w.2.1)
        (hjetVi w.2.1 hpS) hjetVj hjetQ hampj hampi hamp2
    · rw [not_lt] at hτ
      rw [QIQTH.ChartJetHessianMixed.witnessMixed_eq_zero_of_nonpos hn g gi hC hK S a b i j
            w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem
      (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} from hzKS)]
    by_cases hzK : w.2.2 ∈ K
    · have hpS : w.2.1 ∉ S w.2.2 := fun h => hzKS ⟨hzK, h⟩
      by_cases hτ : 0 < w.1
      · exact hOffS2 w hzK hτ hpS
      · rw [not_lt] at hτ
        exact QIQTH.ChartJetHessianMixed.witnessMixed_eq_zero_of_nonpos hn g gi hC hK S a b i j
          w.1 w.2.1 w.2.2 hτ
    · exact QIQTH.ChartJetHessianMixed.witnessMixed_offGate_eq_zero g gi hC hK S a b i j
        w.1 w.2.1 w.2.2 hzK

/-! ###############################################################################
    ### §D — the v5 hcar shape (weakened `hgate`), re-threaded through the reshaped identity.
    ############################################################################### -/

/-- **★★ `secondFieldPd_prod_measurable_v5`.**  The mixed second-`pd` measurability from the WEAKENED
    (`∀ y ∈ S w.2.2`) carrier: the raw off-diagonal second field-`pd` kernel is jointly Borel, via the
    reshaped identity `witnessMixed2_eq_gatedMixed2RepProdS_nbhd` glued to the UNCHANGED
    `GatedRepSFix.gatedMixed2RepProdS_measurable`.  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_measurable_v5 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPimeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
    (hPjmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
    (hQmeas : ∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivIMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDerivJMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
          (Pifield w.2.2 y k) (y i)) ∧
        (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
          (Pjfield w.2.2 y k) (y j)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k) (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
        (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
    (hOffS2 : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1 = 0) :
    Measurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1)
      = QIQTH.GatedRepSFix.gatedMixed2RepProdS g gi hC hK S a b i j Pifield Pjfield Qfield := by
    funext w
    exact witnessMixed2_eq_gatedMixed2RepProdS_nbhd hn g gi hC hK S a b i j Pifield Pjfield Qfield
      hgate hOffS2 w
  rw [hrw]
  exact QIQTH.GatedRepSFix.gatedMixed2RepProdS_measurable g gi hC hK S a b i j Pifield Pjfield Qfield
    hKSmeas hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas

/-- **★★ `secondFieldPd_prod_stronglyMeasurable_v5` — BorelDischargeSurface CONJUNCT (3), ∀ i j,
    SATISFIABLE (weakened `hgate`).**  For the concrete gated witness `G := vanVleckGatedWitness …`,
    `∀ i j, StronglyMeasurable (fun w => pd (fun y => pd (fun x => G w.1 x w.2.2) j y) i w.2.1)`, with
    the `hcarField2` existential's `hgate` jet families weakened to `∀ y ∈ S w.2.2` — the SATISFIABLE
    v5 shape (`hcarField2_hgate_concrete` discharges it at the concrete gate).  CONTINUITY-FREE.
    NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_stronglyMeasurable_v5 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0)) :
    ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1) := by
  intro i j
  obtain ⟨Pifield, Pjfield, Qfield, hChartMeas, hPimeas, hPjmeas, hQmeas, hAmpMeas,
    hAmpDerivIMeas, hAmpDerivJMeas, hAmpDeriv2Meas, hgate, hOffS2⟩ := hcar i j
  exact (secondFieldPd_prod_measurable_v5 hn g gi hC hK S a b i j Pifield Pjfield Qfield hKSmeas
    hChartMeas hPimeas hPjmeas hQmeas hAmpMeas hAmpDerivIMeas hAmpDerivJMeas hAmpDeriv2Meas
    hgate hOffS2).stronglyMeasurable

/-! ###############################################################################
    ### §E — the general-`p` SECOND field jet + ★ the weakened `hgate` at the concrete gate.
    ############################################################################### -/

/-- **★ `chartFieldSecondJet_hasDerivAt` — the general-`p`, general-`(i,j)` SECOND field jet.**
    General-point / off-diagonal port of `GeneralBaseJets.chartField_secondJet_of_contDiffAt`
    (field-centre `0`, `i = i`): from `ContDiffAt ℝ 2 (W z) p`, the `i`-line derivative of the
    `j`-column of the inverse-chart Jacobian exists at `p` —
        `HasDerivAt (fun s ↦ DW_z(update p i s)(e_j) k) (D(DW_z(·)(e_j))(p)(e_i) k) (p i)`.
    Route: `C² ⟹ fderiv W z ∈ C¹` at `p`, so `y ↦ DW_z(y)(e_j)` is differentiable at `p`; compose with
    the coordinate line (`hasDerivAt_update_line`).  NOT `a₁ = R/6`. -/
theorem chartFieldSecondJet_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z p : Point n) (i j : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) p) :
    ∀ k, HasDerivAt
      (fun s : ℝ =>
        fderiv ℝ (uniformInverseChart g gi hC hK z) (Function.update p i s) (Pi.single j (1 : ℝ)) k)
      (fderiv ℝ (fun y => (fderiv ℝ (uniformInverseChart g gi hC hK z) y) (Pi.single j (1 : ℝ))) p
          (Pi.single i (1 : ℝ)) k) (p i) := by
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ W y) p :=
    hreg.fderiv_right (m := 1) (by norm_num)
  have hΦ : DifferentiableAt ℝ (fun y => fderiv ℝ W y) p := hfd.differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) p :=
    hΦ.clm_apply (differentiableAt_const _)
  have hGfd : HasFDerivAt (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) p)
      (Function.update p i (p i)) := by
    rw [Function.update_eq_self]; exact hG.hasFDerivAt
  have hcomp : HasDerivAt
      (fun s : ℝ => (fderiv ℝ W (Function.update p i s)) (Pi.single j (1 : ℝ)))
      (fderiv ℝ (fun y => (fderiv ℝ W y) (Pi.single j (1 : ℝ))) p (Pi.single i (1 : ℝ))) (p i) := by
    have h := hGfd.comp_hasDerivAt (p i) (hasDerivAt_update_line p i)
    simpa using h
  exact fun k => (hasDerivAt_pi.mp hcomp) k

/-- **★★ `hcarField2_hgate_concrete` — the WEAKENED `hgate` SATISFIED at the concrete flow-ball gate.**
    At `S q = uniformFlowExp g gi hC hK q '' Metric.ball 0 c` (`0 < a < b < c < δ₀`), for every index
    pair `(i, j)` there are first-jet fields `Pifield`/`Pjfield` (the chart Fréchet columns) and a mixed
    second-jet field `Qfield` (the `i`-derivative of the `j`-column) such that on the FULL gate the
    weakened `hgate` holds:
      • `IsOpen (S q)`;
      • `∀ y ∈ S q, ∀ k`, the `i`/`j` first field jets (§`chartFieldFirstJet_hasDerivAt` at each
        reachable `y`);
      • `∀ k`, the mixed second field jet at `p = w.2.1` (`chartFieldSecondJet_hasDerivAt`);
      • `∀ y ∈ S q`, the `j`-amplitude `PdiffAt` (`OnGateJets.ampField_pdiffAt`);
      • the `i`-amplitude `PdiffAt` at `p` and the mixed amplitude `PdiffAt` at `p`
        (`LaplaceBeltrami.PdiffAt_pd_of_contDiffAt` from `OnGateJets.ampField_contDiffAt`).
    Every provider is a C²-at-reachable-points fact + Riemannian positivity — SATISFIABLE, never the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hcarField2_hgate_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 := by
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min δr δo, lt_min hδr hδo, ?_⟩
  intro c hbc hcδ S hSeq i j
  refine ⟨fun q y k => fderiv ℝ (uniformInverseChart g gi hC hK q) y (Pi.single i (1 : ℝ)) k,
    fun q y k => fderiv ℝ (uniformInverseChart g gi hC hK q) y (Pi.single j (1 : ℝ)) k,
    fun q p k => fderiv ℝ
        (fun y => (fderiv ℝ (uniformInverseChart g gi hC hK q) y) (Pi.single j (1 : ℝ))) p
        (Pi.single i (1 : ℝ)) k, ?_⟩
  intro w hzK hτ hpS
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδo : c < δo := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rw [hSeq]
  -- every point of the gate is `C²` for the chart.
  have hC2 : ∀ y ∈ S w.2.2, ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) y := by
    intro y hyS
    have hyS' : y ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      rwa [hSq] at hyS
    obtain ⟨v, hv, hvy⟩ := hyS'
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    rw [← hvy]; exact hreach w.2.2 hzK v (lt_trans hvc hcδr)
  have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := hC2 w.2.1 hpS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSq]; exact (hopen w.2.2 hzK).2 c hc0 hcδo |>.1
  · intro y hyS k
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 y i k (hC2 y hyS)
  · intro y hyS k
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 y j k (hC2 y hyS)
  · intro k
    exact chartFieldSecondJet_hasDerivAt g gi hC hK w.2.2 w.2.1 i j hCp k
  · intro y hyS
    exact QIQTH.OnGateJets.ampField_pdiffAt g gi hC hK a b w.1 w.2.2 y j hg hu (hC2 y hyS) (hgpos _)
  · exact QIQTH.OnGateJets.ampField_pdiffAt g gi hC hK a b w.1 w.2.2 w.2.1 i hg hu hCp (hgpos _)
  · exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
      (chartFieldAmp g gi hC hK a b w.1 w.2.2) j i w.2.1
      (QIQTH.OnGateJets.ampField_contDiffAt g gi hC hK a b w.1 w.2.2 w.2.1 hg hu hCp (hgpos _))

/-! ###############################################################################
    ### §F — the J4-236 v3 bundle EXTENDED with the field2 block.
    ############################################################################### -/

/-- **★★★ `concreteGate_carriers_discharged_v4` — the v3 bundle EXTENDED with the WEAKENED field2 block.**
    At the concrete flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`
    (`0 < a < b < c < δ₀`), UNDER a SINGLE radius `δ₀`, the `J4-236`
    `OnGateJets.concreteGate_carriers_discharged_v3` bundle (v2 five carriers + on-gate first-field
    `hgate` + `∂_τ` amplitude) holds SIMULTANEOUSLY with the WEAKENED (`∀ y ∈ S q`) SECOND-field-`pd`
    `hgate` block (`hcarField2_hgate_concrete`, ∀ `i j`, this file).

    After this brick the ONLY remaining v7 supplier obligation is the MEASURABILITY block — the
    definitional `.choose` chart-measurability wall of `ChartJointBorel`, isolated to the shared
    `hChartRep` obligation.  NOT `a₁ = R/6`. -/
theorem concreteGate_carriers_discharged_v4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      -- J4-234/235: the five carriers of `concreteGate_carriers_discharged_v2`.
      ((MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          ∧ (0 : Point n) ∈ S 0
          ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)))
        ∧ (∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0)
        ∧ (∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y)
                i w.2.1 = 0))
      -- J4-236: the on-gate FIRST field-`pd` `hgate` block (∀ `k`).
      ∧ (∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
      -- J4-236: the on-gate `∂_τ` amplitude HasDerivAt (`hcarTau`).
      ∧ (∃ Cfield : Point n → Point n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)
      -- J4-237: the on-gate WEAKENED (`∀ y ∈ S q`) SECOND field-`pd` `hgate` block (∀ `i j`).
      ∧ (∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, h3⟩ :=
    QIQTH.OnGateJets.concreteGate_carriers_discharged_v3 g gi hC hK hK0 a b ha hab hg hgpos hu
  obtain ⟨δ₂, hδ₂, hfield2⟩ :=
    hcarField2_hgate_concrete g gi hC hK a b ha hab hg hgpos hu
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  obtain ⟨hv2, hfield, htau⟩ := h3 c hbc hcδ₁ S hSeq
  exact ⟨hv2, hfield, htau, hfield2 c hbc hcδ₂ S hSeq⟩

end QIQTH.Field2NbhdReshape

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.Field2NbhdReshape
#print axioms gaussComp_pd_pd_mixed_nbhd
#print axioms gaussComp_amp_pd_pd_mixed_nbhd
#print axioms witnessMixed_gate_eq_nbhd
#print axioms witnessMixed2_eq_gatedMixed2RepProdS_nbhd
#print axioms secondFieldPd_prod_measurable_v5
#print axioms secondFieldPd_prod_stronglyMeasurable_v5
#print axioms chartFieldSecondJet_hasDerivAt
#print axioms hcarField2_hgate_concrete
#print axioms concreteGate_carriers_discharged_v4
end AxiomChecks
