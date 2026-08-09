/-
  FormGateGrounding — J4-496: discharge the `hform_gate` off-collar `(ρ−1)` near-isometry form of
  `concreteRemainder_order_reach` from the banked chart jet supply, finishing the remainder subsystem.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign — the LAST remainder-subsystem
  cleanup.  No `sorry` (header prose excepted), no `:= True`, no `admit`, no new axioms, no vacuous /
  unsatisfiable hypothesis, no result equal to (or trivially yielding) the conclusion, no existing file
  edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT — the last RAW analytic carry of the remainder capstone.  `AmpDiffGrounding.
  concreteRemainder_order_reach` grounded the on-collar amplitude-difference sup `hAmpDiff` to (I1), but
  still CARRIES the OFF-COLLAR gate identity as a raw analytic hypothesis
      `hform_gate : ∀ z ∈ (collar (c√τ))ᶜ, z ∈ K → ‖z‖ < r →
          IchartResidual … z − hessGaussFactor·(chartAmp·F)
            = hessGaussFactor·((rhoRatio − 1)·(chartAmp·F))`
  — an OPAQUE assertion about the value of the complicated `IchartResidual` on the annulus.

  ## THE VERDICT — PURE WIRING (no new geometric estimate).  The `(ρ−1)` annulus form is ALREADY a proved
  banked lemma: `SlotInstantiationV.ichartResidual_sub_hess_form` proves EXACTLY this identity POINTWISE
  at any `z ∈ K`, and — per the SlotInstantiationV regime audit — its hypotheses contain NO collar / `r₀`
  / `τ₀` bound, so it holds OFF-COLLAR.  Its per-point inputs are the CHART JET SUPPLY: the chart first
  jet `P` (`hV1`), its `i`-jet `Q` (`hP1`), the amplitude Pdiffs `hA1`/`hA2`, the three center identities
  `hVP`/`hPsq`/`hVQ`, and the two amplitude-derivative equations `hA1eq`/`hA2eq` — the SAME jet family
  that `AmplitudeDataOnCollar.hD2HexpandOn_concrete` consumes on the collar.  So `hform_gate` is a
  per-annulus-point application of the banked identity, wrapped over the annulus with the jet supply.

  ## WHAT LANDS.
    ★  `hform_gate_of_jetSupply` — from a per-annulus-point CHART JET SUPPLY `hjets` (∃ P Q, the chart
       first/second jets + amplitude Pdiffs + center identities + amplitude-derivative equations, demanded
       EXACTLY on the annulus `(collar (c√τ))ᶜ ∩ K ∩ {‖z‖ < r}`), `ichartResidual_sub_hess_form` gives the
       `hform_gate` identity at each such `z`.  Pure `intro` + `obtain` + apply.
    ★★★ `concreteRemainder_order_reach_form` — the remainder-subsystem CAPSTONE: the SAME explicit `O(1/τ)`
       bound as `concreteRemainder_order_reach`, but with the RAW `hform_gate` carry DISCHARGED from the
       chart jet supply `hjets`.  The remaining substantive external hypotheses are now ONLY the genuine
       geometric inputs — `hiso` (the (I1) near-isometry lower bound), `hgate` (the (ρ−1) annulus
       near-isometry: cubic-jet error + lower bound), and `hjets` (the chart jet supply) — plus the banked
       amplitude/integrability feeds (`hAampForm`/`hfInt`/`hA1F`/`hA2F`/`hqcbdd`).  NO raw analytic gate
       carry remains.

  ## THE GATE (satisfiability — checked BEFORE building).  REGION-CORRECT & (I1)-COMPATIBLE.  `hjets` is
  demanded on EXACTLY the annulus `(collar (c√τ))ᶜ ∩ K ∩ {‖z‖ < r}` the capstone consumes `hform_gate` on
  (NOT full space — the same off-collar trap J4-495 caught is avoided: the jet supply is confined to the
  gate).  It is SATISFIABLE: it is the actual differential structure of the true chart
  `uniformInverseChart` (with `S z` its open domain containing 0) — the SAME jet family the on-collar side
  already uses via `hD2HexpandOn_concrete`, instantiated off-collar per the SlotInstantiationV regime
  audit.  It is NOT the raw `IchartResidual` value; it is the PRIMITIVE chart-jet geometry from which the
  identity is PROVED, so the swap replaces an opaque analytic assertion by genuine geometric input.

  ## HONEST DISTANCE.  This FINISHES the remainder subsystem: the concrete heat-trace remainder τ-order now
  rests on ONLY genuine geometric inputs (`hiso`/`hgate`/`hjets`) + banked amplitude/integrability feeds —
  no raw analytic gate carry.  ⚠ NOT `a₁ = R/6`; the LEADING O(1) coefficient and its `R/6` identification
  lie BEYOND this remainder τ-order.  a₁ = R/6 remains CONDITIONAL.
-/
import QIQTH.AmpDiffGrounding
import QIQTH.SlotInstantiationV

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII
open QIQTH.SlotInstantiationV
open QIQTH.AmpDiffGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.FormGateGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE JET-SUPPLY DISCHARGE of the off-collar `(ρ−1)` gate form.
    ############################################################################### -/

/-- **★ `hform_gate_of_jetSupply`.**  The off-collar `(ρ−1)` near-isometry gate form `hform_gate` on the
    annulus `(collar (c√τ))ᶜ ∩ K ∩ {‖z‖ < r}`, DERIVED from a per-annulus-point CHART JET SUPPLY `hjets`
    (the chart first/second `i`-jets, the amplitude Pdiffs, the three center identities, and the two
    amplitude-derivative equations) by a single per-point application of the banked, off-collar
    `SlotInstantiationV.ichartResidual_sub_hess_form`.  Pure wiring — no new estimate.  ⚠ NOT `a₁ = R/6`. -/
theorem hform_gate_of_jetSupply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r : ℝ)
    (hjets : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ, z ∈ K → ‖z‖ < r →
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        IsOpen (S z) ∧ (0 : Point n) ∈ S z
        ∧ (∀ x k, HasDerivAt
            (fun t : ℝ => uniformInverseChart g gi hC hK z (Function.update x i t) k) (P x k) (x i))
        ∧ (∀ k, HasDerivAt
            (fun t : ℝ => P (Function.update (0 : Point n) i t) k) (Q k) ((0 : Point n) i))
        ∧ (∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
        ∧ PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
        ∧ (∑ k, P 0 k ^ 2 = 1)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)
        ∧ data.A1amp τ z
            = rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)
        ∧ data.A2amp τ z
            = rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) :
    ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ, z ∈ K → ‖z‖ < r →
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) := by
  intro z hzc hzK hznorm
  obtain ⟨P, Q, hSopen, h0, hV1, hP1, hA1, hA2, hVP, hPsq, hVQ, hA1eq, hA2eq⟩ :=
    hjets z hzc hzK hznorm
  exact ichartResidual_sub_hess_form g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ z
    hzK hSopen h0 P Q hV1 hP1 hA1 hA2 hVP hPsq hVQ hA1eq hA2eq

/-! ###############################################################################
    ### ★★★ THE REMAINDER-SUBSYSTEM CAPSTONE (no raw analytic gate carry).
    ############################################################################### -/

/-- **★★★ `concreteRemainder_order_reach_form` — CONCRETE REMAINDER τ-ORDER with BOTH `hAmpDiff` (I1)-
    grounded AND `hform_gate` discharged from the chart jet supply.**  Identical explicit `O(1/τ)` bound
    as `AmpDiffGrounding.concreteRemainder_order_reach`, but the RAW off-collar analytic carry
    `hform_gate` is REPLACED by the per-annulus-point chart jet supply `hjets`, from which
    `hform_gate_of_jetSupply` re-derives it via the banked `ichartResidual_sub_hess_form`.  The remaining
    substantive external hypotheses are now ONLY the genuine geometric inputs `hiso` (the (I1) near-
    isometry lower bound), `hgate` (the (ρ−1) annulus near-isometry) and `hjets` (the chart jet supply),
    plus the banked amplitude/integrability feeds — the remainder subsystem is FINISHED.  ⚠ NOT
    `a₁ = R/6`. -/
theorem concreteRemainder_order_reach_form (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (r Liso L' M1F M2F Mqc : ℝ) (hLiso : 0 ≤ Liso) (hL' : 0 ≤ L')
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (hgateCollar : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hAampForm : ∀ z : Point n,
      data.Aamp τ z = rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0)
    (hfInt : Integrable
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) volume)
    (hjets : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ, z ∈ K → ‖z‖ < r →
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        IsOpen (S z) ∧ (0 : Point n) ∈ S z
        ∧ (∀ x k, HasDerivAt
            (fun t : ℝ => uniformInverseChart g gi hC hK z (Function.update x i t) k) (P x k) (x i))
        ∧ (∀ k, HasDerivAt
            (fun t : ℝ => P (Function.update (0 : Point n) i t) k) (Q k) ((0 : Point n) i))
        ∧ (∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
        ∧ PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
        ∧ (∑ k, P 0 k ^ 2 = 1)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)
        ∧ data.A1amp τ z
            = rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)
        ∧ data.A2amp τ z
            = rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0)
    (hgate : ∀ z ∈ K, ‖z‖ < r →
      (|rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
      ∧ ((1 / 2 : ℝ) * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)))
    (hA1F : ∀ z, |data.A1amp τ z * F s z 0| ≤ M1F)
    (hA2F : ∀ z, |data.A2amp τ z * F s z 0| ≤ M2F)
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    |∫ z : Point n, (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ (collarK (n := n) Liso c τ₀ + 1) * Mqc * ((n : ℝ) + 1) / (2 * τ)
        + (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
              * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                  + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
              / 16 / Real.sqrt τ
            + (M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ))) := by
  have hform_gate := hform_gate_of_jetSupply g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r hjets
  exact concreteRemainder_order_reach g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ hττ₀
    r Liso L' M1F M2F Mqc hLiso hL' hM1F hM2F hMqc hKr hgateCollar hiso hAampForm hfInt
    hform_gate hgate hA1F hA2F hqcbdd

end QIQTH.FormGateGrounding

/-! ###############################################################################
    ## J4-496 LEDGER — discharging `hform_gate`, finishing the remainder subsystem.
    ###############################################################################

  WHAT LANDS.  `concreteRemainder_order_reach_form` reproves the CONCRETE remainder τ-order
    `|∫ f| ≤ (collarK+1)·Mqc·(n+1)/(2τ) + (Bcomp₂/√τ + (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)))`
  with the RAW off-collar analytic carry `hform_gate` REPLACED by the per-annulus-point chart jet supply
  `hjets`, from which `hform_gate_of_jetSupply` re-derives `hform_gate` via the banked, off-collar-
  unconditional `SlotInstantiationV.ichartResidual_sub_hess_form`.

  ⚠ THE GATE (region + satisfiability).  `hjets` is demanded on EXACTLY the annulus
  `(collar (c√τ))ᶜ ∩ K ∩ {‖z‖ < r}` — the SAME region the capstone consumes `hform_gate` on (NOT full
  space; the off-collar blow-up trap J4-495 caught is avoided by confining the jet supply to the gate).
  It is the actual chart-jet geometry of the true chart `uniformInverseChart` (with `S z` its open domain
  containing 0) — the SAME jet family `AmplitudeDataOnCollar.hD2HexpandOn_concrete` consumes on the
  collar, instantiated off-collar per the SlotInstantiationV REGIME AUDIT (the identity's hypotheses carry
  NO collar / `r₀` / `τ₀` bound).  So the swap replaces an OPAQUE analytic assertion about `IchartResidual`
  by PRIMITIVE geometric chart-jet data from which the identity is PROVED — genuine de-risking, not
  relabeling.

  DON'T-UNDERCREDIT.  The `(ρ−1)` annulus form was ALREADY a proved banked lemma
  (`ichartResidual_sub_hess_form`); this brick is the thin adapter wrapping it over the annulus.  Heavy
  analysis reused verbatim: the whole `concreteRemainder_order_reach` three-region assembly (on-collar
  (I1) amp-diff moment + banked off-collar `hcomp_final4` + collar split) and the banked pointwise gate
  identity.  NEW content: the per-annulus-point jet-supply wrapper + the reproved capstone.

  HONEST DISTANCE.  This FINISHES the remainder subsystem: the concrete heat-trace remainder τ-order now
  rests on ONLY genuine geometric inputs (`hiso` near-isometry lower bound, `hgate` (ρ−1) annulus near-
  isometry, `hjets` chart jet supply) + banked amplitude/integrability feeds — NO raw analytic gate carry
  remains.  ⚠ a₁ = R/6 remains CONDITIONAL; the LEADING O(1) coefficient and its `R/6` identification lie
  BEYOND this remainder τ-order (the coefficient-facing walls — the q-audit / Gaussian-moment extraction /
  arbitrary-metric van-Vleck 2-jet — are the next frontier).
-/

section AxiomChecks
open QIQTH.FormGateGrounding
#print axioms hform_gate_of_jetSupply
#print axioms concreteRemainder_order_reach_form
end AxiomChecks
