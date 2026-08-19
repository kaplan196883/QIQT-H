/-
  HZMassIntegrabilityAttempt — J4-867: the `z`-mass wall under the EXPLICIT `BF` (compact base support
  + the Gaussian-envelope mass-one reduction of `hzmass`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick attacks the deep §C
  `hzmass` `z`-mass wall of `MixedDirectionsFieldHessianEnvelope` using the EXPLICIT field-Hessian
  envelope `BF s z := ⨆ x, ‖fderiv …‖` (J4-865).  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## PART-2 FACT-FINDING VERDICT (did the explicit `BF` simplify `hzmass`?).

  `hzmass` is `∫z BL s z · BF s z ≤ C·(t−s)⁻¹`.  Two GENUINE simplifications flow from the explicit
  `BF s z = ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … i (t−s) y z) x‖`:

  (1) **COMPACT BASE SUPPORT (proved, unconditional).**  The witness gate `gatedKernel K S H` kills the
      base slot off `K` (`gatedKernel_apply_of_notMem … (Or.inl hz)`), so for `z ∉ K` the whole field
      kernel `x' ↦ vanVleckGatedWitness … x' z` is `≡ 0`, hence `witnessFieldDeriv … · z ≡ 0`, hence the
      field-Hessian `fderiv (…) ≡ 0`, hence `BF s z = ⨆ x, 0 = 0`.  So the `z`-integrand `BL·BF` is
      SUPPORTED IN THE COMPACT `K`: `∫z BL·BF = ∫_{z∈K} BL·BF`.  This is the concrete payoff of the
      explicit `BF` — the `z`-mass problem lives on a compact set, which is exactly what makes `hbint`
      (integrability) and a bounded-times-finite-measure estimate tractable.

  (2) **GAUSSIAN-ENVELOPE MASS-ONE REDUCTION (proved).**  `hzmass` reduces to a POINTWISE Gaussian-in-`z`
      envelope on the PRODUCT: if `BL s z · BF s z ≤ C·(t−s)⁻¹·gaussDdim (t−s) z` (a.e. `s`, all `z`)
      with the envelope integrable, then `∫z BL·BF ≤ C·(t−s)⁻¹` by `gaussDdim_mass_one` (`∫ gaussDdim = 1`).
      So the INTEGRAL bound `hzmass` collapses to a POINTWISE product envelope whose `(t−s)⁻¹` prefactor
      is explicit — the natural target now that `BF` is a concrete `⨆`.

  ## ⚠ WHAT IS **NOT** SIMPLIFIED (the honest residual).
  The remaining genuine content is the POINTWISE Gaussian envelope on the product `BL s z · BF s z`
  itself — i.e. bounding `⨆ x, ‖fderiv …‖` by `D·(t−s)⁻¹·gaussDdim (t−s) z` in `z`.  `BF` being a `⨆`
  over the COMPACT gate is well-behaved (finite, attained), but certifying its `z`-decay is a Gaussian
  field-Hessian estimate of the SAME difficulty class flagged before; the explicit `BF` gives the
  compact support and the clean mass-one target, NOT the envelope itself.  So `hzmass` is REDUCED and
  its geometry clarified, but the core Gaussian-decay estimate remains open.  NOT `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HZMassIntegrabilityAttempt`).
    • `witnessFieldDeriv_eqZero_of_base_notMem_K` — field-`pd` vanishes for `z ∉ K` (unconditional).
    • `witnessFieldHessian_fderiv_eqZero_of_base_notMem_K` — field-Hessian CLM vanishes for `z ∉ K`.
    • `BF_ciSup_eqZero_of_base_notMem_K` — the EXPLICIT `BF` envelope `= 0` for `z ∉ K`.
    • `productEnvelope_support_subset_K` — `Function.support (z ↦ BL s z · BF s z) ⊆ K`.
    • `hzmass_of_gaussian_product_envelope` — ★ the mass-one reduction of `hzmass` to a pointwise
      Gaussian-in-`z` product envelope.
    • `hzmass_gaussian_reduction_nonvacuous` — antecedents inhabited (`BL·BF ≡ 0`).
-/
import Mathlib
import QIQTH.ChartJetXUniformBound
import QIQTH.GaussianHessianCancel

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlatHeatEquation
open QIQTH.ChartJetXUniformBound
open scoped Topology BigOperators

namespace QIQTH.HZMassIntegrabilityAttempt

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### COMPACT BASE SUPPORT — the explicit `BF` vanishes off `K` in the base slot.
    ############################################################################### -/

/-- **★ OFF-`K` VANISHING of the field-`pd` (base slot).**  For a base point `z ∉ K`, the gated witness
    `x' ↦ vanVleckGatedWitness … x' z` is identically `0` (the base gate `gatedKernel … (Or.inl hz)`
    kills the whole kernel), so its field-`pd` `witnessFieldDeriv` vanishes at every field point `p`.
    Unconditional. -/
theorem witnessFieldDeriv_eqZero_of_base_notMem_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (hz : z ∉ K) (p : Point n) :
    witnessFieldDeriv g gi hC hK S a b i τ p z = 0 := by
  have hfun : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext x'
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDeriv
  rw [hfun]
  exact pd_const 0 i p

/-- **★★ OFF-`K` VANISHING of the field-Hessian CLM (base slot).**  For `z ∉ K`, the field-derivative
    kernel `y ↦ witnessFieldDeriv … y z` is identically `0`, so its Fréchet derivative — the
    field-Hessian the envelope bounds — vanishes at every `x`. -/
theorem witnessFieldHessian_fderiv_eqZero_of_base_notMem_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (hz : z ∉ K) (x : Point n) :
    fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 := by
  have hfun : (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z)
      = (fun _ : Point n => (0 : ℝ)) := by
    funext y
    exact witnessFieldDeriv_eqZero_of_base_notMem_K g gi hC hK S a b i τ z hz y
  rw [hfun]
  exact fderiv_const_apply (0 : ℝ)

/-- **★ THE EXPLICIT `BF` VANISHES OFF `K`.**  For `z ∉ K`, the J4-865 explicit envelope
    `BF s z = ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖` is `0` (every field-Hessian norm is
    `‖0‖ = 0`, and `⨆` of the zero function is `0`).  Hence `BF` is supported in `K`. -/
theorem BF_ciSup_eqZero_of_base_notMem_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n) (hz : z ∉ K) :
    (⨆ x : Point n, ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖) = 0 := by
  have hpt : ∀ x : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ = 0 := by
    intro x
    rw [witnessFieldHessian_fderiv_eqZero_of_base_notMem_K g gi hC hK S a b i τ z hz x, norm_zero]
  simp only [hpt]
  exact ciSup_const

/-- **★ COMPACT SUPPORT of the `z`-mass integrand.**  With `BF` the explicit J4-865 envelope, the
    product dominator `z ↦ BL s z · BF s z` is supported in the COMPACT `K`: off `K` the `BF` factor is
    `0`.  So `∫z BL·BF` is a compact-support integral — the concrete payoff of the explicit `BF` for
    both `hbint` (integrability) and the `z`-mass estimate. -/
theorem productEnvelope_support_subset_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (BL : ℝ → Point n → ℝ) (s : ℝ) :
    Function.support (fun z => BL s z *
      (⨆ x : Point n, ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)) ⊆ K := by
  intro z hz
  by_contra hzK
  apply hz
  simp only [Function.mem_support] at hz ⊢
  rw [BF_ciSup_eqZero_of_base_notMem_K g gi hC hK S a b i τ z hzK, mul_zero]

/-! ###############################################################################
    ### THE GAUSSIAN-ENVELOPE MASS-ONE REDUCTION of `hzmass`.
    ############################################################################### -/

/-- **★ THE MASS-ONE REDUCTION of `hzmass`.**  The `z`-mass bound `∫z BL·BF ≤ C·(t−s)⁻¹` reduces to a
    POINTWISE Gaussian-in-`z` envelope on the PRODUCT: given, a.e. `s ∈ uIoc 0 (t−εₘ)`,
      • `0 < t − s`,
      • integrability of `z ↦ BL s z · BF s z`,
      • the pointwise bound `BL s z · BF s z ≤ C·(t−s)⁻¹·gaussDdim (t−s) z` for all `z`,
    the conclusion follows by `integral_mono` against the envelope, whose integral is
    `C·(t−s)⁻¹·∫ gaussDdim (t−s) = C·(t−s)⁻¹` (`gaussDdim_mass_one`).  The `(t−s)⁻¹` prefactor is thus
    made an EXPLICIT feature of the pointwise envelope — the natural target for the concrete `⨆`-form
    `BF`.  `BF` is a free parameter here (the reduction is envelope-agnostic); wired to the explicit
    J4-865 `BF s z := ⨆ x, ‖fderiv …‖` downstream. -/
theorem hzmass_of_gaussian_product_envelope
    (t : ℝ) (m : ℕ) (C : ℝ) (BL BF : ℝ → Point n → ℝ)
    (hCnn : 0 ≤ C)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s)
    (hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => BL s z * BF s z) volume)
    (henv : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n, BL s z * BF s z ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ z, BL s z * BF s z) ≤ C * (t - s)⁻¹ := by
  filter_upwards [hpos, hint, henv] with s hposs hints henvs hsUioc
  have hts : 0 < t - s := hposs hsUioc
  have hints := hints hsUioc
  have henvs' := henvs hsUioc
  -- the envelope `z ↦ C·(t−s)⁻¹·gaussDdim (t−s) z` is integrable and has integral `C·(t−s)⁻¹`.
  have hgint : Integrable (fun z : Point n => gaussDdim (t - s) z) volume :=
    gaussDdim_integrable' (t - s) hts
  have henvint : Integrable (fun z : Point n => C * (t - s)⁻¹ * gaussDdim (t - s) z) volume :=
    hgint.const_mul (C * (t - s)⁻¹)
  have hmono : (∫ z, BL s z * BF s z) ≤ ∫ z : Point n, C * (t - s)⁻¹ * gaussDdim (t - s) z :=
    integral_mono hints henvint henvs'
  have hval : (∫ z : Point n, C * (t - s)⁻¹ * gaussDdim (t - s) z) = C * (t - s)⁻¹ := by
    rw [integral_const_mul, gaussDdim_mass_one (t - s) hts, mul_one]
  rwa [hval] at hmono

/-! ###############################################################################
    ### NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity of the mass-one reduction.**  The two GENUINELY-CHOSEN antecedents (`hint`, `henv`)
    are jointly inhabited at the zero envelope `BL·BF ≡ 0`: it is integrable, and `0 ≤ C·(t−s)⁻¹·
    gaussDdim (t−s) z` (nonnegativity of `C`, of `(t−s)⁻¹` on the positive window, and of the Gaussian),
    yielding `∫z 0 = 0 ≤ C·(t−s)⁻¹`.  The window-positivity `hpos` is a property of `(t,m)` (not a
    chosen datum), so it is carried as a hypothesis — this exhibits satisfiability without asserting a
    false window fact.  No J4-548/847-style unsatisfiable antecedent. -/
theorem hzmass_gaussian_reduction_nonvacuous {n : ℕ} (t : ℝ) (m : ℕ) (C : ℝ) (hCnn : 0 ≤ C)
    (hpos : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 < t - s) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        (∫ _z : Point n, (0 : ℝ) * 0) ≤ C * (t - s)⁻¹ := by
  have hint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n => (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z) volume := by
    refine ae_of_all _ (fun s _ => ?_)
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have henv : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, (fun _ _ => (0 : ℝ)) s z * (fun _ _ => (0 : ℝ)) s z
        ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z := by
    filter_upwards [hpos] with s hposs hs
    intro z
    have hts : 0 < t - s := hposs hs
    have hnn : (0 : ℝ) ≤ C * (t - s)⁻¹ * gaussDdim (t - s) z :=
      mul_nonneg (mul_nonneg hCnn (le_of_lt (inv_pos.mpr hts))) (gaussDdim_nonneg' (t - s) z)
    simpa using hnn
  have h := hzmass_of_gaussian_product_envelope (n := n) t m C
    (fun _ _ => 0) (fun _ _ => 0) hCnn hpos hint henv
  filter_upwards [h] with s hs hsU
  exact hs hsU

end QIQTH.HZMassIntegrabilityAttempt

section AxiomChecks
open QIQTH.HZMassIntegrabilityAttempt
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witnessFieldDeriv_eqZero_of_base_notMem_K
#print axioms witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
#print axioms BF_ciSup_eqZero_of_base_notMem_K
#print axioms productEnvelope_support_subset_K
#print axioms hzmass_of_gaussian_product_envelope
#print axioms hzmass_gaussian_reduction_nonvacuous
end AxiomChecks
