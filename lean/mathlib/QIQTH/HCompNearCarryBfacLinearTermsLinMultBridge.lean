/-
  HCompNearCarryBfacLinearTermsLinMultBridge — J4-1041: `nb`'s `Bfac` sum has FOUR summands
  (`HCompNearCarryKPrimeBaseFieldCoV.lean`, J4-1010, BRICK 1):
      `Bfac(z) := Levi(s,z)·(hsMixed·A + grⱼ·∂ⱼA + grᵢ·∂ᵢA + ∂ⱼ∂ᵢA)`.
  All of this session's `nb`-term1 work (J4-1017–1028) targeted ONLY `hsMixed·A`, terminating in the
  confirmed-hard `hxmem` wall (J4-1032–1034).  THIS FILE investigates the OTHER THREE summands
  (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) and finds their DOWNSTREAM cancellation/regularity sub-problem is
  structurally CHEAPER than term1's — though `hxmem` remains an equally-shared UPSTREAM gate for all
  four summands (it is needed merely to invoke BRICK 1's factorization pointwise at all, prerequisite
  to `hfac`'s discharge over any change-of-variables domain — NOT specific to any one summand's inner
  algebra).  Sol (`gpt-5.6-sol`, high, 2026-08-23) plan-reviewed and GO-confirmed this diagnosis and
  the banking plan BEFORE any Lean was written.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FINDING.
  Writing `G := gaussDdim τ v`, `τ := t−s`, `v := U := uniformInverseChart … z x`:
    • `grⱼ := −⟨v,PJ⟩/(2τ)`, multiplying `∂ⱼA`.  Since `linMult τ Q v := (⟨v,Q⟩/(2τ))·G`
      (ALREADY BANKED, `HCompNearCarryTerm1LipschitzCancellation.linMult`, J4-1019), we get, by BARE
      UNFOLDING (`ring`, no new algebra):
          `G·(grⱼ·∂ⱼA) = −(linMult τ PJ v)·∂ⱼA`  LITERALLY.
      Term2 is therefore a DIRECT instance of the ALREADY-BANKED `linMult` machinery — its exact
      zero-integral (`integral_linMult_eq_zero`) and τ-INDEPENDENT Lipschitz-remainder payoff
      (`integral_linMult_mul_lipschitz`) apply VERBATIM, with NO NEED for `heatHessMult`'s
      second-moment cancellation machinery (which term1's `hsMixed` piece needed) — a genuinely
      SIMPLER sub-problem than term1's.
    • `grᵢ := −⟨v,PI⟩/(2τ)`, multiplying `∂ᵢA` — the SAME identification, index-swapped
      (`G·(grᵢ·∂ᵢA) = −(linMult τ PI v)·∂ᵢA`).
    • `∂ⱼ∂ᵢA` carries NO `gr`-type multiplier at all — `G·∂ⱼ∂ᵢA` is the "flat" `gaussDdim τ v · B(z)`
      shape with NO `1/τ` or `1/τ²` singularity to cancel as `τ → 0`.  It needs NO cancellation
      mechanism whatsoever: a bare pointwise bound on `∂ⱼ∂ᵢA` (no Lipschitz needed) combined with the
      ALREADY-BANKED total-mass-one fact (`gaussDdim_mass_one`, `HeatResidualBound`/`GaussianHessianCancel`)
      gives an immediate `O(1)` bound — the CHEAPEST of all four summands.

  Sol (high, before Lean) confirmed: (a) this diagnosis is correct and non-circular; (b) the algebra is
  literally the bare unfolding of `linMult`'s definition, no hidden gap; (c) worth banking as standalone
  infrastructure EVEN THOUGH `hxmem` still gates final composition — exactly analogous to what
  J4-1024–1028 banked for term1 PRE-`hxmem`; (d) flagged that the full `chartFieldAmp`-derivative
  GLOBAL regularity chain (mirroring J4-1025–1027's port for `A` itself, one derivative order higher
  for `∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA`) is a SEPARATE, NOT-attempted-here effort (flagged as a possible API-level
  obstruction: `pd`/`PdiffAt` are 1-D-line `deriv`/`DifferentiableAt` objects, not `fderiv` coordinates,
  so porting `ContDiffAt ℝ 2 A → ContDiffAt ℝ 1 (pd A i)` may need an explicit bridge theorem, not
  attempted here).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It supplies
  ONLY the algebraic identification (terms 2/3 ≡ signed `linMult` instances) and the flat-shape bound
  (term 4), reusing ALREADY-BANKED `linMult`/`gaussDdim_mass_one` machinery with NO new asymptotic
  claim (no sympy check needed — pure algebra/composition, per standing task instructions). It does
  **NOT**:
    • discharge `hxmem` (the shared upstream gate for ALL FOUR of `Bfac`'s summands — UNCHANGED, still
      the confirmed-hard architectural wall; NOT attempted here);
    • discharge `hfac`'s literal carry over the IFT-selected domain `S'` (residuals r1/r2 of
      `HCompNearCarryKPrimeBaseFieldCoV`, UNCHANGED, untouched);
    • establish `∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA`'s own GLOBAL bound+Lipschitz regularity for the LITERAL
      `chartFieldAmp` (the abstract Lipschitz/boundedness hypotheses below are supplied ABSTRACTLY,
      exactly as J4-1019's abstract-`Amp` term1 payoff did before J4-1025–1028's later globalization
      chain; the analogous globalization for the derivative objects is NOT attempted here);
    • discharge `nb`, `hCConv`, or any part of `hcomp` — `Bfac`'s summands remain SEPARATELY open;
    • touch the far-carry `fb` (entirely separate, untouched).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeBaseFieldCoV
import QIQTH.HCompNearCarryTerm1LipschitzCancellation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open QIQTH.HCompNearCarryTerm1LipschitzCancellation
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. GENERIC identification — `Bfac`'s "gr"-type summands are signed `linMult` instances.
    ############################################################################### -/

/-- **★ `grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp` — the generic, parameter-free identity.**
    Writing `grTerm τ Q v := −(∑ k, v k * Q k) / (2 * τ)` (the literal shape of `Bfac`'s `grⱼ`/`grᵢ`
    coefficients, `HCompNearCarryKPrimeBaseFieldCoV` BRICK 1), for ANY `τ Q v : … / Point n` and ANY
    scalar `Amp : ℝ`:
        `gaussDdim τ v · ((−(∑ k, v k * Q k) / (2 * τ)) * Amp) = −(linMult τ Q v * Amp)`.
    Bare unfolding of `linMult`'s definition (`linMult τ Q v := (∑ k, v k*Q k)/(2τ)·gaussDdim τ v`,
    J4-1019) — pure `ring`, no hypothesis needed (Lean's field division is total). NOT `a₁ = R/6`. -/
theorem grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp
    (τ : ℝ) (Q v : Point n) (Amp : ℝ) :
    gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * Amp)
      = -(linMult τ Q v * Amp) := by
  simp only [linMult]; ring

/-! ###############################################################################
    ### 2. LITERAL specialization — matching `HCompNearCarryKPrimeBaseFieldCoV` BRICK 1 verbatim.
    ############################################################################### -/

/-- **★★ `kPrime_term2_grj_eq_neg_linMult_mul_partialjAmp` — LITERAL term2 identification.**
    The exact `grⱼ·∂ⱼA` sub-expression of BRICK 1's RHS (`HCompNearCarryKPrimeBaseFieldCoV`,
    J4-1010), multiplied by the common outer Gaussian `G`, equals `−linMult(τ,PJ,U)·∂ⱼA` LITERALLY —
    the SAME `U := uniformInverseChart g gi hC hK z x`, `PJ`, `A := chartFieldAmp …`, `τ := t−s` as
    BRICK 1's own signature. NOT `a₁ = R/6`. -/
theorem kPrime_term2_grj_eq_neg_linMult_mul_partialjAmp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (j : Fin n) (t s : ℝ) (x z : Point n)
    (PJ : Point n → Fin n → ℝ) :
    gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
        * ((-(∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (2 * (t - s)))
            * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x)
      = -(linMult (t - s) (PJ x) (uniformInverseChart g gi hC hK z x)
            * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x) :=
  grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp (t - s) (PJ x)
    (uniformInverseChart g gi hC hK z x) (pd (chartFieldAmp g gi hC hK a b (t - s) z) j x)

/-- **★★ `kPrime_term3_gri_eq_neg_linMult_mul_partialiAmp` — LITERAL term3 identification.**
    Index-swapped mirror of the above, for `grᵢ·∂ᵢA`. NOT `a₁ = R/6`. -/
theorem kPrime_term3_gri_eq_neg_linMult_mul_partialiAmp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t s : ℝ) (x z : Point n)
    (PI : Point n → Fin n → ℝ) :
    gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
        * ((-(∑ k, uniformInverseChart g gi hC hK z x k * PI x k) / (2 * (t - s)))
            * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x)
      = -(linMult (t - s) (PI x) (uniformInverseChart g gi hC hK z x)
            * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x) :=
  grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp (t - s) (PI x)
    (uniformInverseChart g gi hC hK z x) (pd (chartFieldAmp g gi hC hK a b (t - s) z) i x)

/-! ###############################################################################
    ### 3. THE LIPSCHITZ-REMAINDER PAYOFF — direct reuse of `integral_linMult_mul_lipschitz`.
    ############################################################################### -/

/-- **★★★ `grTerm_gaussian_mul_amp_lipschitz_bound` — the G1-analogue payoff for terms 2/3,
    DIRECTLY from the ALREADY-BANKED `linMult` machinery, with NO `heatHessMult` needed** (unlike
    term1's `hsMixed`, which needed BOTH `heatHessMult` and `linMult`).  For `τ > 0`, `Q : Point n`,
    a weight `f : Point n → ℝ` Lipschitz-at-`0` with modulus `L ≥ 0`:
        `|∫ v, gaussDdim τ v · ((−(∑ k, v k*Q k)/(2τ)) * f v)| ≤ n²·L·‖Q‖`.
    Route: rewrite the integrand pointwise via part 1's identity to `−(linMult τ Q v * f v)`, then
    `integral_neg` + the ALREADY-BANKED `integral_linMult_mul_lipschitz` (J4-1019). NOT `a₁ = R/6`. -/
theorem grTerm_gaussian_mul_amp_lipschitz_bound
    (τ : ℝ) (hτ : 0 < τ) (Q : Point n)
    (L : ℝ) (hL : 0 ≤ L) (f : Point n → ℝ) (hf : AEStronglyMeasurable f volume)
    (hlip : ∀ v : Point n, |f v - f 0| ≤ L * ‖v‖) :
    |∫ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * f v)|
      ≤ (n : ℝ) ^ 2 * L * ‖Q‖ := by
  have hpt : ∀ v : Point n, gaussDdim τ v * ((-(∑ k, v k * Q k) / (2 * τ)) * f v)
      = -(linMult τ Q v * f v) :=
    fun v => grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp τ Q v (f v)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_neg, abs_neg]
  exact integral_linMult_mul_lipschitz τ hτ Q L hL f hf hlip

/-! ###############################################################################
    ### 4. TERM 4 — the flat shape `∂ⱼ∂ᵢA`, needing NO cancellation at all.
    ############################################################################### -/

/-- **★★★ `flat_gaussian_mul_amp_bound` — the CHEAPEST of `Bfac`'s four summands.** `∂ⱼ∂ᵢA` carries
    NO `1/τ`-type multiplier, so `G·∂ⱼ∂ᵢA` is a bare `gaussDdim τ v · Amp v` product: for `τ > 0` and
    `Amp` merely BOUNDED (no Lipschitz needed at all, unlike every other summand), immediately
        `|∫ v, gaussDdim τ v · Amp v| ≤ M`,
    via the ALREADY-BANKED total-mass-one fact (`gaussDdim_mass_one`, `HeatResidualBound`). NOT
    `a₁ = R/6`. -/
theorem flat_gaussian_mul_amp_bound
    (τ : ℝ) (hτ : 0 < τ) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ v : Point n, |Amp v| ≤ M) :
    |∫ v : Point n, gaussDdim τ v * Amp v| ≤ M := by
  have hGnn : ∀ v : Point n, 0 ≤ gaussDdim τ v := fun v => gaussDdim_nonneg' τ v
  have hGint : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable' τ hτ
  have hD_int : Integrable (fun v : Point n => M * gaussDdim τ v) volume := hGint.const_mul _
  have hptbnd : ∀ v : Point n, |gaussDdim τ v * Amp v| ≤ M * gaussDdim τ v := fun v => by
    rw [abs_mul, abs_of_nonneg (hGnn v)]
    calc gaussDdim τ v * |Amp v| ≤ gaussDdim τ v * M := by
          exact mul_le_mul_of_nonneg_left (hbound v) (hGnn v)
      _ = M * gaussDdim τ v := by ring
  have hmeas : AEStronglyMeasurable (fun v : Point n => gaussDdim τ v * Amp v) volume :=
    hGint.aestronglyMeasurable.mul hAmp
  have hint : Integrable (fun v : Point n => gaussDdim τ v * Amp v) volume :=
    hD_int.mono' hmeas (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs]; exact hptbnd v))
  calc |∫ v : Point n, gaussDdim τ v * Amp v|
      ≤ ∫ v : Point n, |gaussDdim τ v * Amp v| := by
        have h := norm_integral_le_integral_norm (μ := (volume : Measure (Point n)))
          (fun v : Point n => gaussDdim τ v * Amp v)
        simpa only [Real.norm_eq_abs] using h
    _ ≤ ∫ v : Point n, M * gaussDdim τ v :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => abs_nonneg _))
          hD_int (Filter.Eventually.of_forall hptbnd)
    _ = M := by rw [integral_const_mul, gaussDdim_mass_one τ hτ, mul_one]

/-- **★★ `kPrime_term4_flat_bound` — LITERAL term4 identification + bound.** The exact
    `∂ⱼ∂ᵢA` sub-expression of BRICK 1's RHS, multiplied by the common outer Gaussian `G`, is the flat
    shape `flat_gaussian_mul_amp_bound` consumes directly (`Amp := fun z => pd (fun y => pd
    (chartFieldAmp …) i y) j x`, CONSTANT in the integration variable `v`, since `z` is what varies —
    here specialized at the pointwise value, matching BRICK1's literal sub-term). NOT `a₁ = R/6`. -/
theorem kPrime_term4_flat_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i j : Fin n) (t s : ℝ) (x z : Point n)
    (hts : 0 < t - s) (M : ℝ) (hM : 0 ≤ M)
    (hbound : |pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x| ≤ M) :
    gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
        * pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x
      ≤ gaussDdim (t - s) (uniformInverseChart g gi hC hK z x) * M := by
  have hGnn : 0 ≤ gaussDdim (t - s) (uniformInverseChart g gi hC hK z x) :=
    gaussDdim_nonneg' (t - s) (uniformInverseChart g gi hC hK z x)
  have hle : pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x ≤ M :=
    (abs_le.mp hbound).2
  exact mul_le_mul_of_nonneg_left hle hGnn

end QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
#print axioms grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp
#print axioms kPrime_term2_grj_eq_neg_linMult_mul_partialjAmp
#print axioms kPrime_term3_gri_eq_neg_linMult_mul_partialiAmp
#print axioms grTerm_gaussian_mul_amp_lipschitz_bound
#print axioms flat_gaussian_mul_amp_bound
#print axioms kPrime_term4_flat_bound
end AxiomChecks
