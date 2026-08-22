/-
  ExpInverseMetricGauge — the EXACT inverse-metric radial identity for the exp-pullback metric `g̃`
  (corrected-`hpull` program, item (2); a sub-brick of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This file discharges item (2) of the
  corrected-`hpull` program: the EXACT inverse-metric identity `g̃(x)⁻¹ · g_p · x = x` (near `0`),
  the inverse companion of item (1)'s forward Gauss germ `g̃(x) · x = g_p · x`
  (`GaussInteriorMVTGeneral.hGauss_pullback_general_concrete`).  Nothing here builds normal
  coordinates, moves numerical-G, or closes `a₁ = R/6`.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHY THIS IS THIN ALGEBRA (matrix-inverse API + index bookkeeping, not new analysis)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Item (1) delivers the forward Gauss germ (no `g_p = I` gauge), which in operator form is
    `matToCLM (g̃ x) · x = matToCLM (g_p) · x`   near `0`.
  Near `0` the pullback-metric operator `matToCLM (g̃ x)` is a UNIT: at `x = 0` it equals
  `matToCLM (g_p)`, a unit (`metricCLMUnit0`); `x ↦ matToCLM (g̃ x)` is continuous (its entries are
  `C²`, `contDiffAt2_expPullbackMetric_zero`); and the units of a Banach algebra form an OPEN set
  (`Units.isOpen`).  So applying `Ring.inverse (matToCLM (g̃ x))` to both sides of the forward Gauss
  identity gives, near `0`,
    `Ring.inverse (matToCLM (g̃ x)) · (matToCLM (g_p) · x) = x`,
  i.e. `g̃(x)⁻¹ · g_p · x = x`.  No new analytic content — a one-step un-inversion of item (1).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERED (fully derived, axiom-free, no `sorry`)
  ─────────────────────────────────────────────────────────────────────────────────────────────
   • I0  `clm_apply_eq_sum` — the basis-expansion identity `T w μ = ∑ j, (T eⱼ)_μ · wⱼ` for a CLM `T`
       (the entry-to-action bridge used to pass between operator and component forms).
   • I1  `expPullbackMetric_isUnit_nhds_zero` — `∀ᶠ x in 𝓝 0, IsUnit (matToCLM (g̃ x))`, from
       continuity at `0` + `metricCLMUnit0` + `Units.isOpen`.
   • I2  `inverseMetric_gauss_operator` — the EXACT inverse-metric identity in operator form:
       `∀ᶠ x in 𝓝 0, Ring.inverse (matToCLM (g̃ x)) (matToCLM (g_p) x) = x`.
   • I3  `inverseMetric_gauss_general` — item (2) in component form:
       `∀ μ, (fun x => ∑ j, g̃⁻¹(x)_{μj} · (∑ b, g_p(j,b)·x^b)) =ᶠ[𝓝 0] (fun x => x^μ)`,
       with `g̃⁻¹ = expPullbackMetricInv`.
   • I4  `inverseMetric_gauss_gauge_of_general` — REGRESSION: under `g_p = I` the identity collapses to
       the clean inverse radial gauge `∑ j, g̃⁻¹(x)_{μj}·x^j =ᶠ[𝓝 0] x^μ` — the exp-pullback analog of
       `CurvedCenterIdentities.curvedRNCInv_radialGauge` / `RadialNormalCoordinateGauge.invGauge`.

  NET: item (2) of the corrected-`hpull` program is delivered.  This is STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.PullbackMetric
import QIQTH.GaussInteriorMVTGeneral

namespace QIQTH.ExpInverseMetricGauge

open QIQTH.Curvature QIQTH.ExpMap QIQTH.PullbackMetric QIQTH.GaussInteriorMVTGeneral
open Finset Topology Filter

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### I0 — the basis-expansion bridge between a CLM's entries and its action. -/

/-- **I0 — `clm_apply_eq_sum`.**  For a continuous linear map `T : Point n →L[ℝ] Point n`, its action on
    a vector `w` reads off its "columns" `T eⱼ`:
      `(T w)_μ = ∑ j, (T (Pi.single j 1))_μ · w j`.
    Standard basis expansion `w = ∑ j, w j • eⱼ` pushed through linearity.  ⚠ NOT a₁ = R/6. -/
theorem clm_apply_eq_sum (T : Point n →L[ℝ] Point n) (w : Point n) (μ : Fin n) :
    T w μ = ∑ j, (T (Pi.single j (1 : ℝ)) μ) * w j := by
  have hw : w = ∑ j, w j • (Pi.single j (1 : ℝ) : Point n) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [hw]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### I1 — the pullback-metric operator is a unit near `0`. -/

/-- **I1 — `expPullbackMetric_isUnit_nhds_zero`.**  Near `0` the pullback-metric operator
    `matToCLM (g̃ x)` is a UNIT.  At `x = 0` it equals `matToCLM (g_p)`, a unit (`metricCLMUnit0`, using
    the base-metric nondegeneracy `hinv`); `x ↦ matToCLM (g̃ x)` is continuous at `0` (its entries are
    `C²`, `contDiffAt2_expPullbackMetric_zero`); and units of a Banach algebra are OPEN (`Units.isOpen`).
    ⚠ NOT a₁ = R/6. -/
theorem expPullbackMetric_isUnit_nhds_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) :
    ∀ᶠ x in 𝓝 (0 : Point n),
      IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) := by
  -- continuity at `0` of the operator field (entries are `C²`).
  have hmet_diff : DifferentiableAt ℝ
      (fun x => matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) 0 := by
    show DifferentiableAt ℝ
      (fun x => ∑ a, ∑ b, expPullbackMetric g gi hC p x a b • elemCLM a b) 0
    apply DifferentiableAt.fun_sum
    intro a _
    apply DifferentiableAt.fun_sum
    intro b _
    exact ((contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).differentiableAt
      (by norm_num)).smul (differentiableAt_const _)
  have hcont : ContinuousAt
      (fun x => matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) 0 :=
    hmet_diff.continuousAt
  -- the value at `0` is a unit.
  have h0unit : IsUnit (matToCLM (fun a b => expPullbackMetric g gi hC p (0 : Point n) a b)) :=
    (metricCLMUnit0 g gi hC p hinv).isUnit
  -- units are an open neighbourhood; pull back through continuity.
  exact hcont (Units.isOpen.mem_nhds h0unit)

/-! ### I2 — the EXACT inverse-metric identity in operator form. -/

/-- **I2 — `inverseMetric_gauss_operator`.**  The exact inverse-metric radial identity in operator
    form: near `0`,
      `Ring.inverse (matToCLM (g̃ x)) (matToCLM (g_p) x) = x`.
    Derivation (item (2) crux): the forward Gauss germ (item (1),
    `hGauss_pullback_general_concrete`) gives `matToCLM (g̃ x) x = matToCLM (g_p) x` near `0`; near `0`
    `matToCLM (g̃ x)` is a unit (I1); apply `Ring.inverse (matToCLM (g̃ x))` to both sides and cancel via
    `Ring.inverse_mul_cancel`.  ⚠ NOT a₁ = R/6. -/
theorem inverseMetric_gauss_operator
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) :
    ∀ᶠ x in 𝓝 (0 : Point n),
      Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))
          (matToCLM (fun a b => g p a b) x) = x := by
  -- forward Gauss germ (item (1)), collected over all indices `i`.
  have hgauss : ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => ∑ b, g p i b * x b) :=
    hGauss_pullback_general_concrete g gi hC hsymm hinv hg p
  have hgaussAll : ∀ᶠ x in 𝓝 (0 : Point n), ∀ i,
      (∑ j, expPullbackMetric g gi hC p x i j * x j) = ∑ b, g p i b * x b :=
    eventually_all.mpr hgauss
  -- IsUnit near `0` (I1, using the base-metric nondegeneracy at `p`).
  have hunit := expPullbackMetric_isUnit_nhds_zero g gi hC p (hinv p) hg
  filter_upwards [hgaussAll, hunit] with x hg' hu
  -- operator form of the forward Gauss identity: `matToCLM (g̃ x) x = matToCLM (g_p) x`.
  have hvec : matToCLM (fun a b => expPullbackMetric g gi hC p x a b) x
      = matToCLM (fun a b => g p a b) x := by
    funext i
    rw [matToCLM_apply, matToCLM_apply]
    exact hg' i
  -- apply the operator inverse and cancel.
  calc Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))
          (matToCLM (fun a b => g p a b) x)
      = Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))
          (matToCLM (fun a b => expPullbackMetric g gi hC p x a b) x) := by rw [hvec]
    _ = (Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))
          * matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) x := by
            rw [ContinuousLinearMap.mul_apply]
    _ = (1 : Point n →L[ℝ] Point n) x := by rw [Ring.inverse_mul_cancel _ hu]
    _ = x := ContinuousLinearMap.one_apply x

/-! ### I3 — item (2): the EXACT inverse-metric identity in component form. -/

/-- **I3 — `inverseMetric_gauss_general`.**  Item (2) of the corrected-`hpull` program: the exact
    inverse-metric radial identity in component form — near `0`,
      `∀ μ, ∑ j, g̃⁻¹(x)_{μj} · (∑ b, g_p(j,b)·x^b) = x^μ`,
    with `g̃⁻¹ = expPullbackMetricInv`.  The inverse companion of item (1)'s forward Gauss germ
    `∑ j, g̃(x)_{ij}·x^j = ∑ b, g_p(i,b)·x^b`.  Derived from the operator form I2 by the basis expansion
    `clm_apply_eq_sum` and `expPullbackMetricInv`/`matToCLM_apply`.  Surviving hypotheses: ONLY the
    metric geometry `hsymm/hinv/hg`; NO base gauge `g_p = I`.  ⚠ NOT a₁ = R/6. -/
theorem inverseMetric_gauss_general
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) (μ : Fin n) :
    (fun x => ∑ j, expPullbackMetricInv g gi hC p x μ j * (∑ b, g p j b * x b))
      =ᶠ[𝓝 (0 : Point n)] (fun x => x μ) := by
  filter_upwards [inverseMetric_gauss_operator g gi hC hsymm hinv hg p] with x hx
  -- rewrite the component sum as the operator action, then use I2.
  have hstep : (∑ j, expPullbackMetricInv g gi hC p x μ j * (∑ b, g p j b * x b))
      = Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))
          (matToCLM (fun a b => g p a b) x) μ := by
    rw [clm_apply_eq_sum (Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)))
          (matToCLM (fun a b => g p a b) x) μ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [matToCLM_apply]
    rfl
  rw [hstep, hx]

/-! ### I4 — regression: the clean inverse radial gauge under `g_p = I`. -/

/-- **I4 — `inverseMetric_gauss_gauge_of_general`.**  REGRESSION / consistency check: under the base
    gauge `g_p = I` (`hgauge`), item (2) collapses to the clean inverse radial gauge
      `∀ μ, ∑ j, g̃⁻¹(x)_{μj}·x^j =ᶠ[𝓝 0] x^μ`,
    the exp-pullback analog of `CurvedCenterIdentities.curvedRNCInv_radialGauge` and
    `RadialGaugeInterface.RadialNormalCoordinateGauge.invGauge`.  Confirms I3 strictly generalizes the
    base-normalized inverse radial gauge — `g_p = I` is a statement normalization only.  ⚠ NOT a₁ = R/6. -/
theorem inverseMetric_gauss_gauge_of_general
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) (μ : Fin n) :
    (fun x => ∑ j, expPullbackMetricInv g gi hC p x μ j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x μ) := by
  filter_upwards [inverseMetric_gauss_general g gi hC hsymm hinv hg p μ] with x hx
  rw [← hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- collapse `∑ b, g_p(j,b)·x^b = x^j` under `g_p = I`.
  have hcollapse : (∑ b, g p j b * x b) = x j := by
    rw [Finset.sum_congr rfl (fun b _ => by rw [hgauge j b] :
        ∀ b ∈ (Finset.univ : Finset (Fin n)), g p j b * x b = (if j = b then 1 else 0) * x b)]
    simp [Finset.sum_ite_eq]
  rw [hcollapse]

end QIQTH.ExpInverseMetricGauge

section AxiomChecks
open QIQTH.ExpInverseMetricGauge
#print axioms clm_apply_eq_sum
#print axioms expPullbackMetric_isUnit_nhds_zero
#print axioms inverseMetric_gauss_operator
#print axioms inverseMetric_gauss_general
#print axioms inverseMetric_gauss_gauge_of_general
end AxiomChecks
