/-
  CensusCovSubballMeasurable — the two ROUTINE glue items of the modulo-G2 `hballrate` (C1) closure
  attempt flagged by gpt-5.6-sol (high) in the J4-955 re-audit:
    (1) a RESTRICTED change of variables over a sub-ball `ball 0 δ` (`δ ≤ D.ρ`), generalizing the
        `D.ρ`-hardcoded `commonWitness_cov` (J4-943);
    (2) MEASURABILITY of the CoV image set `Wbv '' (ball 0 δ)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure STRUCTURAL / MEASURE-THEORY glue brick sitting on top of the common-witness monolith
  `BaseVaryingIFTData` (J4-943) and the banked chart Gaussian change of variables
  (`chart_gaussian_change_variables`).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## CONTEXT (the J4-955 modulo-G2 residual glue).  The re-audit established that UNCONDITIONAL
  arbitrary-`S` `hballrate` is a genuine NO-GO (the gate indicator destroys the center-Lipschitz
  cancellation), but the MODULO-G2 path is analytically within reach of banked infra
  (`censusTauDeriv_eq_onGate_on_jointGate_ball`, `commonWitness_cov`, `two_term_census_bound_superset`,
  `commonWitness_image_sandwich`) modulo exactly three residual glue items.  This file closes the two
  ROUTINE ones (glue (1) and glue (2)); glue (3) — G2-threading + UNIFORM transported constants over
  the `(s, τ)` rectangle — is a substantial multi-part sub-assembly and is NOT in this file.

  ## WHY GLUE (1) IS ROUTINE.  `commonWitness_cov` (J4-943) states the base-slot Gaussian CoV over
  `ball 0 D.ρ` by feeding `chart_gaussian_change_variables` the structure's IFT facts (`D.hderiv`,
  `D.hinj`, `D.hleftInv`, `D.hdetPos`) at radius `D.ρ`.  `chart_gaussian_change_variables` is itself
  PARAMETERIZED by an arbitrary measurable domain `S`, so restricting to a sub-ball `ball 0 δ`
  (`δ ≤ D.ρ`) needs only the SAME facts restricted along `ball 0 δ ⊆ ball 0 D.ρ`
  (`Metric.ball_subset_ball hδ`) — `HasFDerivWithinAt.mono`, `Set.InjOn.mono`, and pointwise
  restriction.  The CoV identity holds pointwise, so restricting the integration domain is a
  set-restriction of an already-true statement.

  ## WHY GLUE (2) IS ROUTINE.  On `ball 0 D.ρ` the base chart `Wbv z = uniformInverseChart … z 0` is
  C¹ (hence continuous, from `D.hderiv`) and INJECTIVE (`D.hinj`); `Point n = Fin n → ℝ` is a Polish
  Borel space.  So the Lusin–Souslin theorem `MeasurableSet.image_of_continuousOn_injOn` applies to the
  measurable sub-ball `ball 0 δ`, giving `MeasurableSet (Wbv '' (ball 0 δ))` outright — no openness /
  open-map argument needed (though the image IS open, measurability is all the two-term superset bound
  `two_term_census_bound_superset`'s `hΩ` slot requires).

  ## WHAT LANDS.
    • `commonWitness_cov_subball` — ★★ the RESTRICTED base-slot Gaussian CoV over `ball 0 δ` for any
        `δ ≤ D.ρ` (glue (1)), about the SAME `D.V` and canonical `fderiv ℝ Wbv` as `commonWitness_cov`.
    • `commonWitness_image_measurable` — ★★ measurability of the CoV image `Wbv '' (ball 0 δ)` for any
        `δ ≤ D.ρ` (glue (2)), via Lusin–Souslin.
    • `commonWitness_cov_subball_of_geometry` — UNCONDITIONAL non-vacuity of glue (1): the restricted
        CoV holds for a geometry-produced `D` at a genuine positive sub-radius `δ = D.ρ / 2`.
    • `commonWitness_image_measurable_of_geometry` — UNCONDITIONAL non-vacuity of glue (2).

  ## HONEST STATUS (blunt; the modulo-G2 `hballrate` residual after this brick).  This file closes glue
  (1) and glue (2) of the modulo-G2 `hballrate` closure.  It does NOT close `hballrate` (C1) or
  `hCensusBound`/`hCross`, and it discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}`.  Glue (3)
  REMAINS and is NOT a single routine lemma: it comprises (a) the CoV two-term FOLD (rewriting
  `poly (Wbv (V w)) = poly w` on the image via `commonWitness_weightMatch`, then matching the exact
  `two_term_census_bound_superset` integrand shape), (b) the truncation / GLOBAL measurability of the
  transported weights `q₁, q₂` (which the superset bound requires globally, while the transport delivers
  regularity only on `ball 0 σ'`), and (c) UNIFORM transported constants `L, M₁, M₂` over the compact
  `(s, τ)` rectangle (`s ∈ Ioo (u-ε) u`, `τ = a - s ∈ (0, τ₀]`), which itself needs a uniform positive
  lower bound on `|det (fderiv Wbv (V ·))|` and uniform-in-`s` bounded+Lipschitz `F`-regularity — genuine
  estimates beyond G2.  So the FULL modulo-G2 `hballrate` is NOT assembled here.  `hDuhamel`/`hDConv`
  remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseVaryingIFTCommonWitness
import QIQTH.ChartGaussianChangeVar

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatResidualBound
open QIQTH.BaseVaryingIFTCommonWitness
open scoped Topology BigOperators

namespace QIQTH.CensusCovSubballMeasurable

variable {n : ℕ}

set_option maxHeartbeats 1600000

variable {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K}

/-! ###############################################################################
    ### §1 — GLUE (1): the RESTRICTED base-slot Gaussian CoV over `ball 0 δ`.
    ############################################################################### -/

/-- **★★ `commonWitness_cov_subball` — the RESTRICTED base-slot Gaussian change of variables.**  For the
    ONE common-witness `D`, any sub-radius `δ ≤ D.ρ`, any `τ` and weight `B`:
        `∫ z in ball 0 δ, gauss τ (Wbv z) · B z
           = ∫ w in Wbv '' (ball 0 δ), gauss τ w · (B (D.V w) / |det (fderiv Wbv (D.V w))|)`.
    Generalizes `commonWitness_cov` (J4-943), which is hardcoded at `D.ρ`, to any sub-ball — the exact
    domain the on-gate inner-ball census integral occupies (`ball 0 δ ⊆ ball 0 D.ρ`).  Proof:
    `chart_gaussian_change_variables` at domain `ball 0 δ`, with the structure IFT facts restricted along
    `ball 0 δ ⊆ ball 0 D.ρ` (`HasFDerivWithinAt.mono`, `Set.InjOn.mono`, pointwise).  NOT `a₁ = R/6`. -/
theorem commonWitness_cov_subball (D : BaseVaryingIFTData g gi hC hK) (δ : ℝ) (hδ : δ ≤ D.ρ)
    (τ : ℝ) (B : Point n → ℝ) :
    (∫ z in Metric.ball (0 : Point n) δ,
        gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z)
      = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ),
          gaussDdim τ w * (B (D.V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) := by
  have hsub : Metric.ball (0 : Point n) δ ⊆ Metric.ball (0 : Point n) D.ρ :=
    Metric.ball_subset_ball hδ
  refine QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball (0 : Point n) δ) (fun z => uniformInverseChart g gi hC hK z 0) D.V
    (fun z => fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z)
    (fun z => |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|) B
    measurableSet_ball ?_ ?_ ?_ (fun _ _ => rfl) ?_
  · -- within-derivative field on `ball 0 δ`, restricted from `D.hderiv` on `ball 0 D.ρ`.
    intro z hz
    exact (D.hderiv z (hsub hz)).mono hsub
  · -- injectivity on `ball 0 δ`.
    exact D.hinj.mono hsub
  · -- left inverse on `ball 0 δ`.
    intro z hz
    exact D.hleftInv z (hsub hz)
  · -- positive Jacobian on `ball 0 δ`.
    intro z hz
    exact D.hdetPos z (hsub hz)

/-! ###############################################################################
    ### §2 — GLUE (2): measurability of the CoV image `Wbv '' (ball 0 δ)`.
    ############################################################################### -/

/-- **★★ `commonWitness_image_measurable` — measurability of the CoV image set.**  For the common-witness
    `D` and any sub-radius `δ ≤ D.ρ`, the CoV image `Wbv '' (ball 0 δ)` is measurable.  From the
    Lusin–Souslin theorem (`MeasurableSet.image_of_continuousOn_injOn`): `Wbv` is continuous on the ball
    (`D.hderiv` ⟹ `ContinuousWithinAt`) and injective (`D.hinj`), and `Point n = Fin n → ℝ` is a Polish
    Borel space.  This is exactly the `hΩ` (measurable superset) slot the two-term superset bound
    `two_term_census_bound_superset` requires for `Ω := Wbv '' (ball 0 δ)`.  NOT `a₁ = R/6`. -/
theorem commonWitness_image_measurable (D : BaseVaryingIFTData g gi hC hK) (δ : ℝ) (hδ : δ ≤ D.ρ) :
    MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ)) := by
  have hsub : Metric.ball (0 : Point n) δ ⊆ Metric.ball (0 : Point n) D.ρ :=
    Metric.ball_subset_ball hδ
  refine MeasurableSet.image_of_continuousOn_injOn measurableSet_ball ?_ (D.hinj.mono hsub)
  -- `ContinuousOn Wbv (ball 0 δ)` from the within-derivative field (restricted).
  intro z hz
  exact ((D.hderiv z (hsub hz)).continuousWithinAt).mono hsub

/-! ###############################################################################
    ### §3 — UNCONDITIONAL non-vacuity (both glue items hold from the standing geometry).
    ############################################################################### -/

/-- **Non-vacuity of glue (1) — the restricted CoV holds from the standing geometry.**  Discharging the
    `BaseVaryingIFTData` antecedent via `baseVaryingIFTData_nonempty` (J4-943), the restricted base-slot
    CoV holds at a genuine positive sub-radius `δ = D.ρ / 2 < D.ρ` for the geometry-produced `D` — the
    antecedent is genuinely inhabitable.  NOT `a₁ = R/6`. -/
theorem commonWitness_cov_subball_of_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) (τ : ℝ) (B : Point n → ℝ) :
    ∃ (D : BaseVaryingIFTData g gi hC hK) (δ : ℝ), 0 < δ ∧ δ ≤ D.ρ ∧
      (∫ z in Metric.ball (0 : Point n) δ,
          gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ),
            gaussDdim τ w * (B (D.V w)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (D.V w)).det|) := by
  obtain ⟨D⟩ := baseVaryingIFTData_nonempty g gi hC hK h0Kmem
  refine ⟨D, D.ρ / 2, by positivity [D.hρ], by linarith [D.hρ], ?_⟩
  exact commonWitness_cov_subball D (D.ρ / 2) (by linarith [D.hρ]) τ B

/-- **Non-vacuity of glue (2) — the image measurability holds from the standing geometry.**  As above,
    at `δ = D.ρ / 2`.  NOT `a₁ = R/6`. -/
theorem commonWitness_image_measurable_of_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ (D : BaseVaryingIFTData g gi hC hK) (δ : ℝ), 0 < δ ∧ δ ≤ D.ρ ∧
      MeasurableSet
        ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) δ)) := by
  obtain ⟨D⟩ := baseVaryingIFTData_nonempty g gi hC hK h0Kmem
  refine ⟨D, D.ρ / 2, by positivity [D.hρ], by linarith [D.hρ], ?_⟩
  exact commonWitness_image_measurable D (D.ρ / 2) (by linarith [D.hρ])

end QIQTH.CensusCovSubballMeasurable

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusCovSubballMeasurable
#print axioms commonWitness_cov_subball
#print axioms commonWitness_image_measurable
#print axioms commonWitness_cov_subball_of_geometry
#print axioms commonWitness_image_measurable_of_geometry
end AxiomChecks
