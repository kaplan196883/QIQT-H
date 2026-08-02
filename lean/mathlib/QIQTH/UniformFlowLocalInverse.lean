/-
  UniformFlowLocalInverse — J4-93: the OFF-DIAGONAL local inverse of the recentring chart
  `φ_q = uniformFlowExp g gi hC hK q`, discharging the two `Vmap`-side hypotheses that J4-92
  (`GlobalResidualWitness.lean`) carried as antecedents.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## The wall J4-92 hit, and how this file breaks it.

  J4-92's in-chart residual transport `heatOp_globalWitness_eq_recentred_inChart` (W2) and its bound
  `globalWitness_residual_bound_inChart` (W3) take the inverse chart map `Vmap` ABSTRACT and carry,
  as genuine antecedents at each in-chart base point `p = φ_q v` (`‖v‖ < r₀`):

    (h1)  `hgerm : (fun z => Vmap q (φ_q z)) =ᶠ[𝓝 v] id`   — the left-inverse germ, and
    (h2)  `ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q) (φ_q v)`
          — the `C²`-regularity of the transported witness `(χ·H₀(τ)) ∘ Vmap_q` at `φ_q v`, which is
          exactly the OFF-DIAGONAL `C²`-regularity of the inverse chart `Vmap_q = φ_q⁻¹`.

  J4-92's header declared (h2) an "infrastructure-scale local-diffeomorphism layer": in this repo the
  inverse chart's `C²`-regularity was known only at the single diagonal point `v = 0` (`p = q`).

  **This assessment was wrong.**  Mathlib's inverse function theorem discharges (h1)+(h2) directly at
  EVERY `v` with the two inputs J4-91 already provides on a uniform ball:
    * `contDiffAt2_uniformFlowExp`               — `ContDiffAt ℝ 2 φ_q v` for `‖v‖ < uniformFlowRadius`;
    * `uniformFlowExp_common_nondeg_radius`      — `IsUnit (fderiv ℝ φ_q v)` for `‖v‖ < ρ₀`.
  A unit `fderiv` is turned into the `ContinuousLinearEquiv` the IFT consumes via
  `ContinuousLinearEquiv.ofUnit`, and then `ContDiffAt.localInverse` / `.to_localInverse` /
  `HasStrictFDerivAt.eventually_left_inverse` produce the local inverse, its `C²`-regularity, and its
  left-inverse germ.

  ## Deliverables.
    * (I1) `uniformFlowExp_localInverse_exists` — the per-`(q,v)` local inverse `Vloc` with germ + `C²`.
    * (I2) `basepointInverseChart` (a SINGLE per-`q` inverse chart = the base-point IFT partial
      homeomorph's `symm`) together with `basepointInverseChart_germ` / `basepointInverseChart_contDiffAt`
      — germ + `C²` at EVERY `v` in a uniform ball, from ONE function per `q`.
    * (I3) `globalWitness_hypotheses_discharged` — packages (h1)+(h2) for the concrete witness.
    * (I4) `globalWitness_residual_bound_inChart_unconditional` — J4-92's W3 bound with (h1)+(h2)
      DISCHARGED: only geometric + heat-side hypotheses remain.

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  This is the in-chart
  discharge; it does NOT build the global (`∀ p`) zero-extension, so `hunif`/`hcoord` still gate the
  recenter capstone — NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PullbackNaturalityLocal
import QIQTH.UniformFlowNondegClose
import QIQTH.GlobalResidualWitness
import QIQTH.SmoothCutoff
import QIQTH.HeatParametrixAnsatz

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### I1 — the per-`(q,v)` off-diagonal local inverse via Mathlib's IFT. -/

/-- **I1 — the OFF-DIAGONAL local inverse of the recentring chart `φ_q = uniformFlowExp g gi hC hK q`.**

    There is a single radius `r₀ > 0` such that for every `q ∈ K` and every `v` with `‖v‖ < r₀`, the
    chart `φ_q` has a genuine local inverse `Vloc` at `v`:
      * `(fun z => Vloc (φ_q z)) =ᶠ[𝓝 v] id`   (the left-inverse germ), and
      * `ContDiffAt ℝ 2 Vloc (φ_q v)`.

    Proof: apply Mathlib's `ContDiffAt.localInverse` at `v`, whose two hypotheses are exactly J4-91's
    `contDiffAt2_uniformFlowExp` (`ContDiffAt ℝ 2 φ_q v`) and `uniformFlowExp_common_nondeg_radius`
    (`IsUnit (fderiv φ_q v)`, packaged into a `ContinuousLinearEquiv` via `ofUnit`).  The germ is
    `HasStrictFDerivAt.eventually_left_inverse`; the `C²` of `Vloc` is `ContDiffAt.to_localInverse`. -/
theorem uniformFlowExp_localInverse_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₀ > (0 : ℝ), ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      ∃ Vloc : Point n → Point n,
        (fun z => Vloc (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 Vloc (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨ρ₀, hρ₀pos, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  refine ⟨min ρ₀ (uniformFlowRadius g gi hC hK),
    lt_min hρ₀pos (uniformFlowRadius_pos g gi hC hK), ?_⟩
  intro q hq v hv
  have hvρ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvR : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv (min_le_right _ _)
  -- The two IFT inputs from J4-91.
  have hf : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) v :=
    contDiffAt2_uniformFlowExp g gi hC hK q hq v hvR
  have hUnit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnondeg q hq v hvρ
  -- The unit `fderiv` as a `ContinuousLinearEquiv`.
  set fe : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hUnit.unit with hfe
  have hcoe : (fe : Point n →L[ℝ] Point n) = fderiv ℝ (uniformFlowExp g gi hC hK q) v := by
    apply ContinuousLinearMap.ext
    intro x
    have h1 : (fe : Point n →L[ℝ] Point n) x = (hUnit.unit : Point n →L[ℝ] Point n) x := rfl
    rw [h1, hUnit.unit_spec]
  have hfd : HasFDerivAt (uniformFlowExp g gi hC hK q)
      (fderiv ℝ (uniformFlowExp g gi hC hK q) v) v :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hf' : HasFDerivAt (uniformFlowExp g gi hC hK q) (fe : Point n →L[ℝ] Point n) v := by
    rw [hcoe]; exact hfd
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  refine ⟨hf.localInverse hf' hn2, ?_, ?_⟩
  · -- germ from the strict-derivative left inverse.
    have hs := hf.hasStrictFDerivAt' hf' hn2
    filter_upwards [hs.eventually_left_inverse] with x hx
    exact hx
  · -- `C²` of the local inverse from `to_localInverse`.
    exact hf.to_localInverse hf' hn2

/-! ### I2 — a SINGLE per-`q` inverse chart valid on a whole ball (the base-point partial homeo). -/

/-- **I2 (existence) — one inverse-chart function per base point, valid on a uniform ball.**  Building
    Mathlib's IFT partial homeomorph `e` of `φ_q` at the DIAGONAL point `v = 0` gives a SINGLE function
    `W = e.symm` that is a genuine left inverse of `φ_q` and is `C²` at `φ_q v` for EVERY `v` in an open
    ball around `0`.  The germ at each such `v` comes from `e.source` being open (`eventually_left_inverse`);
    the `C²`-regularity comes from `OpenPartialHomeomorph.contDiffAt_symm` at the target point `φ_q v`,
    whose forward inputs (invertible `fderiv` + `C²` of `φ_q`) hold at `v` by J4-91 on the same ball. -/
theorem basepointChart_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∃ (W : Point n → Point n) (δ : ℝ), 0 < δ ∧ ∀ v : Point n, ‖v‖ < δ →
      (fun z => W (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) ∧
      ContDiffAt ℝ 2 W (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨ρ₀, hρ₀pos, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  set R := uniformFlowRadius g gi hC hK with hRdef
  have hRpos : 0 < R := uniformFlowRadius_pos g gi hC hK
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h0R : ‖(0 : Point n)‖ < R := by rw [norm_zero]; exact hRpos
  have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀pos
  -- base-point IFT data at `v = 0`.
  have hf0 : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) 0 :=
    contDiffAt2_uniformFlowExp g gi hC hK q hq 0 h0R
  have hU0 : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) 0) := hnondeg q hq 0 h0ρ
  set fe0 : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hU0.unit with hfe0
  have hcoe0 : (fe0 : Point n →L[ℝ] Point n) = fderiv ℝ (uniformFlowExp g gi hC hK q) 0 := by
    apply ContinuousLinearMap.ext; intro x
    have h1 : (fe0 : Point n →L[ℝ] Point n) x = (hU0.unit : Point n →L[ℝ] Point n) x := rfl
    rw [h1, hU0.unit_spec]
  have hf'0 : HasFDerivAt (uniformFlowExp g gi hC hK q) (fe0 : Point n →L[ℝ] Point n) 0 := by
    rw [hcoe0]; exact (hf0.differentiableAt (by norm_num)).hasFDerivAt
  set e := hf0.toOpenPartialHomeomorph (uniformFlowExp g gi hC hK q) hf'0 hn2 with hedef
  have hcoee : (⇑e : Point n → Point n) = uniformFlowExp g gi hC hK q := by
    rw [hedef]; exact hf0.toOpenPartialHomeomorph_coe hf'0 hn2
  have h0src : (0 : Point n) ∈ e.source := by
    rw [hedef]; exact hf0.mem_toOpenPartialHomeomorph_source hf'0 hn2
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.isOpen_iff.mp e.open_source 0 h0src
  refine ⟨(e.symm : Point n → Point n), min δ₁ (min ρ₀ R),
    lt_min hδ₁pos (lt_min hρ₀pos hRpos), ?_⟩
  intro v hv
  have hvδ₁ : ‖v‖ < δ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hvρ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvR : ‖v‖ < R := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvsrc : v ∈ e.source :=
    hδ₁sub (by rw [Metric.mem_ball, dist_zero_right]; exact hvδ₁)
  have hev : (⇑e) v = uniformFlowExp g gi hC hK q v := by rw [hcoee]
  refine ⟨?_, ?_⟩
  · -- germ: `e.source` is open, so the partial homeo's left inverse holds near `v`.
    filter_upwards [e.eventually_left_inverse hvsrc] with z hz
    rw [← hcoee]; exact hz
  · -- `C²` of `e.symm` at `φ_q v` from `contDiffAt_symm`.
    have htgt : uniformFlowExp g gi hC hK q v ∈ e.target := by
      rw [← hev]; exact e.map_source hvsrc
    have hsymmpt : (⇑e.symm) (uniformFlowExp g gi hC hK q v) = v := by
      rw [← hev]; exact e.left_inv hvsrc
    have hUv : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q) v) := hnondeg q hq v hvρ
    set fev : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hUv.unit with hfev
    have hcoev : (fev : Point n →L[ℝ] Point n) = fderiv ℝ (uniformFlowExp g gi hC hK q) v := by
      apply ContinuousLinearMap.ext; intro x
      have h1 : (fev : Point n →L[ℝ] Point n) x = (hUv.unit : Point n →L[ℝ] Point n) x := rfl
      rw [h1, hUv.unit_spec]
    have hfv : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) v :=
      contDiffAt2_uniformFlowExp g gi hC hK q hq v hvR
    have hf'v : HasFDerivAt (uniformFlowExp g gi hC hK q) (fev : Point n →L[ℝ] Point n) v := by
      rw [hcoev]; exact (hfv.differentiableAt (by norm_num)).hasFDerivAt
    apply e.contDiffAt_symm (f₀' := fev) htgt
    · rw [hsymmpt, hcoee]; exact hf'v
    · rw [hsymmpt, hcoee]; exact hfv

open Classical in
/-- **I2 (the named per-`q` inverse chart).**  A total inverse-chart function: on the base set it is the
    base-point IFT partial homeomorph's inverse (`basepointChart_exists`), off it the zero default. -/
noncomputable def basepointInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) : Point n → Point n → Point n :=
  fun q => if hq : q ∈ K then (basepointChart_exists g gi hC hK q hq).choose else fun _ => 0

/-- **I2 (spec).**  For `q ∈ K`, the named inverse chart `basepointInverseChart … q` is a genuine local
    left inverse of `φ_q` with `C²`-regularity, on a uniform ball. -/
theorem basepointInverseChart_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) :
    ∃ δ > (0 : ℝ), ∀ v : Point n, ‖v‖ < δ →
      (fun z => basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
          =ᶠ[nhds v] (fun z => z) ∧
      ContDiffAt ℝ 2 (basepointInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v) := by
  have hunfold : basepointInverseChart g gi hC hK q
      = (basepointChart_exists g gi hC hK q hq).choose := by
    simp only [basepointInverseChart, dif_pos hq]
  obtain ⟨δ, hδ, hspec⟩ := (basepointChart_exists g gi hC hK q hq).choose_spec
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  rw [hunfold]
  exact hspec v hv

/-! ### I3 — the two `Vmap`-side antecedents of J4-92, DISCHARGED. -/

/-- **I3 — J4-92's `Vmap`-side hypotheses `hgerm` + witness-`C²`, DISCHARGED for the concrete chart.**
    For `q ∈ K` there is `δ > 0` so that on `‖v‖ < δ` BOTH the left-inverse germ and the `C²`-regularity
    of the transported witness `(χ·H₀(τ)) ∘ Vmap_q` at `φ_q v` hold, where `Vmap = basepointInverseChart`.
    The germ is I2's; the witness `C²` is the composition of I2's `C²` inverse chart with the (smooth)
    profile `y ↦ radialCutoff a b y · heatParametrix 0 Θ u τ y`. -/
theorem globalWitness_hypotheses_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (τ : ℝ) (q : Point n) (hq : q ∈ K) :
    ∃ δ > (0 : ℝ), ∀ v : Point n, ‖v‖ < δ →
      (fun z => basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
          =ᶠ[nhds v] (fun z => z) ∧
      ContDiffAt ℝ 2
        (fun x => globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK) τ x q)
        (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨δ, hδ, hspec⟩ := basepointInverseChart_spec g gi hC hK q hq
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  obtain ⟨hgerm, hWc2⟩ := hspec v hv
  refine ⟨hgerm, ?_⟩
  -- the smooth radial-cutoff × parametrix profile is `C²` everywhere.
  have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 0 Θ u τ y)
      (basepointInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)) := by
    apply ContDiffAt.mul
    · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    · have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
          = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
        funext x; rw [heatParametrix_folded]; simp
      have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
        rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
      exact hH.contDiffAt.of_le le_top
  exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2

/-! ### I4 — J4-92's in-chart residual bound with the `Vmap`-side hypotheses discharged. -/

/-- **★ I4 — the in-chart per-base-point residual Gaussian bound, `Vmap`-hypotheses DISCHARGED.**
    J4-92's `globalWitness_residual_bound_inChart` (W3) restated for the CONCRETE inverse chart
    `basepointInverseChart`, with its two `Vmap`-side antecedents (`hgerm`, witness-`C²`) discharged by
    I3.  Only the genuine geometric far-point inputs (`g` `C¹`, nondegeneracy, two-sided metric inverse)
    remain as antecedents; the heat-side data is packaged in the hypotheses, and the single `(a,b,B)` is
    `τ`-free and uniform over `q ∈ K`. -/
theorem globalWitness_residual_bound_inChart_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
          IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
          (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
              * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
          (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
              * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdimWide τ v := by
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀W, hr₀W, hboundinner⟩ := hbound (basepointInverseChart g gi hC hK) τ q hq hτ
  obtain ⟨δ, hδ, hdisch⟩ :=
    globalWitness_hypotheses_discharged g gi hC hK Θ u a b hw0smooth τ q hq
  refine ⟨min r₀W δ, lt_min hr₀W hδ, ?_⟩
  intro v hv hg1 hU hGGi hGiG
  have hvW : ‖v‖ < r₀W := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδ : ‖v‖ < δ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hgerm, hf⟩ := hdisch v hvδ
  exact hboundinner v hvW hgerm hg1 hf hU hGGi hGiG

end QIQTH.HeatResidualBound
