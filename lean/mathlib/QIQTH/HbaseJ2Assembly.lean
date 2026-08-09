/-
  HbaseJ2Assembly — J4-483: ASSEMBLE the base-slot SECOND-jet modulus `hbaseJ2` from the two-point
  Grönwall (J4-482) — the penultimate step of the a₁ = R/6 convergent-wall effort.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-482).  `SecondVariationModulus` (J4-481) exposed the endpoint
  second-variation operator (`uniformFlowExp_secondVar_spec`) and the `.2`-component inhomogeneous
  Jacobi ODE (`secondVar_snd_hasDerivAt`); `HbaseJ2Gronwall` (J4-482) landed the two-point Grönwall
  on that `.2`-component ODE (`secondVar_snd_twopoint_diff_bound`).  This file INSTANTIATES that
  Grönwall at the two exposures for nearby bases `q, q'`, discharges its hypotheses from the banked
  compactness / tube-separation / first-jet Jacobi kit, welds in the SECOND-jet bridge
  `fderiv²(uniformFlowExp q) v δ b = (Vf δ 1).2.1`, and closes the double operator-norm sup — giving
  the base-slot second-jet modulus `hbaseJ2` on the strict (reachable) interior.  This is the J4-435
  `JacobiCLMExposure.uniformFlowExp_fderiv_base_modulus` assembly ONE ORDER UP.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `fderiv2_apply_eq_of_hasFDerivAt` — **the SECOND-jet bridge.**  If `fderiv ℝ f` is differentiable
      at `v` and `HasFDerivAt (fun w => fderiv ℝ f w b) L₂ v`, then
        `L₂ δ = fderiv ℝ (fderiv ℝ f) v δ b`   for all `δ`.
      The `(apply b) ∘ (fderiv f)` chain-rule composition + `HasFDerivAt` uniqueness — the identity that
      turns the per-seed second-variation operator `L₂` (exposure output) into the second Fréchet jet.

    * `opNorm2_le_bound` — **the double operator-norm bound.**  For `T : E →L (E →L F)` and `C ≥ 0`,
      `(∀ δ b, ‖T δ b‖ ≤ C·‖δ‖·‖b‖) ⟹ ‖T‖ ≤ C`.  Two nested `opNorm_le_bound`s — the sup over the
      bilinear pair `(δ, b)` the second-jet modulus needs.

    * `secondVar_endpoint_seed_diff_bound` — **★ the per-seed core.**  For two base doubled curves
      (bases `q, q'`) sharing the seed data, the endpoint `.2`-slot difference of the doubled
      second-variation fields obeys
        `‖(Vf₁ 1).2 − (Vf₂ 1).2‖ ≤ (3·Dc·M₂·e^{4Kf} + DD·e^{3Kf})·‖δ‖·‖b‖`,
      the two-point Grönwall `secondVar_snd_twopoint_diff_bound` with every hypothesis discharged from
      the first-jet Jacobi kit (`jacobi_growth_bound` / `jacobi_twopoint_diff_bound` on the `.1`-slots
      and base-Jacobi fields via `secondVar_fst_hasDerivAt`) + `linODE_growth_bound` on the inhomogeneous
      `.2`-slot.  Each source term carries the joint `δ·b` bilinearity a full-doubled-norm bound loses.

    * `uniformFlowExp_fderiv2_base_modulus` — **★★ hbaseJ2 (reachable interior), DISCHARGED.**  A single
      uniform `Λ₂ ≥ 0` over `K` with
        `‖fderiv²(uniformFlowExp q) v − fderiv²(uniformFlowExp q') v‖ ≤ Λ₂·‖q − q'‖`
      for `q, q' ∈ K` and `v` reachable (`‖v‖ < expRho q`, `‖v‖ < expRho q'`, `‖v‖ < ρ_K`).  The
      two-exposure instantiation of the per-seed core + the SECOND-jet bridge + the double opNorm.

  ⚠ WHAT REMAINS (J4-484 — the WELD; NOT here): the `z₀`-anchored triangle (the `ForwardFlowJet`
    pattern one order up) welding VELOCITY (`Flow3Regularity.forward2_velocitySlot`) + BASE (this
    file's `hbaseJ2`) into the joint `hFwd2` on `K ×ˢ ball` ⟹
    `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` UNCONDITIONAL ⟹ THE CONVERGENT WALL FALLS.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HbaseJ2Gronwall
import QIQTH.JacobiCLMExposure
import QIQTH.Flow3Regularity

open Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.GeodesicGronwall
open QIQTH.HbaseJ2Gronwall QIQTH.JacobiCLMExposure QIQTH.SecondVariationModulus QIQTH.Flow3Regularity
open scoped Topology NNReal

namespace QIQTH.HbaseJ2Assembly

variable {n : ℕ}

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

/-! ###############################################################################
    ### THE SECOND-JET BRIDGE + THE DOUBLE OPERATOR NORM (pure CLM / calculus).
    ############################################################################### -/

/-- **`fderiv2_apply_eq_of_hasFDerivAt` — the SECOND-jet bridge.**  If the first jet `fderiv ℝ f` is
    differentiable at `v` and the per-seed map `w ↦ fderiv ℝ f w b` has Fréchet derivative `L₂` at `v`,
    then `L₂ δ = fderiv ℝ (fderiv ℝ f) v δ b`.  Proof: `(fun w => fderiv f w b) = (apply b) ∘ (fderiv f)`
    (a CLM composition), whose Fréchet derivative is `(apply b).comp (fderiv²)`; `HasFDerivAt` uniqueness
    identifies `L₂`, and `(apply b) (fderiv² δ) = fderiv² δ b`.  NOT `a₁ = R/6`. -/
theorem fderiv2_apply_eq_of_hasFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {v b : E} {L₂ : E →L[ℝ] F}
    (hf2 : DifferentiableAt ℝ (fderiv ℝ f) v)
    (hL₂ : HasFDerivAt (fun w => fderiv ℝ f w b) L₂ v) :
    ∀ δ : E, L₂ δ = fderiv ℝ (fderiv ℝ f) v δ b := by
  have hcomp : HasFDerivAt (fun w => fderiv ℝ f w b)
      ((ContinuousLinearMap.apply ℝ F b).comp (fderiv ℝ (fderiv ℝ f) v)) v := by
    have h := (ContinuousLinearMap.apply ℝ F b).hasFDerivAt.comp v hf2.hasFDerivAt
    simpa [Function.comp, ContinuousLinearMap.apply_apply] using h
  have heq := hL₂.unique hcomp
  intro δ
  rw [heq]
  simp [ContinuousLinearMap.apply_apply]

/-- **`opNorm2_le_bound` — the double operator-norm bound.**  For a bilinear-shaped continuous linear
    map `T : E →L[ℝ] (E →L[ℝ] F)` and `C ≥ 0`, a uniform per-pair bound `‖T δ b‖ ≤ C·‖δ‖·‖b‖` gives
    `‖T‖ ≤ C`.  Two nested `ContinuousLinearMap.opNorm_le_bound`s — the sup over `(δ, b)`.
    NOT `a₁ = R/6`. -/
theorem opNorm2_le_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] (E →L[ℝ] F)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ δ b : E, ‖T δ b‖ ≤ C * ‖δ‖ * ‖b‖) : ‖T‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound T hC (fun δ => ?_)
  refine ContinuousLinearMap.opNorm_le_bound (T δ) (mul_nonneg hC (norm_nonneg _)) (fun b => ?_)
  exact h δ b

/-! ###############################################################################
    ### ★ THE PER-SEED CORE — instantiate the two-point Grönwall + discharge hypotheses.
    ############################################################################### -/

/-- **★ `secondVar_endpoint_seed_diff_bound` — the per-seed core bound.**  For two base doubled curves
    `(Y₁, Jf₁)`, `(Y₂, Jf₂)` (bases `q, q'`) — the base geodesics `Yᵢ` and the base velocity Jacobi
    fields `Jfᵢ` (seed `(0,b)`) — and the doubled second-variation fields `Vfᵢ` (seed `((0,δ),(0,0))`)
    solving the doubled-linearized ODE along `(Yᵢ, Jfᵢ)`, the endpoint `.2`-slot difference obeys
      `‖(Vf₁ 1).2 − (Vf₂ 1).2‖ ≤ (3·Dc·M₂·e^{4Kf} + DD·e^{3Kf})·‖δ‖·‖b‖`,
    where `Kf` bounds `‖DF(geo)(Yᵢ)‖`, `M₂` bounds `‖D²F(geo)(Yᵢ)‖`, `Dc` the coefficient separation
    `‖DF(Y₁) − DF(Y₂)‖`, `DD` the `D²F` separation `‖D²F(Y₁) − D²F(Y₂)‖`.  Every hypothesis of the
    two-point Grönwall `secondVar_snd_twopoint_diff_bound` is discharged from the first-jet Jacobi kit
    (`jacobi_growth_bound` / `jacobi_twopoint_diff_bound` on the `.1`-slots — homogeneous Jacobi fields
    via `secondVar_fst_hasDerivAt` — and on the base-Jacobi fields) plus `linODE_growth_bound` on the
    inhomogeneous `.2`-slot.  NOT `a₁ = R/6`. -/
theorem secondVar_endpoint_seed_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y₁ Y₂ Jf1 Jf2 : ℝ → Point n × Point n}
    {Vf1 Vf2 : ℝ → (Point n × Point n) × (Point n × Point n)}
    {b δ : Point n} {Kf M₂ Dc DD : ℝ} (hKf0 : 0 ≤ Kf) (hM₂0 : 0 ≤ M₂)
    (hJf1_0 : Jf1 0 = ((0 : Point n), b)) (hJf2_0 : Jf2 0 = ((0 : Point n), b))
    (hJf1ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Jf1 (fderiv ℝ (geodesicField g gi) (Y₁ τ) (Jf1 τ)) τ)
    (hJf2ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Jf2 (fderiv ℝ (geodesicField g gi) (Y₂ τ) (Jf2 τ)) τ)
    (hVf1_0 : Vf1 0 = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))))
    (hVf2_0 : Vf2 0 = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))))
    (hVf1ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Vf1
      (fderiv ℝ (doubledField g gi)
        ((Y₁ τ, Jf1 τ) : (Point n × Point n) × (Point n × Point n)) (Vf1 τ)) τ)
    (hVf2ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Vf2
      (fderiv ℝ (doubledField g gi)
        ((Y₂ τ, Jf2 τ) : (Point n × Point n) × (Point n × Point n)) (Vf2 τ)) τ)
    (hKbq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ τ)‖ ≤ Kf)
    (hKbq' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Kf)
    (hD2q : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)‖ ≤ M₂)
    (hD2q' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ ≤ M₂)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Dc)
    (hDD : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
        - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ ≤ DD) :
    ‖(Vf1 1).2 - (Vf2 1).2‖
      ≤ (3 * Dc * M₂ * (Real.exp Kf) ^ 4 + DD * (Real.exp Kf) ^ 3) * ‖δ‖ * ‖b‖ := by
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hnormδ : ‖((0 : Point n), δ)‖ = ‖δ‖ := by rw [Prod.norm_mk]; simp
  have hnormb : ‖((0 : Point n), b)‖ = ‖b‖ := by rw [Prod.norm_mk]; simp
  -- the `.1`-slot and `.2`-slot ODEs (projections of the doubled ODE).
  have hP1ode := fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1) => secondVar_fst_hasDerivAt g gi hC (hVf1ode τ hτ)
  have hP2ode := fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1) => secondVar_fst_hasDerivAt g gi hC (hVf2ode τ hτ)
  have hS1 := fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1) => secondVar_snd_hasDerivAt g gi hC (hVf1ode τ hτ)
  have hS2 := fun τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1) => secondVar_snd_hasDerivAt g gi hC (hVf2ode τ hτ)
  -- `.1`-slot growth (homogeneous Jacobi, seed `(0,δ)`): `Pb = ‖δ‖·exp Kf`.
  have hP1b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖(Vf1 τ).1‖ ≤ ‖δ‖ * Real.exp Kf := by
    intro τ hτ
    have h := jacobi_growth_bound g gi hKf0 hP1ode hKbq τ hτ
    simpa [hVf1_0, hnormδ] using h
  have hP2b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖(Vf2 τ).1‖ ≤ ‖δ‖ * Real.exp Kf := by
    intro τ hτ
    have h := jacobi_growth_bound g gi hKf0 hP2ode hKbq' τ hτ
    simpa [hVf2_0, hnormδ] using h
  -- base-Jacobi growth (seed `(0,b)`): `Jbb = ‖b‖·exp Kf`.
  have hJ1b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf1 τ‖ ≤ ‖b‖ * Real.exp Kf := by
    intro τ hτ
    have h := jacobi_growth_bound g gi hKf0 hJf1ode hKbq τ hτ
    rw [hJf1_0] at h
    simpa [hnormb] using h
  have hJ2b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf2 τ‖ ≤ ‖b‖ * Real.exp Kf := by
    intro τ hτ
    have h := jacobi_growth_bound g gi hKf0 hJf2ode hKbq' τ hτ
    rw [hJf2_0] at h
    simpa [hnormb] using h
  -- `.1`-slot two-point separation (same seed): `DP = Dc·(‖δ‖·exp Kf)·exp Kf`.
  have hPd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(Vf1 τ).1 - (Vf2 τ).1‖ ≤ Dc * (‖δ‖ * Real.exp Kf) * Real.exp Kf := by
    intro τ hτ
    have h0eq : (fun t => (Vf1 t).1) 0 = (fun t => (Vf2 t).1) 0 := by
      show (Vf1 0).1 = (Vf2 0).1
      rw [hVf1_0, hVf2_0]
    have htp := jacobi_twopoint_diff_bound g gi (K := Kf) (Dcoef := Dc) (Jb := ‖δ‖ * Real.exp Kf)
      hKf0 hP1ode hP2ode h0eq hKbq hAd hP2b τ hτ
    simpa using htp
  -- base-Jacobi two-point separation (same seed): `DJb = Dc·(‖b‖·exp Kf)·exp Kf`.
  have hJd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Jf1 τ - Jf2 τ‖ ≤ Dc * (‖b‖ * Real.exp Kf) * Real.exp Kf := by
    intro τ hτ
    have h0eq : Jf1 0 = Jf2 0 := by rw [hJf1_0, hJf2_0]
    exact jacobi_twopoint_diff_bound g gi (K := Kf) (Dcoef := Dc) (Jb := ‖b‖ * Real.exp Kf)
      hKf0 hJf1ode hJf2ode h0eq hKbq hAd hJ2b τ hτ
  -- `.2`-slot growth (inhomogeneous, zero seed): `Xb = (M₂·Pb·Jbb)·exp Kf`.
  have hsrc : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) ((Vf2 τ).1) (Jf2 τ)‖
        ≤ M₂ * (‖δ‖ * Real.exp Kf) * (‖b‖ * Real.exp Kf) := by
    intro τ hτ
    calc ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) ((Vf2 τ).1) (Jf2 τ)‖
        ≤ ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) ((Vf2 τ).1)‖ * ‖Jf2 τ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ * ‖(Vf2 τ).1‖) * ‖Jf2 τ‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (M₂ * (‖δ‖ * Real.exp Kf)) * (‖b‖ * Real.exp Kf) :=
          mul_le_mul (mul_le_mul (hD2q' τ hτ) (hP2b τ hτ) (norm_nonneg _) hM₂0)
            (hJ2b τ hτ) (norm_nonneg _) (mul_nonneg hM₂0 (by positivity))
  have hXb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(Vf2 τ).2‖ ≤ (M₂ * (‖δ‖ * Real.exp Kf) * (‖b‖ * Real.exp Kf)) * Real.exp Kf := by
    have hbnd := linODE_growth_bound (E := Point n × Point n)
      (A := fun τ => fderiv ℝ (geodesicField g gi) (Y₂ τ))
      (X := fun t => (Vf2 t).2)
      (b := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) ((Vf2 τ).1) (Jf2 τ))
      (K := Kf) (Bsrc := M₂ * (‖δ‖ * Real.exp Kf) * (‖b‖ * Real.exp Kf))
      hKf0 hS2 (by simp [hVf2_0]) hKbq' hsrc
    intro τ hτ
    exact hbnd τ hτ
  -- THE TWO-POINT GRÖNWALL on the `.2`-component ODE.
  have hmain := secondVar_snd_twopoint_diff_bound g gi
    (Y₁ := Y₁) (Y₂ := Y₂) (P₁ := fun t => (Vf1 t).1) (P₂ := fun t => (Vf2 t).1)
    (Jb₁ := Jf1) (Jb₂ := Jf2) (S₁ := fun t => (Vf1 t).2) (S₂ := fun t => (Vf2 t).2)
    (Kf := Kf) (Dc := Dc)
    (Xb := (M₂ * (‖δ‖ * Real.exp Kf) * (‖b‖ * Real.exp Kf)) * Real.exp Kf)
    (M₂ := M₂) (DD := DD) (Pb := ‖δ‖ * Real.exp Kf) (Jbb := ‖b‖ * Real.exp Kf)
    (DP := Dc * (‖δ‖ * Real.exp Kf) * Real.exp Kf)
    (DJb := Dc * (‖b‖ * Real.exp Kf) * Real.exp Kf)
    hKf0 hS1 hS2 (by show (Vf1 0).2 = (Vf2 0).2; rw [hVf1_0, hVf2_0])
    hKbq hAd hXb hD2q' hDD hP1b hP2b hJ1b hPd hJd 1 ht1
  refine (hmain).trans (le_of_eq ?_)
  ring

/-! ###############################################################################
    ### ★★ hbaseJ2 — the two-exposure instantiation + bridge + double opNorm.
    ############################################################################### -/

/-- **★★ `uniformFlowExp_fderiv2_base_modulus` — hbaseJ2 (reachable interior), DISCHARGED.**  A single
    uniform `Λ₂ ≥ 0` over the compact `K` with
      `‖fderiv²(uniformFlowExp … q) v − fderiv²(uniformFlowExp … q') v‖ ≤ Λ₂·‖q − q'‖`
    for `q, q' ∈ K` and `v` reachable (`‖v‖ < expRho q`, `‖v‖ < expRho q'`, `‖v‖ < ρ_K`).  Assembled
    from the exposure `uniformFlowExp_secondVar_spec` (second jet = endpoint doubled second-variation
    operator) at both bases, the SECOND-jet bridge `fderiv2_apply_eq_of_hasFDerivAt`
    (`fderiv²(uniformFlowExp q) v δ b = (Vf δ 1).2.1`, needing `C²` from `contDiffAt3_uniformFlowExp`),
    the per-seed core `secondVar_endpoint_seed_diff_bound`, and the double `opNorm2_le_bound` over the
    bilinear pair `(δ, b)`.  This is `JacobiCLMExposure.uniformFlowExp_fderiv_base_modulus` one order up.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_fderiv2_base_modulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Λ₂ : ℝ, 0 ≤ Λ₂ ∧ ∀ q ∈ K, ∀ q' ∈ K, ∀ v : Point n,
      ‖v‖ < expRho g gi hC q → ‖v‖ < expRho g gi hC q' →
      ‖v‖ < uniformFlowRadius g gi hC hK →
        ‖fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
            - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v‖
          ≤ Λ₂ * ‖q - q'‖ := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- `K ⊆ closedBall 0 M`; the common confinement ball `S`.
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) (M + C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  -- global differentiability of the first jet (for the `D¹F` MVT).
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  -- the `M₂` (C²) sup bound on `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · refine ⟨0, le_refl _, fun z hz => ?_⟩
      rw [hSe] at hz; exact absurd hz (by simp)
    · have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
        (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
          (by simp)).norm
      obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
      exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
        norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
        fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  -- the `M₃` (C³) two-point `D²F` separation on `S`.
  obtain ⟨M₃, hM₃0, hM₃sep⟩ := geodesicField_fderiv2_diff_bound g gi hC hScompact hSconv
  -- the field bound `Kf` on `S`.
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  -- the base-tube separation `Lsep` (uniform over `K`).
  obtain ⟨Lsep, hLsep0, hsep⟩ := uniformTube_twopoint_diff_bound g gi hC hK
  set Λ₂ : ℝ := 3 * M₂ ^ 2 * Real.exp Lsep * (Real.exp Kf) ^ 4
      + M₃ * Real.exp Lsep * (Real.exp Kf) ^ 3 with hΛ₂def
  have hΛ₂0 : 0 ≤ Λ₂ := by
    rw [hΛ₂def]
    have h1 : 0 ≤ 3 * M₂ ^ 2 * Real.exp Lsep * (Real.exp Kf) ^ 4 := by positivity
    have h2 : 0 ≤ M₃ * Real.exp Lsep * (Real.exp Kf) ^ 3 :=
      mul_nonneg (mul_nonneg hM₃0 (Real.exp_pos _).le) (by positivity)
    linarith
  refine ⟨Λ₂, hΛ₂0, ?_⟩
  intro q hq q' hq' v hvexpq hvexpq' hvuf
  have hvρ : ‖v‖ ≤ ρ := hvuf.le
  -- both tubes live in `S`.
  have hmemtube : ∀ z ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK z v τ ∈ S := by
    intro z hz τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hconf : ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK z hz v hvρ τ hτ
    have hzn : ‖((z, 0) : Point n × Point n)‖ ≤ M := by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      have := hM hz; rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc ‖uniformFlowTube g gi hC hK z v τ‖
        ≤ ‖((z, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((z, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n))
          simpa using this
      _ ≤ M + C₀ * ‖v‖ := add_le_add hzn hconf
      _ ≤ M + C₀ * ρ := by
          have : C₀ * ‖v‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀nn
          linarith
  -- `C²` differentiability of both forward maps at `v` (for the second-jet bridge).
  have hf2q : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v :=
    ((contDiffAt3_uniformFlowExp g gi hC hK q hq v hvexpq hvuf).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hf2q' : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v :=
    ((contDiffAt3_uniformFlowExp g gi hC hK q' hq' v hvexpq' hvuf).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  -- field bounds along both tubes.
  have hKbq : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q hq τ hτ)
  have hKbq' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q' hq' τ hτ)
  -- C² bounds along both tubes.
  have hD2q : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)‖ ≤ M₂ :=
    fun τ hτ => hM₂ _ (hmemtube q hq τ hτ)
  have hD2q' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ M₂ :=
    fun τ hτ => hM₂ _ (hmemtube q' hq' τ hτ)
  set Dc : ℝ := M₂ * (‖q - q'‖ * Real.exp Lsep) with hDcdef
  set DD : ℝ := M₃ * (‖q - q'‖ * Real.exp Lsep) with hDDdef
  -- coefficient separation `Dc` (D¹F MVT × tube separation).
  have hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)
          - fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Dc := by
    intro τ hτ
    have hmvt := hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hM₂
      (hmemtube q' hq' τ hτ) (hmemtube q hq τ hτ)
    refine hmvt.trans ?_
    have hd := hsep q hq q' hq' v hvρ τ hτ
    simp only [dist_eq_norm] at hd
    have hexpτ : Real.exp (Lsep * τ) ≤ Real.exp Lsep := by
      apply Real.exp_le_exp.mpr
      calc Lsep * τ ≤ Lsep * 1 := mul_le_mul_of_nonneg_left hτ.2 hLsep0
        _ = Lsep := mul_one _
    rw [hDcdef]
    calc M₂ * ‖uniformFlowTube g gi hC hK q v τ - uniformFlowTube g gi hC hK q' v τ‖
        ≤ M₂ * (‖q - q'‖ * Real.exp (Lsep * τ)) := mul_le_mul_of_nonneg_left hd hM₂0
      _ ≤ M₂ * (‖q - q'‖ * Real.exp Lsep) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpτ (norm_nonneg _)) hM₂0
  -- `D²F` separation `DD` (M₃ two-point bound × tube separation).
  have hDD_bound : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q v τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ DD := by
    intro τ hτ
    refine (hM₃sep _ (hmemtube q hq τ hτ) _ (hmemtube q' hq' τ hτ)).trans ?_
    have hd := hsep q hq q' hq' v hvρ τ hτ
    simp only [dist_eq_norm] at hd
    have hexpτ : Real.exp (Lsep * τ) ≤ Real.exp Lsep := by
      apply Real.exp_le_exp.mpr
      calc Lsep * τ ≤ Lsep * 1 := mul_le_mul_of_nonneg_left hτ.2 hLsep0
        _ = Lsep := mul_one _
    rw [hDDdef]
    calc M₃ * ‖uniformFlowTube g gi hC hK q v τ - uniformFlowTube g gi hC hK q' v τ‖
        ≤ M₃ * (‖q - q'‖ * Real.exp (Lsep * τ)) := mul_le_mul_of_nonneg_left hd hM₃0
      _ ≤ M₃ * (‖q - q'‖ * Real.exp Lsep) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpτ (norm_nonneg _)) hM₃0
  -- THE PER-PAIR BOUND: for each `(δ, b')`, bridge to the per-seed core.
  have hper : ∀ δ b' : Point n,
      ‖(fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v) δ b'‖
        ≤ Λ₂ * ‖q - q'‖ * ‖δ‖ * ‖b'‖ := by
    intro δ b'
    obtain ⟨Jf0q, Vfq, L₂q, hJf0q0, hJf0qode, hVfq0, hVfqode, hL₂q, hFDq⟩ :=
      uniformFlowExp_secondVar_spec g gi hC hK q hq v hvuf b'
    obtain ⟨Jf0q', Vfq', L₂q', hJf0q'0, hJf0q'ode, hVfq'0, hVfq'ode, hL₂q', hFDq'⟩ :=
      uniformFlowExp_secondVar_spec g gi hC hK q' hq' v hvuf b'
    have hbrq := fderiv2_apply_eq_of_hasFDerivAt hf2q hFDq
    have hbrq' := fderiv2_apply_eq_of_hasFDerivAt hf2q' hFDq'
    have hval : (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
          - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v) δ b'
        = (Vfq δ 1).2.1 - (Vfq' δ 1).2.1 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
          ← hbrq δ, ← hbrq' δ, hL₂q δ, hL₂q' δ]
    rw [hval]
    have hcore := secondVar_endpoint_seed_diff_bound g gi hC
      (Y₁ := uniformFlowTube g gi hC hK q v) (Y₂ := uniformFlowTube g gi hC hK q' v)
      (Jf1 := Jf0q) (Jf2 := Jf0q') (Vf1 := Vfq δ) (Vf2 := Vfq' δ) (b := b') (δ := δ)
      (Kf := Kf) (M₂ := M₂) (Dc := Dc) (DD := DD)
      hKf0 hM₂0 hJf0q0 hJf0q'0 hJf0qode hJf0q'ode (hVfq0 δ) (hVfq'0 δ) (hVfqode δ) (hVfq'ode δ)
      hKbq hKbq' hD2q hD2q' hAd hDD_bound
    calc ‖(Vfq δ 1).2.1 - (Vfq' δ 1).2.1‖
        = ‖((Vfq δ 1).2 - (Vfq' δ 1).2).1‖ := by rw [Prod.fst_sub]
      _ ≤ ‖(Vfq δ 1).2 - (Vfq' δ 1).2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ (3 * Dc * M₂ * (Real.exp Kf) ^ 4 + DD * (Real.exp Kf) ^ 3) * ‖δ‖ * ‖b'‖ := hcore
      _ = Λ₂ * ‖q - q'‖ * ‖δ‖ * ‖b'‖ := by rw [hDcdef, hDDdef, hΛ₂def]; ring
  -- THE DOUBLE OPERATOR NORM.
  exact opNorm2_le_bound
    (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q)) v
      - fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK q')) v)
    (mul_nonneg hΛ₂0 (norm_nonneg _)) hper

end QIQTH.HbaseJ2Assembly

/-! ## THE ASSEMBLY LEDGER (post J4-483).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE CONVERGENT WALL.  Both a₁=R/6 consumer chains bottom out on the chart SECOND field-jet at the │
  │  field centre; J4-479 (`ChartSecondJet`) reduced it to the atom `hFwd2`; J4-480 (`Flow3Regularity`)│
  │  discharged the VELOCITY slot (`forward2_velocitySlot`); J4-481 (`SecondVariationModulus`) exposed  │
  │  the endpoint second-variation operator + the `.2`-component inhomogeneous Jacobi ODE; J4-482        │
  │  (`HbaseJ2Gronwall`) landed the two-point Grönwall on that ODE.  THIS BRICK assembles the BASE-slot  │
  │  second-jet modulus `hbaseJ2` from that Grönwall.                                                   │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (i) THE BRIDGE — `fderiv2_apply_eq_of_hasFDerivAt` (DERIVED, pure calculus).  Turns the exposure's │
  │  per-seed operator `L₂` into the SECOND Fréchet jet: `L₂ δ = fderiv²(f) v δ b` via the             │
  │  `(apply b) ∘ (fderiv f)` chain rule + `HasFDerivAt` uniqueness (needs `C²` at `v`).                │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (ii) THE DOUBLE opNORM — `opNorm2_le_bound` (DERIVED).  `(∀ δ b, ‖T δ b‖ ≤ C‖δ‖‖b‖) ⟹ ‖T‖ ≤ C`    │
  │  — two nested `opNorm_le_bound`s, the sup over the bilinear pair `(δ,b)`.                            │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (iii) THE PER-SEED CORE — `secondVar_endpoint_seed_diff_bound` (DERIVED, the star).  Instantiates  │
  │  `secondVar_snd_twopoint_diff_bound` (J4-482) with EVERY hypothesis discharged: field/C² bounds     │
  │  (Kf/M₂), coefficient/D²F separations (Dc/DD), `.1`-slot + base-Jacobi bounds/separations from      │
  │  `jacobi_growth_bound` / `jacobi_twopoint_diff_bound` (via `secondVar_fst_hasDerivAt`), the         │
  │  inhomogeneous `.2`-slot bound from `linODE_growth_bound`.  Yields                                  │
  │      `‖(Vf₁ 1).2 − (Vf₂ 1).2‖ ≤ (3·Dc·M₂·e^{4Kf} + DD·e^{3Kf})·‖δ‖·‖b‖`.                            │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (iv) ★★ hbaseJ2 — `uniformFlowExp_fderiv2_base_modulus` (DERIVED).  The two-exposure               │
  │  instantiation of the core + bridge + double opNorm:                                                │
  │      `‖fderiv²(uniformFlowExp q) v − fderiv²(uniformFlowExp q') v‖ ≤ Λ₂·‖q − q'‖`,                   │
  │  `Λ₂ = 3·M₂²·e^{Lsep}·e^{4Kf} + M₃·e^{Lsep}·e^{3Kf}` uniform over `K` (Dc = M₂·e^{Lsep}·‖q−q'‖,     │
  │  DD = M₃·e^{Lsep}·‖q−q'‖ carry the two-point smallness), on the reachable interior                  │
  │  (`‖v‖ < expRho q`, `‖v‖ < expRho q'`, `‖v‖ < ρ_K`).                                                │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT.  The two-point Grönwall on the `.2`-component ODE
  (`secondVar_snd_twopoint_diff_bound`, J4-482), the trilinear source telescope (`clm2_apply_telescope`),
  the M₃ D²F-separation (`geodesicField_fderiv2_diff_bound`), the inhomogeneous growth bound
  (`linODE_growth_bound`), the `.1`-slot Jacobi ODE (`secondVar_fst_hasDerivAt`), the endpoint exposure
  (`uniformFlowExp_secondVar_spec`, J4-481), the first-jet Jacobi kit (`jacobi_growth_bound`,
  `jacobi_twopoint_diff_bound`), the tube separation (`uniformTube_twopoint_diff_bound`) and the `C³`
  forward map (`contDiffAt3_uniformFlowExp`) were ALL ALREADY BANKED.  So this brick is a pure
  instantiate/discharge/bridge/opNorm ASSEMBLY — the J4-435 `uniformFlowExp_fderiv_base_modulus` template
  one derivative up — NOT a new ODE or regularity effort.  ⚠ The reachability guard on `v` (`expRho q`,
  `expRho q'`) is the price of the second-jet bridge (`C²` at `v`); the J4-484 weld reconciles it with a
  K-uniform reachability radius.

  ── WHAT REMAINS (J4-484): THE WELD.  The `z₀`-anchored triangle (the `ForwardFlowJet` pattern one order
  up) + a K-uniform reachability radius, welding VELOCITY (`Flow3Regularity.forward2_velocitySlot`) +
  BASE (this file's `uniformFlowExp_fderiv2_base_modulus`) into the joint `hFwd2` on `K ×ˢ ball` ⟹
  `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` UNCONDITIONAL ⟹ THE CONVERGENT WALL FALLS.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.HbaseJ2Assembly
#print axioms fderiv2_apply_eq_of_hasFDerivAt
#print axioms opNorm2_le_bound
#print axioms secondVar_endpoint_seed_diff_bound
#print axioms uniformFlowExp_fderiv2_base_modulus
end AxiomChecks
