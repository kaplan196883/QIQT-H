/-
  CConvV2DerivRep — J4-329: FACADE-v2 BRICKS 12 + 13 (HDerivConv / DRepresentation).

  This file discharges the B4 "derivative-representative" fields of
  `CConvFacade.CConvDerivativeData` from the BANKED machinery, for the facade-v2 chain:

    • `hlin`  — the linewise `HasDerivAt` of the heat convolution IN THE SPATIAL coordinate
                `w ↦ heatConv H Fconv t (update x i w) 0`, with value the `i`-th
                witness-field-derivative double integral;
    • `hDrep` — the coordinate representation `D x = ∑ i (∫∫ wfd_i · F) • proj i`;
    • `hD1`   — `ContDiffAt ℝ 1 D 0`, conditional on the named per-coordinate sliver census.

  ─────────────────────────────────────────────────────────────────────────────────────────
  V0 RECONNAISSANCE (verdicts).
  ─────────────────────────────────────────────────────────────────────────────────────────
  (R1) `heatConv`'s definitional shape (`QIQTH.HeatDuhamel.heatConv`):
         `heatConv A B t x y = ∫ s in (0)..t, ∫ z, A (t − s) x z · B s z y`
       — an `intervalIntegral` in `s ∈ [0,t]` of the Lebesgue `z`-integral on `Point n`.

  (R2) THE VARIABLE-MISMATCH VERDICT (route (a) vs (b)).  Route (a) — the banked hDConv
       loc-unif machinery `HDConvGateThreading.hDConv_W1free` / `HDerivConvComposition.
       hDerivConv_conditional` — produces `DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t`,
       i.e. it differentiates in the TIME variable `u` (the third argument of `heatConv`) at the
       FIXED spatial point `0`.  `hlin` needs the derivative in the SPATIAL coordinate
       `w ↦ heatConv H Fconv t (update x i w) 0` at fixed time `t`.  ⇒ ROUTE (a) IS THE WRONG
       VARIABLE.  We take route (b): dominated differentiation-under-∫ in the spatial variable.
       The bank ALREADY contains this as a linewise lemma:
       `QIQTH.HeatResidualBound.hConvDeriv_linewise` (CConvLayerDischarge), which moves `∂_w`
       under BOTH integrals via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
       with a NON-constant interval-integrable `s`-dominator (the `(t−s)^{−1/2}` sliver) — exactly
       the spatial-line HasDerivAt `hlin` requires.  So brick 12 = a re-export of that banked
       lemma at the concrete kernels; NO second dominated-differentiation development is built here.

  (R3) THE FACADE CONSUMER'S H / Fconv (`hCConv_concrete_from_data`):
         `H     := vanVleckGatedWitness g gi hChr hK S a b`
         `Fconv := leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))`
         `F     := fun s z => Fconv s z 0`   (the scalar source of `hDrep`).
       So `witnessFieldDeriv … i (t−s) x z · F s z` and `dH (t−s) x z · Fconv s z 0` coincide
       (`dH := fun τ p z => witnessFieldDeriv … i τ p z`, `F s z = Fconv s z 0`).  This file is
       written width-generic in `Fconv`; the concrete instantiation is definitional.

  (R4) THE SLIVER ADAPTERS' HYPOTHESIS LISTS (brick 13's `hD1`):
       `XUniformSliverFull.hD1_from_data` (scalar, per component):
         inputs {`hsOpen`,`hsnhds`,`fbulk`,`fderivBulk`,`gfull`,`gderiv`,`b`,`hb`,
                 `hbulkderiv`,`hbulk_tendsto`,`hsliver`,`hcont`}  ⟹  `ContDiffAt ℝ 1 gfull 0`;
       `HD1CLMLift.hD1_clm_of_scalar_and_rep` lifts the `n` scalar jets `gcoef i`, together with
       the representation `D = ∑ i gcoef i • proj i`, to `ContDiffAt ℝ 1 D 0`.  We thread these
       two directly (no need for the full `CConvDerivativeData` bundle at the `hD1` slot, since
       `Dmap`'s representation is definitional).

  ─────────────────────────────────────────────────────────────────────────────────────────
  HONESTY FIREWALL.  a₁ = R/6 remains CONDITIONAL.  Every theorem here is a re-threading of
  banked, satisfiable data; NONE proves a₁ = R/6.  The carries of `hlin_linewise` are the genuine
  diff-under-∫ side conditions of `hConvDeriv_linewise` (measurability / interval-integrability /
  the `(t−s)^{−1/2}` sliver domination — SATISFIABLE from the banked wide legs `hStarWide_concrete`
  + `hFpairWide`); the carries of `hD1_conditional` are the named per-coordinate sliver census.
  No `sorry`, no `:= True`, no new axioms, no existing file edited.  NOT a₁ = R/6.
-/
import Mathlib
import QIQTH.HD1CLMLift
import QIQTH.CConvLayerDischarge
import QIQTH.CConvV2WitnessStar

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.CConvFacade
open scoped Topology BigOperators Interval ContDiff

namespace QIQTH.CConvV2DerivRep

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### V1a — the affine line map `ℓ(w) = x + (w − x i)·eᵢ = update x i w`.
    ############################################################################### -/

/-- **`update_eq_affine_line`.**  The `i`-th coordinate line through `x` written as an affine map:
    `Function.update x i w = fun j => x j + (w − x i) · (Pi.single i 1) j`.  At `w = x i` it is `x`;
    its `w`-derivative direction is `eᵢ = Pi.single i 1`.  This is the geometric content of the
    spatial-line differentiation `hlin` performs (the banked `hConvDeriv_linewise` handles the line
    internally; this lemma records the map for the record).  NOT a₁ = R/6. -/
theorem update_eq_affine_line (x : Point n) (i : Fin n) (w : ℝ) :
    Function.update x i w = fun j => x j + (w - x i) * ((Pi.single i (1 : ℝ) : Point n) j) := by
  funext j
  rw [Function.update_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! ###############################################################################
    ### V2a — the CLM derivative representative `Dmap` (brick 13's `D`).
    ############################################################################### -/

/-- **`Dmap`.**  The explicit derivative-representative map for the heat convolution, in the exact
    coordinate form the facade's `hDrep` demands:
      `Dmap … x = ∑ i (∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z · Fconv s z 0) • proj i`.
    Written width-generic in `Fconv`; at the facade's scalar source `F s z = Fconv s z 0` this is
    verbatim the `hDrep` right-hand side.  NOT a₁ = R/6. -/
noncomputable def Dmap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ) (x : Point n) : Point n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
        ∂(volume : Measure (Point n))) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)

/-- **`Dmap_apply_single`.**  The coordinate read-off `(Dmap … x)(Pi.single i 1) = i-th integral`,
    via `ContinuousLinearMap.sum_apply` + the `Pi.single` Kronecker collapse (the banked
    `GcoefContinuity.hcoord` pattern).  NOT a₁ = R/6. -/
theorem Dmap_apply_single (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ) (x : Point n) (i : Fin n) :
    (Dmap g gi hC hK S a b Fconv t x) (Pi.single i (1 : ℝ))
      = ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
          ∂(volume : Measure (Point n)) := by
  rw [Dmap, ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [Pi.single_eq_of_ne hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ###############################################################################
    ### V1b — `hlin_linewise` (brick 12): the SPATIAL linewise `HasDerivAt`.
    ############################################################################### -/

/-- **★ (brick 12) `hlin_linewise`.**  The per-coordinate `HasDerivAt` of the heat convolution
    `w ↦ heatConv H Fconv t (update x i w) 0` in the SPATIAL coordinate `i`, at the concrete left
    kernel `H := vanVleckGatedWitness g gi hC hK S a b`, with derivative value the `i`-th
    witness-field-derivative double integral
      `∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z · Fconv s z 0`.
    THE BANKED ROUTE (b): a re-export of `QIQTH.HeatResidualBound.hConvDeriv_linewise` at
    `dH := fun τ p z ↦ witnessFieldDeriv … i τ p z` (route (a)'s time-variable machinery is the
    WRONG variable — see V0/R2).  The carried hypotheses are EXACTLY the genuine
    diff-under-∫ side conditions of `hConvDeriv_linewise` (each SATISFIABLE from the banked wide
    legs; none is the conclusion): the `w`-neighbourhood `snb ∈ 𝓝 (x i)`, the two
    `AEStronglyMeasurable` legs, the base-line interval integrability, the `(t−s)^{−1/2}`-type
    interval-integrable dominator `bound` with `hbound`, and the pointwise inner `HasDerivAt`
    family `hdiff`.  NOT a₁ = R/6. -/
theorem hlin_linewise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ) (i : Fin n) (x : Point n)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (x i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z
        * Fconv s z 0) (volume.restrict (Set.uIoc 0 t)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) x z * Fconv s z 0) volume 0 t)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0)
      (volume.restrict (Set.uIoc 0 t)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
        * Fconv s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s)
          (Function.update x i w) z * Fconv s z 0)
        (∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
          * Fconv s z 0) w) :
    HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hC hK S a b) Fconv t
        (Function.update x i w) 0)
      (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
        ∂(volume : Measure (Point n))) (x i) :=
  QIQTH.HeatResidualBound.hConvDeriv_linewise
    (vanVleckGatedWitness g gi hC hK S a b)
    (fun τ p z => witnessFieldDeriv g gi hC hK S a b i τ p z)
    Fconv t i x snb hsnb hFmeas hFint hF'meas bound hbdd hbound hdiff

/-! ###############################################################################
    ### V2b — `hDrep_of_def` (trivial) + `hlin_as_D` (V1 rewritten through `Dmap`).
    ############################################################################### -/

/-- **(brick 13) `hDrep_of_def`.**  The facade's `hDrep` shape, TRIVIALLY, from the definition of
    `Dmap`: at the scalar source `F s z = Fconv s z 0`,
      `Dmap … x = ∑ i (∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z · F s z) • proj i`.
    Definitional (`rfl`).  NOT a₁ = R/6. -/
theorem hDrep_of_def (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ) (x : Point n) :
    Dmap g gi hC hK S a b Fconv t x
      = ∑ i : Fin n,
          (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * (fun s z => Fconv s z 0) s z ∂(volume : Measure (Point n)))
            • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ) :=
  rfl

/-- **★ (brick 12→13) `hlin_as_D`.**  `hlin_linewise` with the derivative value rewritten through
    the representative map `Dmap`: the target `hlin` field shape of `CConvDerivativeData`,
      `HasDerivAt (fun w => heatConv H Fconv t (update x i w) 0) ((Dmap … x)(Pi.single i 1)) (x i)`.
    Combines `hlin_linewise` (brick 12) with `Dmap_apply_single`.  Carries = `hlin_linewise`'s
    diff-under-∫ census.  NOT a₁ = R/6. -/
theorem hlin_as_D (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ) (i : Fin n) (x : Point n)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (x i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z
        * Fconv s z 0) (volume.restrict (Set.uIoc 0 t)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s) x z * Fconv s z 0) volume 0 t)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0)
      (volume.restrict (Set.uIoc 0 t)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
        * Fconv s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (t - s)
          (Function.update x i w) z * Fconv s z 0)
        (∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) (Function.update x i w) z
          * Fconv s z 0) w) :
    HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hC hK S a b) Fconv t
        (Function.update x i w) 0)
      ((Dmap g gi hC hK S a b Fconv t x) (Pi.single i (1 : ℝ))) (x i) := by
  rw [Dmap_apply_single g gi hC hK S a b Fconv t x i]
  exact hlin_linewise g gi hC hK S a b Fconv t i x snb hsnb hFmeas hFint hF'meas
    bound hbdd hbound hdiff

/-! ###############################################################################
    ### V3 — `hD1_conditional` (brick 13): `ContDiffAt ℝ 1 (Dmap …) 0` via the sliver census.
    ############################################################################### -/

/-- **★ (brick 13) `hD1_conditional`.**  `ContDiffAt ℝ 1 (Dmap … Fconv t) 0` — the facade's L2
    regularity slot — from the NAMED per-coordinate sliver census feeding
    `XUniformSliverFull.hD1_from_data` (one scalar jet per coordinate `i`), lifted to the CLM-valued
    `Dmap` by `HD1CLMLift.hD1_clm_of_scalar_and_rep` (the representation being `Dmap`'s definition).
    The census (each entry SATISFIABLE — the standard uniform-limit-of-derivatives data, none the
    conclusion): a nbhd `sSet ∈ 𝓝 0`, the bulk truncated primitives `fbulk i` with derivatives
    `fderivBulk i` (`hbulkderiv`), their pointwise convergence to the `i`-th integral
    (`hbulk_tendsto`), the vanishing x-uniform sliver bound `hsliver`/`hb`, and the derivative-field
    continuity `hcont`.  This is the ONE honest still-open L2 carry of the facade-v2 chain — it does
    NOT prove a₁ = R/6.  NOT a₁ = R/6. -/
theorem hD1_conditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Fconv : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    ContDiffAt ℝ 1 (Dmap g gi hC hK S a b Fconv t) (0 : Point n) := by
  -- (1) the per-coordinate scalar C¹ jets from `hD1_from_data`.
  have hg : ∀ i : Fin n, ContDiffAt ℝ 1
      (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
          ∂(volume : Measure (Point n))) (0 : Point n) := by
    intro i
    exact QIQTH.XUniformSliverFull.hD1_from_data hsOpen hsnhds (fbulk i) (fderivBulk i)
      (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
          ∂(volume : Measure (Point n)))
      (gderiv i) (bb i) (hb i) (hbulkderiv i) (hbulk_tendsto i) (hsliver i) (hcont i)
  -- (2) the CLM lift via the definitional representation of `Dmap`.
  exact QIQTH.HD1CLMLift.hD1_clm_of_scalar_and_rep Finset.univ 1
    (Dmap g gi hC hK S a b Fconv t)
    (fun i x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * Fconv s z 0
        ∂(volume : Measure (Point n)))
    (fun i => (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) (0 : Point n)
    (Filter.univ_mem) (fun x _ => rfl) (fun i _ => hg i)

end QIQTH.CConvV2DerivRep

section AxiomChecks
open QIQTH.CConvV2DerivRep
#print axioms update_eq_affine_line
#print axioms Dmap_apply_single
#print axioms hlin_linewise
#print axioms hDrep_of_def
#print axioms hlin_as_D
#print axioms hD1_conditional
end AxiomChecks
