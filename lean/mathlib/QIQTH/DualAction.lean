/-
  W1 (TYPE_II_TRACE_PLAN.md) — THE DUAL ACTION θ_s on the crossed product.

  The Takesaki dual ℝ-action of `M ⋊_σ ℝ`, implemented by conjugation with the fiberwise phase (modulation)
  unitary `(V_s ξ)(x) = e^{isx}·ξ(x)` on `L²(ℝ;H)`:  `θ_s(T) := V_{−s} T V_s`.  The two defining identities:
      θ_s(π(a)) = π(a)             (`dualAction_matter` — the phase is scalar, fiberwise actions commute),
      θ_s(λ_t)  = e^{ist}·λ_t      (`dualAction_clock` — the vector-valued Weyl relation),
  plus the group law and multiplicativity.  This is the action against which the dual-weight trace scales,
  `τ∘θ_s = e^{−s}τ` (the ladder's later rungs).  Binding convention (GPT-5.5-pro consult): θ_s SHIFTS the
  log-clock spectrum — the weight density lives on `L`, never on the clock position.

  ⚠ Honest scope: the dual action on the REPRESENTED operators `B(L²(ℝ;H))` (restricting to the generated
  algebra); the von Neumann closure and the full CPW trace stay carried (plan header). Axiom-free, std-3.
-/
import Mathlib
import QIQTH.CrossedProductCovariance
import QIQTH.Spectral.ModulationFlow

namespace QIQTH.StandardSubspaceModular

open MeasureTheory QIQTH.Spectral QIQTH.Spectral.Multiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The inverse-phase product: `e^{−isx}·e^{isx} = 1`. -/
theorem modSymbol_neg_mul (s x : ℝ) : modSymbol (-s) x * modSymbol s x = 1 := by
  rw [modSymbol, modSymbol, ← Complex.exp_add]
  have h : (↑(-s * x) : ℂ) * Complex.I + (↑(s * x) : ℂ) * Complex.I = 0 := by push_cast; ring
  rw [h, Complex.exp_zero]

/-- The additive phase product: `e^{i(s+r)x} = e^{isx}·e^{irx}`. -/
theorem modSymbol_add_left (s r x : ℝ) :
    modSymbol (s + r) x = modSymbol s x * modSymbol r x := by
  rw [modSymbol, modSymbol, modSymbol, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The dual-phase fiber is in `L²`: `x ↦ e^{isx}·ξ(x)` (the phase is unimodular). -/
theorem memLp_dualPhaseFiber (s : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun x => modSymbol s x • ξ x) 2 (volume : Measure ℝ) :=
  MemLp.of_le_mul (Lp.memLp ξ)
    (((modSymbol_measurable s).aestronglyMeasurable).smul (Lp.aestronglyMeasurable ξ))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_smul, norm_modSymbol, one_mul])

/-- The fiberwise phase map on `L²(ℝ;H)`. -/
noncomputable def dualPhaseFun (s : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) :=
  (memLp_dualPhaseFiber s ξ).toLp

theorem dualPhaseFun_coeFn (s : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    dualPhaseFun s ξ =ᵐ[volume] fun x => modSymbol s x • ξ x :=
  MemLp.coeFn_toLp _

theorem dualPhaseFun_add (s : ℝ) (ξ η : Lp H 2 (volume : Measure ℝ)) :
    dualPhaseFun s (ξ + η) = dualPhaseFun s ξ + dualPhaseFun s η := by
  rw [Lp.ext_iff]
  filter_upwards [dualPhaseFun_coeFn s (ξ + η),
    Lp.coeFn_add (dualPhaseFun s ξ) (dualPhaseFun s η),
    dualPhaseFun_coeFn s ξ, dualPhaseFun_coeFn s η, Lp.coeFn_add ξ η] with x e1 e2 e3 e4 e5
  simp only [e1, e2, Pi.add_apply, e3, e4, e5, smul_add]

theorem dualPhaseFun_smul (s : ℝ) (c : ℂ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    dualPhaseFun s (c • ξ) = c • dualPhaseFun s ξ := by
  rw [Lp.ext_iff]
  filter_upwards [dualPhaseFun_coeFn s (c • ξ),
    Lp.coeFn_smul c (dualPhaseFun s ξ), dualPhaseFun_coeFn s ξ, Lp.coeFn_smul c ξ]
    with x e1 e2 e3 e4
  simp only [e1, e2, Pi.smul_apply, e3, e4, smul_comm (modSymbol s x) c]

theorem dualPhaseFun_norm_le (s : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    ‖dualPhaseFun s ξ‖ ≤ ‖ξ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [dualPhaseFun_coeFn s ξ] with x e1
  rw [e1, norm_smul, norm_modSymbol, one_mul]

/-- **The dual-phase unitary** `V_s` on `L²(ℝ;H)`: `(V_s ξ)(x) = e^{isx}·ξ(x)`. -/
noncomputable def dualPhase (s : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := dualPhaseFun s
      map_add' := dualPhaseFun_add s
      map_smul' := dualPhaseFun_smul s }
    1 (fun ξ => by simpa using dualPhaseFun_norm_le s ξ)

theorem dualPhase_coeFn (s : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    dualPhase s ξ =ᵐ[volume] fun x => modSymbol s x • ξ x :=
  dualPhaseFun_coeFn s ξ

/-- `V_{−s} V_s = 1` — the phase is invertible. -/
theorem dualPhase_neg_comp (s : ℝ) :
    (dualPhase (-s) : Lp H 2 (volume : Measure ℝ) →L[ℂ] _) ∘L dualPhase s = 1 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, Lp.ext_iff]
  filter_upwards [dualPhase_coeFn (-s) (dualPhase s ξ), dualPhase_coeFn s ξ] with x e1 e2
  rw [e1, e2, smul_smul, modSymbol_neg_mul, one_smul]

/-- The phase group law `V_{s+r} = V_s ∘ V_r`. -/
theorem dualPhase_add (s r : ℝ) :
    (dualPhase (s + r) : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = dualPhase s ∘L dualPhase r := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, Lp.ext_iff]
  filter_upwards [dualPhase_coeFn (s + r) ξ, dualPhase_coeFn s (dualPhase r ξ),
    dualPhase_coeFn r ξ] with x e1 e2 e3
  rw [e1, e2, e3, smul_smul, modSymbol_add_left]

/-- **THE DUAL ACTION** `θ_s(T) := V_{−s} T V_s` — the Takesaki dual ℝ-action as conjugation on `B(L²(ℝ;H))`. -/
noncomputable def dualAction (s : ℝ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  dualPhase (-s) ∘L T ∘L dualPhase s

/-- The matter rep's fiber (the `matterRep`-level form of `matterRepFun_coeFn`). -/
theorem matterRep_coeFn' (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    matterRep S a ξ =ᵐ[volume] fun x => modularAut S (-x) a (ξ x) :=
  matterRepFun_coeFn S a ξ

/-- **θ_s fixes the matter** `θ_s(π(a)) = π(a)`: the phase is scalar in each fiber. -/
theorem dualAction_matter (S : StandardSubspace H) (s : ℝ) (a : H →L[ℂ] H) :
    dualAction s (matterRep S a) = matterRep S a := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [dualAction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Lp.ext_iff]
  have hmid : matterRep S a (dualPhase s ξ)
      =ᵐ[volume] fun x => modularAut S (-x) a ((dualPhase s ξ) x) := matterRep_coeFn' S a _
  filter_upwards [dualPhase_coeFn (-s) (matterRep S a (dualPhase s ξ)), hmid,
    dualPhase_coeFn s ξ, matterRep_coeFn' S a ξ] with x e1 e2 e3 e4
  rw [e1, e2, e3, e4, map_smul, smul_smul, modSymbol_neg_mul, one_smul]

/-- **θ_s phases the clock** `θ_s(λ_t) = e^{ist}·λ_t` — the vector-valued Weyl relation. -/
theorem dualAction_clock (s t : ℝ) :
    dualAction s (clockTransl t : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = Complex.exp (↑(s * t) * Complex.I) • clockTransl t := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [dualAction, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Lp.ext_iff]
  have hqm := (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving
  have h2 : (fun x => (dualPhase s ξ : ℝ → H) (x + t))
      =ᵐ[volume] fun x => modSymbol s (x + t) • (ξ : ℝ → H) (x + t) :=
    hqm.tendsto_ae.eventually (dualPhase_coeFn s ξ)
  filter_upwards [dualPhase_coeFn (-s) (clockTransl t (dualPhase s ξ)),
    clockTransl_coeFn t (dualPhase s ξ), h2,
    Lp.coeFn_smul (Complex.exp (↑(s * t) * Complex.I)) (clockTransl t ξ),
    clockTransl_coeFn t ξ] with x e1 e2 e3 e4 e5
  rw [e1, e2, e3, e4]
  simp only [Pi.smul_apply]
  rw [e5, smul_smul, modSymbol_add_right]
  rw [show modSymbol (-s) x * (Complex.exp (↑(s * t) * Complex.I) * modSymbol s x)
      = Complex.exp (↑(s * t) * Complex.I) * (modSymbol (-s) x * modSymbol s x) from by ring,
    modSymbol_neg_mul, mul_one]

/-- The dual action's group law `θ_{s+r} = θ_r ∘ θ_s`. -/
theorem dualAction_add (s r : ℝ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    dualAction (s + r) T = dualAction r (dualAction s T) := by
  simp only [dualAction]
  have h1 : (dualPhase (-(s + r)) : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = dualPhase (-r) ∘L dualPhase (-s) := by
    rw [show -(s + r) = -r + -s from by ring, dualPhase_add]
  have h2 : (dualPhase (s + r) : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = dualPhase s ∘L dualPhase r := dualPhase_add s r
  rw [h1, h2]
  simp only [← ContinuousLinearMap.comp_assoc]

/-- θ_s is multiplicative (a conjugation): `θ_s(T·U) = θ_s(T)·θ_s(U)`. -/
theorem dualAction_mul (s : ℝ)
    (T U : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    dualAction s (T ∘L U) = dualAction s T ∘L dualAction s U := by
  simp only [dualAction]
  have h : (dualPhase s : Lp H 2 (volume : Measure ℝ) →L[ℂ] _) ∘L dualPhase (-s) = 1 := by
    have := dualPhase_neg_comp (H := H) (-s)
    rwa [neg_neg] at this
  simp only [ContinuousLinearMap.comp_assoc]
  congr 2
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, h,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

end QIQTH.StandardSubspaceModular
