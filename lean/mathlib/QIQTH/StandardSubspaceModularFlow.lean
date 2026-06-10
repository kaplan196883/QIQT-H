/-
  Phase 3′ continuation (Track B): the continuum modular flow `Δ^{it}` of a standard subspace,
  via the Rieffel–Van Daele bounded transform and the project's axiom-free bounded BOREL functional
  calculus (`QIQTH.SpectralTheorem.borelFC`, from `PVM_of_selfAdjoint`).

  With `R = P + Q` (`rvdRC S`, bounded self-adjoint, `0 ≤ R ≤ 2`), the RvD modular operator is
  `Δ = (2−R)·R⁻¹` (a Möbius function of `R`, generally UNBOUNDED), and the modular flow is

      Δ^{it} = u_t(R),    u_t(r) = exp(i·t·log((2−r)/r))   on r ∈ (0,2), = 1 at the endpoints.

  `u_t` is a globally bounded BOREL function, DISCONTINUOUS at the spectral endpoints r = 0, 2 — so
  continuous `cfc` genuinely cannot reach `Δ^{it}`; the bounded Borel FC is essential.  We build
  `U_t := u_t(R) = borelFC (rvdRC S) … u_t` and prove it is a one-parameter UNITARY GROUP:
  `U_0 = 1`, `U_{s+t} = U_s · U_t` (from `borelFC_mul` + the pointwise group law of `u_t`),
  `U_t⋆ = U_{-t}` (from the adjoint relation `Φ(f)⋆ = Φ(conj f)` + `conj u_t = u_{-t}`), hence unitary.

  This is the genuine continuum modular unitary group at the one-particle / standard-subspace level
  (NOT yet the second-quantized free-field flow `Γ(Δ^{it})`).  Axiom-free.
-/
import QIQTH.StandardSubspaceModular
import QIQTH.Spectral.SpectralTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace QIQTH.StandardSubspaceModular

open ClosedSubmodule StandardSubspace QIQTH.SpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The modular character `u_t(r) = exp(i·t·log((2−r)/r))` -/

/-- The RvD modular character `u_t(r)`, a globally bounded Borel function on `ℝ`: on `(0,2)` it is
    `exp(i·t·log((2−r)/r))`, and `1` outside (the endpoint convention makes the group law hold
    pointwise). -/
noncomputable def modChar (t : ℝ) : ℝ → ℂ :=
  (Set.Ioo (0 : ℝ) 2).piecewise
    (fun r => Complex.exp (Complex.I * (t : ℂ) * (Real.log ((2 - r) / r) : ℂ)))
    (fun _ => 1)

theorem modChar_measurable (t : ℝ) : Measurable (modChar t) := by
  apply Measurable.piecewise measurableSet_Ioo _ measurable_const
  apply Complex.continuous_exp.measurable.comp
  apply Measurable.mul measurable_const
  exact Complex.continuous_ofReal.measurable.comp
    (Real.measurable_log.comp ((measurable_const.sub measurable_id).div measurable_id))

theorem modChar_norm (t r : ℝ) : ‖modChar t r‖ = 1 := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * (Real.log ((2 - r) / r) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero]
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, norm_one]

theorem modChar_zero (r : ℝ) : modChar 0 r = 1 := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · rw [Set.piecewise_eq_of_mem _ _ _ h]
    simp
  · rw [Set.piecewise_eq_of_notMem _ _ _ h]

theorem modChar_add (s t r : ℝ) : modChar (s + t) r = modChar s r * modChar t r := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Set.piecewise_eq_of_mem _ _ _ h,
        Set.piecewise_eq_of_mem _ _ _ h, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, Set.piecewise_eq_of_notMem _ _ _ h,
        Set.piecewise_eq_of_notMem _ _ _ h, mul_one]

theorem modChar_conj (t r : ℝ) : (starRingEnd ℂ) (modChar t r) = modChar (-t) r := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · rw [Set.piecewise_eq_of_mem _ _ _ h, Set.piecewise_eq_of_mem _ _ _ h, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  · rw [Set.piecewise_eq_of_notMem _ _ _ h, Set.piecewise_eq_of_notMem _ _ _ h, map_one]

/-! ### `borelFC` helpers (congruence + adjoint) -/

/-- `borelFC` depends only on the function (not the bound proofs). -/
theorem borelFC_congr (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) {f f' : spectrum ℝ T → ℂ}
    {Cf Cf' : ℝ} (hf : Measurable f) (hCf0 : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hf' : Measurable f') (hCf0' : 0 ≤ Cf') (hCf' : ∀ ω, ‖f' ω‖ ≤ Cf') (h : f = f') :
    borelFC T ha hf hCf0 hCf = borelFC T ha hf' hCf0' hCf' :=
  (PVM_of_selfAdjoint T ha).boundedFC_congr hf hCf0 hCf hf' hCf0' hCf' h

/-- **Adjoint of the bounded Borel FC:** `f(T)⋆ = (conj f)(T)`.  From the hermitian symmetry of the
    polarized bilinear form (`bilinDiag_conj_symm`). -/
theorem borelFC_adjoint (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℂ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C)
    {C' : ℝ} (hcf : Measurable (fun ω => (starRingEnd ℂ) (f ω))) (hC0' : 0 ≤ C')
    (hcfb : ∀ ω, ‖(starRingEnd ℂ) (f ω)‖ ≤ C') :
    ContinuousLinearMap.adjoint (borelFC T ha hf hC0 hC) = borelFC T ha hcf hC0' hcfb := by
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_borelFC, inner_borelFC,
      (PVM_of_selfAdjoint T ha).bilinDiag_conj_symm]

/-! ### The continuum modular unitary group `U_t = u_t(R) = Δ^{it}` -/

/-- `u_t` restricted to the spectrum of `R` — the function fed to the bounded Borel FC. -/
noncomputable def modSpecFun (S : StandardSubspace H) (t : ℝ) : spectrum ℝ (rvdRC S) → ℂ :=
  fun ω => modChar t ω.val

theorem modSpecFun_measurable (S : StandardSubspace H) (t : ℝ) : Measurable (modSpecFun S t) :=
  (modChar_measurable t).comp measurable_subtype_coe

theorem modSpecFun_norm_le (S : StandardSubspace H) (t : ℝ) (ω : spectrum ℝ (rvdRC S)) :
    ‖modSpecFun S t ω‖ ≤ 1 := le_of_eq (modChar_norm t ω.val)

/-- `R = rvdRC S` is self-adjoint (it is positive). -/
theorem rvdRC_isSelfAdjoint (S : StandardSubspace H) : IsSelfAdjoint (rvdRC S) :=
  IsSelfAdjoint.of_nonneg (rvdRC_nonneg S)

/-- **The continuum modular unitary `U_t = Δ^{it} = u_t(R)`** via the bounded Borel FC of `R`. -/
noncomputable def modUnitary (S : StandardSubspace H) (t : ℝ) : H →L[ℂ] H :=
  borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) (modSpecFun_measurable S t) zero_le_one
    (modSpecFun_norm_le S t)

/-- **`U_0 = 1`.** -/
theorem modUnitary_zero (S : StandardSubspace H) : modUnitary S 0 = 1 := by
  rw [modUnitary,
      borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) (modSpecFun_measurable S 0) zero_le_one
        (modSpecFun_norm_le S 0) measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl)
        (funext fun ω => modChar_zero ω.val),
      borelFC_one]

/-- **Group law `U_{s+t} = U_s · U_t`** — from `borelFC_mul` and the pointwise law `u_{s+t}=u_s·u_t`. -/
theorem modUnitary_add (S : StandardSubspace H) (s t : ℝ) :
    modUnitary S (s + t) = modUnitary S s * modUnitary S t := by
  have hpm : Measurable (fun ω => modSpecFun S s ω * modSpecFun S t ω) :=
    (modSpecFun_measurable S s).mul (modSpecFun_measurable S t)
  have hpb : ∀ ω, ‖modSpecFun S s ω * modSpecFun S t ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_one₀ (modSpecFun_norm_le S s ω) (norm_nonneg _) (modSpecFun_norm_le S t ω)
  rw [modUnitary, modUnitary, modUnitary,
      ← borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S)
        (modSpecFun_measurable S s) zero_le_one (modSpecFun_norm_le S s)
        (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t) hpm zero_le_one hpb]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) (modSpecFun_measurable S (s + t))
    zero_le_one (modSpecFun_norm_le S (s + t)) hpm zero_le_one hpb
    (funext fun ω => modChar_add s t ω.val)

/-- **`U_t⋆ = U_{-t}`** — from the adjoint relation `Φ(f)⋆ = Φ(conj f)` and `conj u_t = u_{-t}`. -/
theorem modUnitary_adjoint (S : StandardSubspace H) (t : ℝ) :
    ContinuousLinearMap.adjoint (modUnitary S t) = modUnitary S (-t) := by
  have hcm : Measurable (fun ω => (starRingEnd ℂ) (modSpecFun S t ω)) :=
    Complex.continuous_conj.measurable.comp (modSpecFun_measurable S t)
  have hcb : ∀ ω, ‖(starRingEnd ℂ) (modSpecFun S t ω)‖ ≤ 1 := fun ω => by
    rw [RCLike.norm_conj]; exact modSpecFun_norm_le S t ω
  rw [modUnitary, modUnitary,
      borelFC_adjoint (rvdRC S) (rvdRC_isSelfAdjoint S) (modSpecFun_measurable S t) zero_le_one
        (modSpecFun_norm_le S t) hcm zero_le_one hcb]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) hcm zero_le_one hcb
    (modSpecFun_measurable S (-t)) zero_le_one (modSpecFun_norm_le S (-t))
    (funext fun ω => modChar_conj t ω.val)

/-- **`U_t` is unitary** (`U_t⋆U_t = 1 = U_t U_t⋆`). The continuum modular unitary group. -/
theorem modUnitary_unitary (S : StandardSubspace H) (t : ℝ) :
    modUnitary S t ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.star_eq_adjoint, modUnitary_adjoint, ← modUnitary_add,
        neg_add_cancel, modUnitary_zero]
  · rw [ContinuousLinearMap.star_eq_adjoint, modUnitary_adjoint, ← modUnitary_add,
        add_neg_cancel, modUnitary_zero]

end QIQTH.StandardSubspaceModular
