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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ParametricIntegral

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

/-! ### Bridge: the PVM scalar measure equals the construction's spectral measure -/

set_option maxHeartbeats 1000000 in
/-- **`scalarMeasure(PVM_of_selfAdjoint) = specMeasure`.**  The PVM's scalar measure
    `μ_x(s) = ‖E(s)x‖²` (with `E = specProj` a projection, so `‖E(s)x‖² = re⟪E(s)x,x⟫ = qForm = μ_x^{spec}(s)`)
    agrees with the Riesz–Markov spectral measure.  This connects the bounded-Borel-FC layer
    (`diagInt`/`bilinDiag`, on `scalarMeasure`) to the integral spectral theorem
    `re_inner_T_eq_integral` (on `specMeasure`). -/
theorem scalarMeasure_eq_specMeasure (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) (x : H) :
    (PVM_of_selfAdjoint T ha).scalarMeasure x = specMeasure T ha x := by
  apply MeasureTheory.Measure.ext
  intro s hs
  have hErfl : (PVM_of_selfAdjoint T ha).E s = specProj T ha s := rfl
  have hidem : specProj T ha s * specProj T ha s = specProj T ha s := by
    have h := specProj_inter T ha hs hs
    rw [Set.inter_self] at h
    exact h.symm
  have hi : specProj T ha s (specProj T ha s x) = specProj T ha s x := by
    have := DFunLike.congr_fun hidem x
    rwa [ContinuousLinearMap.mul_apply] at this
  have hadj : ContinuousLinearMap.adjoint (specProj T ha s) = specProj T ha s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact (specProj_isSelfAdjoint T ha s).star_eq
  have hee : inner ℂ (specProj T ha s x) (specProj T ha s x)
      = inner ℂ (specProj T ha s x) x := by
    have h := ContinuousLinearMap.adjoint_inner_right (specProj T ha s) (specProj T ha s x) x
    rw [hadj, hi] at h
    exact h
  have hnorm : ‖specProj T ha s x‖ ^ 2 = qForm T ha s x := by
    rw [← reApplyInnerSelf_specProj T ha s x, ContinuousLinearMap.reApplyInnerSelf_apply,
        ← inner_self_eq_norm_sq (𝕜 := ℂ), hee]
  rw [(PVM_of_selfAdjoint T ha).scalarMeasure_apply x hs, hErfl, hnorm, qForm,
      MeasureTheory.measureReal_def,
      ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top (specMeasure T ha x) s)]

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

/-! ### Strong continuity of the modular flow `t ↦ U_t ξ`

Strong (not norm — that fails: `‖u_t − u_s‖_∞ ↛ 0` near the endpoints) continuity, via the sequential
criterion and the bounded-Borel-FC dominated-convergence engine
(`tendsto_inner_boundedFC_of_dominated`): `u_t(r) → 1` pointwise as `t → 0`, all bounded by `1`. -/

/-- `U_t` is an isometry (`‖U_t ξ‖ = ‖ξ‖`), from unitarity. -/
theorem modUnitary_norm (S : StandardSubspace H) (t : ℝ) (ξ : H) :
    ‖modUnitary S t ξ‖ = ‖ξ‖ := by
  have hu := (Unitary.mem_iff.mp (modUnitary_unitary S t)).1
  have key : inner ℂ (modUnitary S t ξ) (modUnitary S t ξ) = inner ℂ ξ ξ := by
    rw [← ContinuousLinearMap.adjoint_inner_right (modUnitary S t) ξ (modUnitary S t ξ),
        ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.star_eq_adjoint, hu,
        ContinuousLinearMap.one_apply]
  have hre : ‖modUnitary S t ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), key]
  rw [← Real.sqrt_sq (norm_nonneg (modUnitary S t ξ)), ← Real.sqrt_sq (norm_nonneg ξ), hre]

/-- **Inner cocycle identity:** `⟪U_a ξ, U_b ξ⟫ = ⟪ξ, U_{b−a} ξ⟫`. -/
theorem inner_modUnitary_modUnitary (S : StandardSubspace H) (a b : ℝ) (ξ : H) :
    inner ℂ (modUnitary S a ξ) (modUnitary S b ξ) = inner ℂ ξ (modUnitary S (b - a) ξ) := by
  have hop : ContinuousLinearMap.adjoint (modUnitary S a) * modUnitary S b
      = modUnitary S (b - a) := by
    rw [modUnitary_adjoint, ← modUnitary_add, neg_add_eq_sub]
  rw [← ContinuousLinearMap.adjoint_inner_right (modUnitary S a) ξ (modUnitary S b ξ),
      ← ContinuousLinearMap.mul_apply, hop]

/-- `t ↦ u_t(r)` is continuous (for each fixed `r`) — the pointwise input to strong continuity. -/
theorem modChar_continuous (r : ℝ) : Continuous (fun t => modChar t r) := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · simp only [Set.piecewise_eq_of_mem _ _ _ h]
    exact Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  · simp only [Set.piecewise_eq_of_notMem _ _ _ h]
    exact continuous_const

/-- **★ Strong continuity:** `t ↦ U_t ξ` is continuous — so `Δ^{it}` is a STRONGLY CONTINUOUS
    one-parameter unitary group (the full textbook definition of the modular flow; note norm
    continuity FAILS near the spectral endpoints).  Proof: sequential criterion + the bounded-Borel-FC
    dominated-convergence engine, `‖U_{t_n}ξ − U_aξ‖² = 2‖ξ‖² − 2·Re⟪ξ, U_{a−t_n}ξ⟫ → 0` since
    `u_{a−t_n} → 1` pointwise (bounded by 1). -/
theorem modUnitary_stronglyContinuous (S : StandardSubspace H) (ξ : H) :
    Continuous (fun t => modUnitary S t ξ) := by
  rw [continuous_iff_seqContinuous]
  intro u a hu
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ha : IsSelfAdjoint (rvdRC S) := rvdRC_isSelfAdjoint S
  set P := PVM_of_selfAdjoint (rvdRC S) ha with hP
  -- pointwise convergence `u_{a−u n} → 1`
  have hptw : ∀ ω, Filter.Tendsto (fun n => modSpecFun S (a - u n) ω) Filter.atTop
      (nhds ((fun _ => (1 : ℂ)) ω)) := by
    intro ω
    have h0 : Filter.Tendsto (fun n => a - u n) Filter.atTop (nhds 0) := by
      simpa using hu.const_sub a
    have hc := ((modChar_continuous ω.val).tendsto 0).comp h0
    simpa [modSpecFun, modChar_zero] using hc
  -- inner products converge: `⟪ξ, U_{a−u n}ξ⟫ → ⟪ξ, ξ⟫`
  have hinner : Filter.Tendsto (fun n => inner ℂ ξ (modUnitary S (a - u n) ξ)) Filter.atTop
      (nhds (inner ℂ ξ ξ)) := by
    have heng := P.tendsto_inner_boundedFC_of_dominated (f := fun n => modSpecFun S (a - u n))
      (g := fun _ => (1 : ℂ)) zero_le_one (fun n => modSpecFun_measurable S (a - u n))
      measurable_const (fun n ω => modSpecFun_norm_le S (a - u n) ω)
      (fun ω => le_of_eq norm_one) hptw ξ ξ
    rw [P.inner_boundedFC, P.bilinDiag_const, one_mul] at heng
    exact heng
  -- the squared norm
  have hform : ∀ n, ‖modUnitary S (u n) ξ - modUnitary S a ξ‖ ^ 2
      = 2 * ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ (modUnitary S (a - u n) ξ)).re := by
    intro n
    rw [norm_sub_sq_real, modUnitary_norm, modUnitary_norm]
    have hib : (inner ℝ (modUnitary S (u n) ξ) (modUnitary S a ξ))
        = (inner ℂ ξ (modUnitary S (a - u n) ξ)).re := by
      show (inner ℂ (modUnitary S (u n) ξ) (modUnitary S a ξ)).re = _
      rw [inner_modUnitary_modUnitary]
    rw [hib]; ring
  -- ‖·‖² → 0, then ‖·‖ → 0
  have hself : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  have hsq : Filter.Tendsto (fun n => ‖modUnitary S (u n) ξ - modUnitary S a ξ‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n => (inner ℂ ξ (modUnitary S (a - u n) ξ)).re)
        Filter.atTop (nhds ((inner ℂ ξ ξ).re)) := (Complex.continuous_re.tendsto _).comp hinner
    have hlim : Filter.Tendsto
        (fun n => 2 * ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ (modUnitary S (a - u n) ξ)).re)
        Filter.atTop (nhds (2 * ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ ξ).re)) :=
      (hg.const_mul 2).const_sub (2 * ‖ξ‖ ^ 2)
    rw [hself, show (2 * ‖ξ‖ ^ 2 - 2 * ‖ξ‖ ^ 2) = 0 by ring] at hlim
    simpa only [hform] using hlim
  have hfin := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp, Real.sqrt_zero] at hfin
  exact Filter.Tendsto.congr (fun n => Real.sqrt_sq (norm_nonneg _)) hfin

/-! ### Toward standard-subspace invariance `U_t 𝒦 = 𝒦`

`𝒦`'s real-orthogonal projection is `P = ½(R + D)` (RvD: `P = (1+Δ)⁻¹ + JΔ^{1/2}(1+Δ)⁻¹`).  So
`U_t` preserves `𝒦` as soon as it commutes with both `R` and `D`.  The structural reduction is done
here; the two commutators are the remaining analytic obligations:
  • `[U_t, R] = 0` — `U_t` is a function of `R`; reachable once `R = borelFC(id)` (polarize
    `re_inner_T_eq_integral`).
  • `[U_t, D] = 0` — the **covariance** `D·f(R) = conj(f(2−·))(R)·D` (here `conj(u_t(2−r)) = u_t(r)`).
    `D` is antilinear and conjugates the spectrum of `R` via `r ↦ 2−r` (`rvdPmQ_mul_rvdR`); this needs
    antilinear conjugation of the bounded Borel FC — the genuine frontier (no Mathlib infrastructure). -/

/-- **`R + D = 2·P`** (RvD `P = ½(R+D)`): `(P+Q) + (P−Q) = 2P`. -/
theorem rvdR_add_rvdPmQ_eq (S : StandardSubspace H) :
    rvdR S + rvdPmQ S = (2 : ℝ) • projK S := by
  rw [rvdR, rvdPmQ, two_smul]
  abel

/-- `𝒦`-membership via its projection: `ξ ∈ 𝒦 ↔ P ξ = ξ`. -/
theorem mem_K_iff_projK (S : StandardSubspace H) (ξ : H) :
    ξ ∈ S.toClosedSubmodule ↔ projK S ξ = ξ := by
  rw [projK, Submodule.starProjection_eq_self_iff, mem_toSubmodule_iff]

/-- **Reduction of `[U_t, P] = 0` to `[U_t, R] = 0 ∧ [U_t, D] = 0`** via `P = ½(R+D)`. -/
theorem modUnitary_commute_projK_of (S : StandardSubspace H) (t : ℝ) (ξ : H)
    (hR : modUnitary S t (rvdR S ξ) = rvdR S (modUnitary S t ξ))
    (hD : modUnitary S t (rvdPmQ S ξ) = rvdPmQ S (modUnitary S t ξ)) :
    modUnitary S t (projK S ξ) = projK S (modUnitary S t ξ) := by
  have hP : ∀ η, (2 : ℝ) • projK S η = rvdR S η + rvdPmQ S η := fun η => by
    have h := congrArg (fun A => (A : H →L[ℝ] H) η) (rvdR_add_rvdPmQ_eq S)
    simpa using h.symm
  have key : (2 : ℝ) • projK S (modUnitary S t ξ) = (2 : ℝ) • modUnitary S t (projK S ξ) := by
    rw [hP, ← hR, ← hD, ← map_add, ← hP, ContinuousLinearMap.map_smul_of_tower]
  exact (smul_right_injective H (two_ne_zero) key).symm

/-- **Conditional standard-subspace invariance:** if `U_t` commutes with `R` and `D` (pointwise),
    then `U_t 𝒦 ⊆ 𝒦`.  With unitarity this gives `U_t 𝒦 = 𝒦` — the property certifying `Δ^{it}` is the
    modular flow OF `𝒦`.  The hypotheses are the two commutators isolated above. -/
theorem modUnitary_mapsTo_K_of_commute (S : StandardSubspace H) (t : ℝ)
    (hR : ∀ ξ, modUnitary S t (rvdR S ξ) = rvdR S (modUnitary S t ξ))
    (hD : ∀ ξ, modUnitary S t (rvdPmQ S ξ) = rvdPmQ S (modUnitary S t ξ)) :
    ∀ ξ ∈ S.toClosedSubmodule, modUnitary S t ξ ∈ S.toClosedSubmodule := by
  intro ξ hξ
  rw [mem_K_iff_projK] at hξ ⊢
  rw [← modUnitary_commute_projK_of S t ξ (hR ξ) (hD ξ), hξ]

/-- **★ `U_t` commutes with every spectral projection `E(s)` of `R`.**  Both `U_t = Φ(u_t)` and
    `E(s) = Φ(𝟙_s)` are values of the bounded Borel FC of `R`, and the FC is multiplicative with
    `u_t · 𝟙_s = 𝟙_s · u_t` pointwise.  So `U_t` lies in the von Neumann algebra generated by `R` —
    the operator-level statement that `Δ^{it}` is a function of `R`.  (The pointwise `[U_t, R] = 0`
    then follows once `R = ∫λ dE`; the `[U_t, D] = 0` covariance remains the frontier.) -/
theorem modUnitary_commute_specProj (S : StandardSubspace H) (t : ℝ)
    {s : Set (spectrum ℝ (rvdRC S))} (hs : MeasurableSet s) :
    modUnitary S t * (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E s
      = (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).E s * modUnitary S t := by
  set P := PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S) with hPP
  have hi : Measurable (s.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs
  have hfg : ∀ ω, ‖modSpecFun S t ω * s.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_one₀ (modSpecFun_norm_le S t ω) (norm_nonneg _) (QIQTH.Spectral.ProjectionValuedMeasure.norm_indicatorOne_le s ω)
  have hgf : ∀ ω, ‖s.indicator (fun _ => (1 : ℂ)) ω * modSpecFun S t ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_one₀ (QIQTH.Spectral.ProjectionValuedMeasure.norm_indicatorOne_le s ω) (norm_nonneg _) (modSpecFun_norm_le S t ω)
  rw [show modUnitary S t = P.boundedFC (modSpecFun_measurable S t) zero_le_one
        (modSpecFun_norm_le S t) from rfl, ← P.boundedFC_indicator hs,
      ← P.boundedFC_mul (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t)
        hi zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_indicatorOne_le s) ((modSpecFun_measurable S t).mul hi) zero_le_one hfg,
      ← P.boundedFC_mul hi zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_indicatorOne_le s) (modSpecFun_measurable S t)
        zero_le_one (modSpecFun_norm_le S t) (hi.mul (modSpecFun_measurable S t)) zero_le_one hgf]
  exact P.boundedFC_congr ((modSpecFun_measurable S t).mul hi) zero_le_one hfg
    (hi.mul (modSpecFun_measurable S t)) zero_le_one hgf (funext fun ω => mul_comm _ _)

/-! ### `R = ∫λ dE` and the literal `[U_t, R] = 0` -/

/-- Two values of the bounded Borel FC commute (multiplicative + scalar functions commute). -/
theorem borelFC_comm (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) {f g : spectrum ℝ T → ℂ}
    {Cf Cg Cfg Cgf : ℝ}
    (hf : Measurable f) (hC0f : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hg : Measurable g) (hC0g : 0 ≤ Cg) (hCg : ∀ ω, ‖g ω‖ ≤ Cg)
    (hfg : Measurable (fun ω => f ω * g ω)) (hC0fg : 0 ≤ Cfg) (hCfg : ∀ ω, ‖f ω * g ω‖ ≤ Cfg)
    (hgf : Measurable (fun ω => g ω * f ω)) (hC0gf : 0 ≤ Cgf) (hCgf : ∀ ω, ‖g ω * f ω‖ ≤ Cgf) :
    borelFC T ha hf hC0f hCf * borelFC T ha hg hC0g hCg
      = borelFC T ha hg hC0g hCg * borelFC T ha hf hC0f hCf := by
  rw [← borelFC_mul T ha hf hC0f hCf hg hC0g hCg hfg hC0fg hCfg,
      ← borelFC_mul T ha hg hC0g hCg hf hC0f hCf hgf hC0gf hCgf]
  exact borelFC_congr T ha hfg hC0fg hCfg hgf hC0gf hCgf (funext fun ω => mul_comm _ _)

/-- The coordinate function `λ ↦ λ` on `σ(R)` — the integrand of `R = ∫λ dE`. -/
noncomputable def specCoord (S : StandardSubspace H) : spectrum ℝ (rvdRC S) → ℂ :=
  fun ω => ((ω : ℝ) : ℂ)

theorem specCoord_measurable (S : StandardSubspace H) : Measurable (specCoord S) :=
  Complex.continuous_ofReal.measurable.comp measurable_subtype_coe

theorem specCoord_norm_le (S : StandardSubspace H) (ω : spectrum ℝ (rvdRC S)) :
    ‖specCoord S ω‖ ≤ ‖rvdRC S‖ * ‖(1 : H →L[ℂ] H)‖ := by
  rw [specCoord, Complex.norm_real]
  exact spectrum.norm_le_norm_mul_of_mem ω.2

/-- `diagInt(coord) z = ⟪z, R z⟫` (the `scalarMeasure=specMeasure` bridge + `re_inner_T_eq_integral`
    + self-adjoint realness). -/
theorem diagInt_specCoord (S : StandardSubspace H) (z : H) :
    (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S) z
      = inner ℂ z (rvdRC S z) := by
  rw [show (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S) z
        = ∫ ω, ((ω : ℝ) : ℂ)
            ∂((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).scalarMeasure z)
      from rfl, scalarMeasure_eq_specMeasure,
      show (∫ ω, ((ω : ℝ) : ℂ) ∂(specMeasure (rvdRC S) (rvdRC_isSelfAdjoint S) z))
        = (((∫ ω, (ω : ℝ) ∂(specMeasure (rvdRC S) (rvdRC_isSelfAdjoint S) z)) : ℝ) : ℂ)
      from integral_ofReal, re_inner_T_eq_integral]
  have hreal : (starRingEnd ℂ) (inner ℂ z (rvdRC S z)) = inner ℂ z (rvdRC S z) := by
    rw [inner_conj_symm]; exact rvdRC_isSymmetric S z z
  exact Complex.conj_eq_iff_re.mp hreal

/-- **`R = borelFC(coord) = ∫λ dE`** — the operator spectral theorem for `R`, via polarization. -/
theorem rvdRC_eq_borelFC (S : StandardSubspace H) :
    rvdRC S = borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) (specCoord_measurable S)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (specCoord_norm_le S) := by
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [inner_borelFC,
      show (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).bilinDiag (specCoord S) x y
        = 4⁻¹ * ((PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S) (x + y)
          - (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S) (x - y)
          + Complex.I *
              (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S)
                (Complex.I • x + y)
          - Complex.I *
              (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).diagInt (specCoord S)
                (Complex.I • x - y)) from rfl,
      diagInt_specCoord, diagInt_specCoord, diagInt_specCoord, diagInt_specCoord]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **★ `[U_t, R] = 0`** (operator form): the modular flow commutes with `R`. -/
theorem modUnitary_commute_rvdRC (S : StandardSubspace H) (t : ℝ) :
    modUnitary S t * rvdRC S = rvdRC S * modUnitary S t := by
  have hfg : ∀ ω, ‖modSpecFun S t ω * specCoord S ω‖ ≤ 1 * (‖rvdRC S‖ * ‖(1 : H →L[ℂ] H)‖) :=
    fun ω => by
      rw [norm_mul]
      exact mul_le_mul (modSpecFun_norm_le S t ω) (specCoord_norm_le S ω) (norm_nonneg _) zero_le_one
  have hgf : ∀ ω, ‖specCoord S ω * modSpecFun S t ω‖ ≤ (‖rvdRC S‖ * ‖(1 : H →L[ℂ] H)‖) * 1 :=
    fun ω => by
      rw [norm_mul]
      exact mul_le_mul (specCoord_norm_le S ω) (modSpecFun_norm_le S t ω) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h := borelFC_comm (rvdRC S) (rvdRC_isSelfAdjoint S)
    (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t)
    (specCoord_measurable S) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (specCoord_norm_le S)
    ((modSpecFun_measurable S t).mul (specCoord_measurable S)) (by positivity) hfg
    ((specCoord_measurable S).mul (modSpecFun_measurable S t)) (by positivity) hgf
  rwa [← rvdRC_eq_borelFC S] at h

/-- **`[U_t, R] = 0`** (pointwise on `rvdR`): `U_t(R ξ) = R(U_t ξ)`. -/
theorem modUnitary_commute_rvdR (S : StandardSubspace H) (t : ℝ) (ξ : H) :
    modUnitary S t (rvdR S ξ) = rvdR S (modUnitary S t ξ) := by
  have h := DFunLike.congr_fun (modUnitary_commute_rvdRC S t) ξ
  simp only [ContinuousLinearMap.mul_apply, rvdRC_apply] at h
  exact h

/-- **Standard-subspace invariance modulo the covariance:** with `[U_t,R]=0` discharged,
    `U_t 𝒦 ⊆ 𝒦` follows from the SINGLE remaining obligation `[U_t, D] = 0` (the covariance). -/
theorem modUnitary_mapsTo_K_of_commute_D (S : StandardSubspace H) (t : ℝ)
    (hD : ∀ ξ, modUnitary S t (rvdPmQ S ξ) = rvdPmQ S (modUnitary S t ξ)) :
    ∀ ξ ∈ S.toClosedSubmodule, modUnitary S t ξ ∈ S.toClosedSubmodule :=
  modUnitary_mapsTo_K_of_commute S t (modUnitary_commute_rvdR S t) hD

/-! ### ★ The antilinear-CFC commutation `D·T = T·D` (the `J²=1` / covariance keystone)

`D = P−Q` is an antilinear (ℝ-linear) bounded self-adjoint operator.  The **real commutant**
`{Y : H→L[ℂ]H | D∘Y = Y∘D}` (composition as ℝ-maps) is a closed real `*`-subalgebra; if it contains
a self-adjoint `B` it contains `elemental ℝ B`, hence `√B = CFC.sqrt B`.  Applied to `B = A = T²`
(which `D` commutes with trivially, `A = D²`), this gives `D·T = T·D`. -/

/-- ℂ-adjoint restricted to ℝ equals the ℝ-adjoint (no direct Mathlib lemma). -/
theorem restrictScalars_star (Y : H →L[ℂ] H) :
    (star Y).restrictScalars ℝ = star (Y.restrictScalars ℝ) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  refine ContinuousLinearMap.ext fun x => ext_inner_left ℝ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  change (inner ℂ y ((ContinuousLinearMap.adjoint Y) x)).re = (inner ℂ (Y y) x).re
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The **real commutant** of a self-adjoint `D : H →L[ℝ] H`, as a real `*`-subalgebra of
    `H →L[ℂ] H` (over `ℝ` only, since `D` is antilinear). -/
noncomputable def realCommutant (D : H →L[ℝ] H) (hD : IsSelfAdjoint D) :
    StarSubalgebra ℝ (H →L[ℂ] H) where
  carrier := {Y | D * Y.restrictScalars ℝ = Y.restrictScalars ℝ * D}
  mul_mem' := fun {Y₁ Y₂} h₁ h₂ => by
    simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
    rw [show (Y₁ * Y₂).restrictScalars ℝ = Y₁.restrictScalars ℝ * Y₂.restrictScalars ℝ from rfl,
        ← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [show (1 : H →L[ℂ] H).restrictScalars ℝ = 1 from rfl, mul_one, one_mul]
  add_mem' := fun {Y₁ Y₂} h₁ h₂ => by
    simp only [Set.mem_setOf_eq] at h₁ h₂ ⊢
    rw [show (Y₁ + Y₂).restrictScalars ℝ = Y₁.restrictScalars ℝ + Y₂.restrictScalars ℝ from rfl,
        mul_add, h₁, h₂, add_mul]
  zero_mem' := by simp
  algebraMap_mem' := fun r => by
    simp only [Set.mem_setOf_eq]
    rw [show (algebraMap ℝ (H →L[ℂ] H) r).restrictScalars ℝ = algebraMap ℝ (H →L[ℝ] H) r from rfl,
        Algebra.commutes]
  star_mem' := fun {Y} h => by
    simp only [Set.mem_setOf_eq] at h ⊢
    rw [restrictScalars_star]
    have hs := congrArg star h
    rw [star_mul, star_mul, hD.star_eq] at hs
    exact hs.symm

theorem realCommutant_isClosed (D : H →L[ℝ] H) (hD : IsSelfAdjoint D) :
    IsClosed ((realCommutant D hD : StarSubalgebra ℝ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) := by
  have hcont : Continuous
      (fun Y : H →L[ℂ] H => D * Y.restrictScalars ℝ - Y.restrictScalars ℝ * D) := by
    have hrs : Continuous (fun Y : H →L[ℂ] H => Y.restrictScalars ℝ) := by
      have h := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).continuous
      rwa [ContinuousLinearMap.coe_restrict_scalarsL'] at h
    exact ((continuous_const.mul hrs).sub (hrs.mul continuous_const))
  have hset : ((realCommutant D hD : StarSubalgebra ℝ (H →L[ℂ] H)) : Set (H →L[ℂ] H))
      = (fun Y : H →L[ℂ] H => D * Y.restrictScalars ℝ - Y.restrictScalars ℝ * D) ⁻¹' {0} := by
    ext Y
    simp only [realCommutant, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      sub_eq_zero]
    rfl
  rw [hset]
  exact isClosed_singleton.preimage hcont

/-- **Antilinear-CFC commutation:** `D` (self-adjoint, ℝ-linear) commuting with `B` commutes with
    everything in `elemental ℝ B`. -/
theorem commute_of_mem_elemental (B : H →L[ℂ] H) (D : H →L[ℝ] H) (hD : IsSelfAdjoint D)
    (hc : D * B.restrictScalars ℝ = B.restrictScalars ℝ * D) {Y : H →L[ℂ] H}
    (hY : Y ∈ StarAlgebra.elemental ℝ B) :
    D * Y.restrictScalars ℝ = Y.restrictScalars ℝ * D :=
  StarAlgebra.elemental.le_of_mem (realCommutant_isClosed D hD) hc hY

/-- `CFC.sqrt B ∈ elemental ℝ B` for `0 ≤ B` (via `CFC.sqrt = cfcₙ Real.sqrt = cfc Real.sqrt`). -/
theorem sqrt_mem_elemental (B : H →L[ℂ] H) (hB : 0 ≤ B) :
    CFC.sqrt B ∈ StarAlgebra.elemental ℝ B := by
  rw [CFC.sqrt_eq_real_sqrt B, cfcₙ_eq_cfc]
  exact cfc_mem_elemental Real.sqrt B

/-- **★ `D·T = T·D`** (operator form): the antilinear modular conjugation `D` commutes with the
    positive modulus `T = √(R(2−R))`.  Whence `J = D·T⁻¹` is self-adjoint and `J² = 1`. -/
theorem rvdPmQ_commute_rvdT (S : StandardSubspace H) :
    rvdPmQ S * (rvdT S).restrictScalars ℝ = (rvdT S).restrictScalars ℝ * rvdPmQ S := by
  have hsqrt : CFC.sqrt (rvdRC S * rvdTwoSubRC S) = rvdT S :=
    CFC.sqrt_unique (rvdT_sq S) (rvdT_nonneg S)
  have hApos : (0 : H →L[ℂ] H) ≤ rvdRC S * rvdTwoSubRC S :=
    Commute.mul_nonneg (rvdRC_nonneg S) (rvdTwoSubRC_nonneg S) (rvdRC_commute_rvdTwoSubRC S)
  have hbase : rvdPmQ S * (rvdRC S * rvdTwoSubRC S).restrictScalars ℝ
      = (rvdRC S * rvdTwoSubRC S).restrictScalars ℝ * rvdPmQ S := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    simpa [ContinuousLinearMap.mul_apply] using rvdPmQ_commute_A S ξ
  have hmem : CFC.sqrt (rvdRC S * rvdTwoSubRC S) ∈ StarAlgebra.elemental ℝ (rvdRC S * rvdTwoSubRC S) :=
    sqrt_mem_elemental _ hApos
  have := commute_of_mem_elemental (rvdRC S * rvdTwoSubRC S) (rvdPmQ S) (rvdPmQ_isSelfAdjoint S)
    hbase hmem
  rwa [hsqrt] at this

/-- **★ `D·T = T·D`** (pointwise): `D(T ξ) = T(D ξ)`. -/
theorem rvdPmQ_commute_rvdT_apply (S : StandardSubspace H) (ξ : H) :
    rvdPmQ S (rvdT S ξ) = rvdT S (rvdPmQ S ξ) := by
  have h := DFunLike.congr_fun (rvdPmQ_commute_rvdT S) ξ
  simpa [ContinuousLinearMap.mul_apply] using h

/-! ### ★ The modular conjugation `J` and `J² = 1`

`D = J·T` (polar decomposition).  `J : T ξ ↦ D ξ` is a well-defined ℝ-linear isometry on the dense
`range T` (`‖Tξ‖=‖Dξ‖`, `T` injective ⟹ `range T` dense), extending to all of `H` via
`LinearMap.extendOfNorm`.  `J² = 1` from `J` self-adjoint (`D·T=T·D`) + isometric. -/

/-- `range T` is dense (`T` injective self-adjoint ⟹ `(range T)ᗮ = ker T = ⊥`). -/
theorem rvdT_restrictScalars_denseRange (S : StandardSubspace H) :
    DenseRange ((rvdT S).restrictScalars ℝ) := by
  have hadj : ContinuousLinearMap.adjoint ((rvdT S).restrictScalars ℝ)
      = (rvdT S).restrictScalars ℝ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← restrictScalars_star, (rvdT_isSelfAdjoint S).star_eq]
  have hbot : (LinearMap.range ((rvdT S).restrictScalars ℝ).toLinearMap)ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hadj, LinearMap.ker_eq_bot]
    intro a b hab; exact rvdT_injective S hab
  have hdense : Dense (↑(LinearMap.range ((rvdT S).restrictScalars ℝ).toLinearMap) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
        ← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  rw [DenseRange, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range]
  exact hdense

/-- `D` and `T` are self-adjoint w.r.t. the real inner product. -/
private theorem real_inner_selfAdjoint (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) (x y : H) :
    inner ℝ (A x) y = inner ℝ x (A y) := by
  have hadj : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hA.star_eq]
  conv_lhs => rw [← hadj]
  exact ContinuousLinearMap.adjoint_inner_left A y x

/-- **The modular conjugation `J`** — the ℝ-linear extension of `T ξ ↦ D ξ`. -/
@[irreducible] noncomputable def modConj (S : StandardSubspace H) : H →L[ℝ] H :=
  LinearMap.extendOfNorm (rvdPmQ S).toLinearMap ((rvdT S).restrictScalars ℝ).toLinearMap

theorem modConj_rvdT (S : StandardSubspace H) (ξ : H) :
    modConj S (rvdT S ξ) = rvdPmQ S ξ := by
  rw [modConj]
  exact LinearMap.extendOfNorm_eq (rvdT_restrictScalars_denseRange S)
    ⟨1, fun x => by simp [rvdT_norm_eq]⟩ ξ

/-- `J` is an isometry (`‖J η‖ = ‖η‖`), by density from `‖J(Tξ)‖ = ‖Dξ‖ = ‖Tξ‖`. -/
theorem modConj_norm (S : StandardSubspace H) (η : H) : ‖modConj S η‖ = ‖η‖ := by
  refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
    (modConj S).continuous.norm continuous_norm ?_) η
  rintro v ⟨ξ, rfl⟩
  show ‖modConj S (rvdT S ξ)‖ = ‖rvdT S ξ‖
  rw [modConj_rvdT]
  exact (rvdT_norm_eq S ξ).symm

/-- **`J` preserves the real inner product** (it is an isometry): `⟪J η, J ζ⟫ = ⟪η, ζ⟫`. -/
theorem modConj_inner_map (S : StandardSubspace H) (η ζ : H) :
    inner ℝ (modConj S η) (modConj S ζ) = inner ℝ η ζ :=
  (⟨(modConj S).toLinearMap, modConj_norm S⟩ : H →ₗᵢ[ℝ] H).inner_map_map η ζ

/-- `T` is real-symmetric — via ℂ-self-adjointness (fast: primary ℂ instance, no scoped-ℝ adjoint). -/
theorem rvdT_real_inner_symm (S : StandardSubspace H) (x y : H) :
    inner ℝ (rvdT S x) y = inner ℝ x (rvdT S y) := by
  have hadj : ContinuousLinearMap.adjoint (rvdT S) = rvdT S := by
    rw [← ContinuousLinearMap.star_eq_adjoint, (rvdT_isSelfAdjoint S).star_eq]
  have hc : inner ℂ (rvdT S x) y = inner ℂ x (rvdT S y) := by
    conv_lhs => rw [← hadj]
    exact ContinuousLinearMap.adjoint_inner_left (rvdT S) y x
  show (inner ℂ (rvdT S x) y).re = (inner ℂ x (rvdT S y)).re
  rw [hc]

/-- `D = P − Q` is real-symmetric — via the projection symmetry (fast, no adjoint). -/
theorem rvdPmQ_real_inner_symm (S : StandardSubspace H) (x y : H) :
    inner ℝ (rvdPmQ S x) y = inner ℝ x (rvdPmQ S y) := by
  simp only [rvdPmQ, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, projK, projIK]
  rw [Submodule.inner_starProjection_left_eq_right, Submodule.inner_starProjection_left_eq_right]

/-- `J` is self-adjoint (`⟪J η, ζ⟫ = ⟪η, J ζ⟫`), by density from `D·T=T·D` (using the fast symmetry
    lemmas above — avoids the scoped-ℝ adjoint that times out). -/
theorem modConj_isSelfAdjoint (S : StandardSubspace H) (η ζ : H) :
    inner ℝ (modConj S η) ζ = inner ℝ η (modConj S ζ) := by
  have hT : ∀ a b : H, inner ℝ (modConj S (rvdT S a)) (rvdT S b)
      = inner ℝ (rvdT S a) (modConj S (rvdT S b)) := fun a b => by
    rw [modConj_rvdT, modConj_rvdT, rvdPmQ_real_inner_symm, rvdPmQ_commute_rvdT_apply,
        ← rvdT_real_inner_symm]
  have hηT : ∀ b : H, inner ℝ (modConj S η) (rvdT S b) = inner ℝ η (modConj S (rvdT S b)) := by
    intro b
    refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
      ((modConj S).continuous.inner continuous_const) (continuous_id.inner continuous_const)
      ?_) η
    rintro v ⟨a, rfl⟩
    show inner ℝ (modConj S (rvdT S a)) (rvdT S b) = inner ℝ (rvdT S a) (modConj S (rvdT S b))
    exact hT a b
  refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
    (continuous_const.inner continuous_id)
    (continuous_const.inner (modConj S).continuous) ?_) ζ
  rintro v ⟨b, rfl⟩
  show inner ℝ (modConj S η) (rvdT S b) = inner ℝ η (modConj S (rvdT S b))
  exact hηT b

/-- **★ `J² = 1`** — the modular conjugation is an involution (`⟪ζ, J²η⟫ = ⟪Jζ, Jη⟫ = ⟪ζ, η⟫`). -/
theorem modConj_sq (S : StandardSubspace H) (η : H) : modConj S (modConj S η) = η := by
  refine ext_inner_left ℝ fun ζ => ?_
  rw [← modConj_isSelfAdjoint S ζ (modConj S η), modConj_inner_map]

/-! ### Modular reflection of `R`: `J R J = 2 − R`

  The bounded shadow of the canonical Tomita–Takesaki relation `J Δ J = Δ⁻¹` (with `Δ = (2−R)R⁻¹`):
  the modular conjugation `J` reflects `R` to `2 − R`.  The engine is the anticommutation
  `D(R−1) = −(R−1)D` (`rvdPmQ_anticommute_rvdR_sub_one`), giving `D R = (2−R) D`, transported to `J`
  through `J(Tξ) = Dξ` on the dense range of `T` (using `T,R` commute). -/

/-- `T` commutes with `R` (both are continuous functions of `R`). -/
theorem rvdRC_commute_rvdT (S : StandardSubspace H) : Commute (rvdRC S) (rvdT S) := by
  have hcomm_2R : Commute (rvdRC S) (rvdTwoSubRC S) := rvdRC_commute_rvdTwoSubRC S
  have hSR : Commute (rvdRC S) (rvdSqrtR S) :=
    ((Commute.refl (rvdRC S)).symm.cfcₙ_nnreal NNReal.sqrt).symm
  have hST : Commute (rvdRC S) (rvdSqrtTwoSubR S) :=
    (hcomm_2R.symm.cfcₙ_nnreal NNReal.sqrt).symm
  rw [rvdT]; exact hSR.mul_right hST

/-- `D R = (2 − R) D` pointwise — from the anticommutation `D(R−1) = −(R−1)D`. -/
theorem rvdPmQ_rvdRC (S : StandardSubspace H) (ξ : H) :
    rvdPmQ S (rvdRC S ξ) = rvdTwoSubRC S (rvdPmQ S ξ) := by
  have h := DFunLike.congr_fun (rvdPmQ_anticommute_rvdR_sub_one S) ξ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.neg_apply, map_sub] at h
  rw [rvdTwoSubRC]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  show rvdPmQ S (rvdR S ξ) = _
  rw [two_smul]
  have hRC : rvdRC S (rvdPmQ S ξ) = rvdR S (rvdPmQ S ξ) := rfl
  rw [hRC]; linear_combination (norm := module) h

/-- `J R = (2 − R) J` pointwise (the reflection intertwiner), by density from `range T`. -/
theorem modConj_rvdRC_reflect (S : StandardSubspace H) (ξ : H) :
    modConj S (rvdRC S ξ) = rvdTwoSubRC S (modConj S ξ) := by
  refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
    ((modConj S).continuous.comp (rvdRC S).continuous)
    ((rvdTwoSubRC S).continuous.comp (modConj S).continuous) ?_) ξ
  rintro v ⟨x, rfl⟩
  show modConj S (rvdRC S (rvdT S x)) = rvdTwoSubRC S (modConj S (rvdT S x))
  have hcomm : rvdRC S (rvdT S x) = rvdT S (rvdRC S x) :=
    DFunLike.congr_fun (rvdRC_commute_rvdT S).eq x
  rw [hcomm, modConj_rvdT, modConj_rvdT, rvdPmQ_rvdRC]

/-- **★ `J R J = 2 − R`** — the modular conjugation reflects `R` (the bounded shadow of `J Δ J = Δ⁻¹`).
    One of the canonical Tomita–Takesaki relations, and a prerequisite for the CGP spectral balance. -/
theorem modConj_rvdRC_modConj (S : StandardSubspace H) (ξ : H) :
    modConj S (rvdRC S (modConj S ξ)) = rvdTwoSubRC S ξ := by
  rw [modConj_rvdRC_reflect, modConj_sq]

/-! ### Bounded Tomita fixedness for `ξ ∈ 𝒦`

  The second CGP spectral-balance prerequisite, in bounded form.  The Tomita operator `S = J Δ^{1/2}`
  fixes the standard subspace `𝒦` (`ξ = J Δ^{1/2} ξ` for `ξ ∈ 𝒦`); since `Δ^{1/2}` is unbounded, we use
  the equivalent BOUNDED relation `D ξ = (2 − R) ξ`, immediate from `R = P + Q`, `D = P − Q` and `P ξ = ξ`
  (so `Q ξ = R ξ − ξ` and `D ξ = ξ − Q ξ = 2ξ − R ξ`).  Together with `J R J = 2 − R` this makes the whole
  CGP spectral balance bounded: from `(2−R) ξ = J(T ξ)` one gets `μ_{(2−R)ξ} = μ_{J(Tξ)}`, i.e.
  `∫ (2−r)² F dμ_ξ = ∫ r(2−r) F(2−r) dμ_ξ`, whose `÷r²` is the balance — no `Δ^{1/2}` ever. -/

/-- **Bounded Tomita fixedness:** for `ξ ∈ 𝒦` (`P ξ = ξ`), `D ξ = (2 − R) ξ`. -/
theorem rvdPmQ_eq_of_mem_K (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ) :
    rvdPmQ S ξ = rvdTwoSubRC S ξ := by
  rw [rvdPmQ, rvdTwoSubRC]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  show projK S ξ - projIK S ξ = (2 : ℂ) • ξ - rvdR S ξ
  rw [rvdR, ContinuousLinearMap.add_apply, hξ, two_smul]
  abel

/-- For `ξ ∈ 𝒦`, `J(T ξ) = (2 − R) ξ` — the modular form of the bounded Tomita fixedness, equating the
    two bounded objects whose `R`-spectral measures drive the CGP balance. -/
theorem modConj_rvdT_of_mem_K (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ) :
    modConj S (rvdT S ξ) = rvdTwoSubRC S ξ := by
  rw [modConj_rvdT, rvdPmQ_eq_of_mem_K S hξ]

/-! ### `cfcCont` — the continuous-function bounded FC of `R`, bundled for Stone–Weierstrass

`U_t = u_t(R)` is discontinuous at the spectral endpoints `r = 0, 2`, but `U_t·A` with `A = R(2−R)`
is CONTINUOUS — the `r(2−r)` factor kills the endpoint singularity.  To exploit that for the
covariance `[U_t, D] = 0`, we package the bounded Borel FC restricted to CONTINUOUS functions as a
continuous, `ℂ`-linear, multiplicative, `*`-preserving map `cfcCont : C(σℝ R, ℂ) → (H →L[ℂ] H)`, on
which the (complex) Stone–Weierstrass theorem applies. -/

/-- `borelFC` is additive in `f` (lift of `boundedFC_add`). -/
theorem borelFC_add (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) {f g : spectrum ℝ T → ℂ}
    {Cf Cg : ℝ} (hf : Measurable f) (hg : Measurable g) (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ ω, ‖f ω‖ ≤ Cf) (hCg : ∀ ω, ‖g ω‖ ≤ Cg) :
    borelFC T ha (hf.add hg) (add_nonneg hCf0 hCg0)
        (fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω)))
      = borelFC T ha hf hCf0 hCf + borelFC T ha hg hCg0 hCg :=
  (PVM_of_selfAdjoint T ha).boundedFC_add hf hg hCf0 hCg0 hCf hCg

/-- `borelFC` is ℂ-homogeneous in `f` (lift of `boundedFC_smul`). -/
theorem borelFC_smul (T : H →L[ℂ] H) (ha : IsSelfAdjoint T) (c : ℂ) {f : spectrum ℝ T → ℂ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C) :
    borelFC T ha (hf.const_mul c) (mul_nonneg (norm_nonneg c) hC0)
        (fun ω => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC ω) (norm_nonneg c))
      = c • borelFC T ha hf hC0 hC :=
  (PVM_of_selfAdjoint T ha).boundedFC_smul c hf hC0 hC

variable (S : StandardSubspace H)

/-- The bounded Borel FC of `R = rvdRC S` on a continuous function, with the automatic compact-sup
    bound `‖f ω‖ ≤ ‖f‖`. -/
noncomputable def cfcCont (f : C(spectrum ℝ (rvdRC S), ℂ)) : H →L[ℂ] H :=
  borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) (map_continuous f).measurable
    (norm_nonneg f) (fun ω => ContinuousMap.norm_coe_le_norm f ω)

/-- `cfcCont` depends only on the underlying function (bound-independence). -/
theorem cfcCont_eq (f : C(spectrum ℝ (rvdRC S), ℂ)) {C : ℝ}
    (hf : Measurable (f : spectrum ℝ (rvdRC S) → ℂ)) (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C) :
    cfcCont S f = borelFC (rvdRC S) (rvdRC_isSelfAdjoint S) hf hC0 hC := by
  rw [cfcCont]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ hf hC0 hC rfl

theorem cfcCont_norm_le (f : C(spectrum ℝ (rvdRC S), ℂ)) : ‖cfcCont S f‖ ≤ 2 * ‖f‖ := by
  rw [cfcCont, borelFC]
  exact (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)).boundedFC_norm_le _ _ _

theorem cfcCont_one : cfcCont S 1 = 1 := by
  rw [cfcCont, borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S)
      (map_continuous (1 : C(spectrum ℝ (rvdRC S), ℂ))).measurable (norm_nonneg _) _
      measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl) (by ext ω; simp)]
  exact borelFC_one (rvdRC S) (rvdRC_isSelfAdjoint S)

theorem cfcCont_mul (f g : C(spectrum ℝ (rvdRC S), ℂ)) :
    cfcCont S (f * g) = cfcCont S f * cfcCont S g := by
  have hb : ∀ ω, ‖f ω * g ω‖ ≤ ‖f‖ * ‖g‖ := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (ContinuousMap.norm_coe_le_norm f ω) (ContinuousMap.norm_coe_le_norm g ω)
      (norm_nonneg _) (norm_nonneg _)
  rw [cfcCont, cfcCont, cfcCont,
      borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous (f * g)).measurable (norm_nonneg _) _
        ((map_continuous f).measurable.mul (map_continuous g).measurable)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb (by ext ω; simp),
      borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous f).measurable (norm_nonneg f) (fun ω => ContinuousMap.norm_coe_le_norm f ω)
        (map_continuous g).measurable (norm_nonneg g) (fun ω => ContinuousMap.norm_coe_le_norm g ω)
        ((map_continuous f).measurable.mul (map_continuous g).measurable)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb]

theorem cfcCont_add (f g : C(spectrum ℝ (rvdRC S), ℂ)) :
    cfcCont S (f + g) = cfcCont S f + cfcCont S g := by
  rw [cfcCont, cfcCont, cfcCont,
      borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous (f + g)).measurable (norm_nonneg _) _
        ((map_continuous f).measurable.add (map_continuous g).measurable)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun ω => (norm_add_le _ _).trans
          (add_le_add (ContinuousMap.norm_coe_le_norm f ω) (ContinuousMap.norm_coe_le_norm g ω)))
        (by ext ω; simp),
      borelFC_add (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous f).measurable (map_continuous g).measurable (norm_nonneg f) (norm_nonneg g)
        (fun ω => ContinuousMap.norm_coe_le_norm f ω) (fun ω => ContinuousMap.norm_coe_le_norm g ω)]

theorem cfcCont_smul (c : ℂ) (f : C(spectrum ℝ (rvdRC S), ℂ)) :
    cfcCont S (c • f) = c • cfcCont S f := by
  rw [cfcCont, cfcCont,
      borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous (c • f)).measurable (norm_nonneg _) _
        ((map_continuous f).measurable.const_mul c) (mul_nonneg (norm_nonneg c) (norm_nonneg f))
        (fun ω => by rw [norm_mul]
                     exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f ω)
                       (norm_nonneg c)) (by ext ω; simp),
      borelFC_smul (rvdRC S) (rvdRC_isSelfAdjoint S) c
        (map_continuous f).measurable (norm_nonneg f) (fun ω => ContinuousMap.norm_coe_le_norm f ω)]

theorem cfcCont_star (f : C(spectrum ℝ (rvdRC S), ℂ)) :
    cfcCont S (star f) = star (cfcCont S f) := by
  rw [ContinuousLinearMap.star_eq_adjoint, cfcCont, cfcCont,
      borelFC_adjoint (rvdRC S) (rvdRC_isSelfAdjoint S)
        (map_continuous f).measurable (norm_nonneg f) (fun ω => ContinuousMap.norm_coe_le_norm f ω)
        (Complex.continuous_conj.measurable.comp (map_continuous f).measurable) (norm_nonneg f)
        (fun ω => by rw [RCLike.norm_conj]; exact ContinuousMap.norm_coe_le_norm f ω)]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ _ _ _ (by ext ω; simp)

/-- `cfcCont` sends the coordinate function to `R`. -/
theorem cfcCont_coord :
    cfcCont S ⟨specCoord S, Complex.continuous_ofReal.comp continuous_subtype_val⟩ = rvdRC S := by
  conv_rhs => rw [rvdRC_eq_borelFC S]
  rw [cfcCont]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ _ _ _ rfl

/-- `cfcCont` as a ℂ-linear map (for the continuity bound). -/
noncomputable def cfcContₗ : C(spectrum ℝ (rvdRC S), ℂ) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := cfcCont S
  map_add' := cfcCont_add S
  map_smul' c f := by simp [cfcCont_smul]

theorem cfcCont_continuous : Continuous (cfcCont S) :=
  (LinearMap.mkContinuous (cfcContₗ S) 2 (fun f => cfcCont_norm_le S f)).continuous

/-! ### The symmetric domain `Ω = [−M, 2+M]` and `cfcΩ`

The Stone–Weierstrass twist `f ↦ conj(f(2−·))` needs a domain SYMMETRIC under `r ↦ 2−r`.  The
spectrum `σℝ R` need not be symmetric, so we work on `Ω = [−M, 2+M]` (`M = ‖R‖·‖1‖`), which IS
symmetric (`r ↦ 2−r` swaps the endpoints) and contains `σℝ R` (norm bound).  `cfcΩ f := cfcCont S
(f ∘ incl)` restricts a continuous function on `Ω` to `σℝ R` and applies the FC. -/

/-- The radius `M = ‖R‖·‖1‖` bounding the spectrum. -/
noncomputable def covM : ℝ := ‖rvdRC S‖ * ‖(1 : H →L[ℂ] H)‖

theorem covM_nonneg : 0 ≤ covM S := mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem spectrum_subset_covΩ :
    spectrum ℝ (rvdRC S) ⊆ Set.Icc (-covM S) (2 + covM S) := by
  intro ω hω
  have h : |ω| ≤ covM S := by
    simpa [covM, Real.norm_eq_abs] using spectrum.norm_le_norm_mul_of_mem (𝕜 := ℝ) hω
  rw [abs_le] at h
  exact ⟨h.1, by linarith [h.2, covM_nonneg S]⟩

/-- The inclusion `σℝ R ↪ Ω` as a continuous map. -/
def inclΩ : C(spectrum ℝ (rvdRC S), Set.Icc (-covM S) (2 + covM S)) where
  toFun := Set.inclusion (spectrum_subset_covΩ S)
  continuous_toFun := continuous_inclusion (spectrum_subset_covΩ S)

/-- The involution `τ(r) = 2 − r` on the symmetric `Ω`. -/
def tauΩ : C(Set.Icc (-covM S) (2 + covM S), Set.Icc (-covM S) (2 + covM S)) where
  toFun x := ⟨2 - x.1, by obtain ⟨h1, h2⟩ := x.2; constructor <;> linarith⟩
  continuous_toFun := Continuous.subtype_mk (continuous_const.sub continuous_subtype_val)
    (fun x => by obtain ⟨h1, h2⟩ := x.2; constructor <;> linarith)

/-- `cfcΩ f = f(R)` for `f` continuous on the symmetric domain `Ω`. -/
noncomputable def cfcΩ (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) : H →L[ℂ] H :=
  cfcCont S (f.comp (inclΩ S))

theorem cfcΩ_one : cfcΩ S 1 = 1 := by
  rw [cfcΩ, ContinuousMap.one_comp, cfcCont_one]

theorem cfcΩ_mul (f g : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    cfcΩ S (f * g) = cfcΩ S f * cfcΩ S g := by
  rw [cfcΩ, cfcΩ, cfcΩ, ContinuousMap.mul_comp, cfcCont_mul]

theorem cfcΩ_add (f g : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    cfcΩ S (f + g) = cfcΩ S f + cfcΩ S g := by
  rw [cfcΩ, cfcΩ, cfcΩ, ContinuousMap.add_comp, cfcCont_add]

theorem cfcΩ_smul (c : ℂ) (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    cfcΩ S (c • f) = c • cfcΩ S f := by
  rw [cfcΩ, cfcΩ, ContinuousMap.smul_comp, cfcCont_smul]

theorem cfcΩ_star (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    cfcΩ S (star f) = star (cfcΩ S f) := by
  have h : (star f).comp (inclΩ S) = star (f.comp (inclΩ S)) := rfl
  rw [cfcΩ, cfcΩ, h, cfcCont_star]

theorem cfcΩ_continuous : Continuous (cfcΩ S) :=
  (cfcCont_continuous S).comp (ContinuousMap.continuous_precomp (inclΩ S))

/-! ### The Stone–Weierstrass intertwiner `D·f(R) = conj(f(2−·))(R)·D` -/

/-- The coordinate function `x ↦ x.1` on `Ω` (real-valued ⟹ self-adjoint, the SW generator). -/
def coordΩ : C(Set.Icc (-covM S) (2 + covM S), ℂ) where
  toFun x := (x.1 : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp continuous_subtype_val

theorem coordΩ_star : star (coordΩ S) = coordΩ S := by
  ext x; simp [coordΩ, ContinuousMap.star_apply, Complex.conj_ofReal]

/-- The twist `(twΩ f)(r) = conj(f(2−r))`. -/
noncomputable def twΩ (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    C(Set.Icc (-covM S) (2 + covM S), ℂ) := star (f.comp (tauΩ S))

theorem twΩ_add (f g : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    twΩ S (f + g) = twΩ S f + twΩ S g := by
  rw [twΩ, twΩ, twΩ, ContinuousMap.add_comp, star_add]

theorem twΩ_mul (f g : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    twΩ S (f * g) = twΩ S f * twΩ S g := by
  rw [twΩ, twΩ, twΩ, ContinuousMap.mul_comp, star_mul, mul_comm]

theorem cfcΩ_coordΩ : cfcΩ S (coordΩ S) = rvdRC S := by
  conv_rhs => rw [rvdRC_eq_borelFC S]
  rw [cfcΩ, cfcCont]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ _ _ _ rfl

theorem cfcΩ_sub (f g : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    cfcΩ S (f - g) = cfcΩ S f - cfcΩ S g := by
  rw [sub_eq_add_neg, cfcΩ_add, ← neg_one_smul ℂ g, cfcΩ_smul, neg_one_smul, ← sub_eq_add_neg]

theorem cfcΩ_twΩ_coordΩ : cfcΩ S (twΩ S (coordΩ S)) = rvdTwoSubRC S := by
  have h : twΩ S (coordΩ S)
      = (2 : ℂ) • (1 : C(Set.Icc (-covM S) (2 + covM S), ℂ)) - coordΩ S := by
    ext x
    simp [twΩ, coordΩ, tauΩ, ContinuousMap.star_apply, Complex.conj_ofReal, Complex.ofReal_sub]
  rw [h, cfcΩ_sub, cfcΩ_smul, cfcΩ_one, cfcΩ_coordΩ, rvdTwoSubRC]

/-- The base case of the intertwiner: `D·R = (2−R)·D` in `restrictScalars` form. -/
theorem rvdPmQ_mul_rvdRC_rs :
    rvdPmQ S * (rvdRC S).restrictScalars ℝ = (rvdTwoSubRC S).restrictScalars ℝ * rvdPmQ S := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  have h := DFunLike.congr_fun (rvdPmQ_mul_rvdR S) ξ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.coe_restrictScalars',
    rvdRC_apply, rvdTwoSubRC_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply] at h ⊢
  exact h

/-- **★ The continuous intertwiner `D·f(R) = conj(f(2−·))(R)·D`** for every CONTINUOUS `f` on the
    symmetric domain `Ω`.  Proved by complex Stone–Weierstrass: both sides are continuous in `f`, the
    `coordΩ`-generated subalgebra is dense, and they agree there (base case `D·R=(2−R)·D` + the
    algebra structure).  `D` is antilinear, so the relation is conjugate-linear — hence the "good set"
    is a plain `Subalgebra` (not a `*`-subalgebra), but `coordΩ` is self-adjoint so the generated
    subalgebra still has dense closure. -/
theorem cfcΩ_intertwine (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    rvdPmQ S * (cfcΩ S f).restrictScalars ℝ
      = (cfcΩ S (twΩ S f)).restrictScalars ℝ * rvdPmQ S := by
  have hrs : Continuous (fun Y : H →L[ℂ] H => Y.restrictScalars ℝ) := by
    have h := (ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).continuous
    rwa [ContinuousLinearMap.coe_restrict_scalarsL'] at h
  have hL : Continuous fun f : C(Set.Icc (-covM S) (2 + covM S), ℂ) =>
      rvdPmQ S * (cfcΩ S f).restrictScalars ℝ :=
    continuous_const.mul (hrs.comp (cfcΩ_continuous S))
  have htw : Continuous (twΩ S) :=
    continuous_star.comp (ContinuousMap.continuous_precomp (tauΩ S))
  have hR : Continuous fun f : C(Set.Icc (-covM S) (2 + covM S), ℂ) =>
      (cfcΩ S (twΩ S f)).restrictScalars ℝ * rvdPmQ S :=
    (hrs.comp ((cfcΩ_continuous S).comp htw)).mul continuous_const
  have hsep : (StarAlgebra.adjoin ℂ {coordΩ S}).SeparatesPoints := by
    intro x y hxy
    refine ⟨_, ⟨coordΩ S, StarAlgebra.self_mem_adjoin_singleton ℂ (coordΩ S), rfl⟩, ?_⟩
    intro hc
    exact hxy (Subtype.ext (Complex.ofReal_injective hc))
  have hcarr : (StarAlgebra.adjoin ℂ {coordΩ S} : Set C(Set.Icc (-covM S) (2 + covM S), ℂ))
      = (Algebra.adjoin ℂ {coordΩ S} : Set C(Set.Icc (-covM S) (2 + covM S), ℂ)) := by
    rw [← StarSubalgebra.coe_toSubalgebra, StarAlgebra.adjoin_toSubalgebra, Set.star_singleton,
        coordΩ_star, Set.union_self]
  have hdense : Dense (Algebra.adjoin ℂ {coordΩ S} : Set C(Set.Icc (-covM S) (2 + covM S), ℂ)) := by
    rw [dense_iff_closure_eq, ← hcarr, ← StarSubalgebra.topologicalClosure_coe,
        ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep,
        StarSubalgebra.coe_top]
  have hEq : Set.EqOn (fun f => rvdPmQ S * (cfcΩ S f).restrictScalars ℝ)
      (fun f => (cfcΩ S (twΩ S f)).restrictScalars ℝ * rvdPmQ S)
      (Algebra.adjoin ℂ {coordΩ S} : Set _) := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      simp only [cfcΩ_coordΩ, cfcΩ_twΩ_coordΩ]
      exact rvdPmQ_mul_rvdRC_rs S
    | algebraMap r =>
      simp only
      rw [Algebra.algebraMap_eq_smul_one, cfcΩ_smul, cfcΩ_one,
          show twΩ S (r • (1 : C(Set.Icc (-covM S) (2 + covM S), ℂ))) = (starRingEnd ℂ) r • 1 by
            rw [twΩ, ContinuousMap.smul_comp, ContinuousMap.one_comp, star_smul, star_one]; rfl,
          cfcΩ_smul, cfcΩ_one]
      refine ContinuousLinearMap.ext fun ξ => ?_
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, rvdPmQ_smul_conj]
    | add x y hx hy ihx ihy =>
      simp only at ihx ihy ⊢
      rw [cfcΩ_add, twΩ_add, cfcΩ_add,
          show ((cfcΩ S x + cfcΩ S y).restrictScalars ℝ)
            = (cfcΩ S x).restrictScalars ℝ + (cfcΩ S y).restrictScalars ℝ from rfl,
          show ((cfcΩ S (twΩ S x) + cfcΩ S (twΩ S y)).restrictScalars ℝ)
            = (cfcΩ S (twΩ S x)).restrictScalars ℝ + (cfcΩ S (twΩ S y)).restrictScalars ℝ from rfl,
          mul_add, add_mul, ihx, ihy]
    | mul x y hx hy ihx ihy =>
      simp only at ihx ihy ⊢
      rw [cfcΩ_mul, twΩ_mul, cfcΩ_mul,
          show ((cfcΩ S x * cfcΩ S y).restrictScalars ℝ)
            = (cfcΩ S x).restrictScalars ℝ * (cfcΩ S y).restrictScalars ℝ from rfl,
          show ((cfcΩ S (twΩ S x) * cfcΩ S (twΩ S y)).restrictScalars ℝ)
            = (cfcΩ S (twΩ S x)).restrictScalars ℝ * (cfcΩ S (twΩ S y)).restrictScalars ℝ from rfl,
          ← mul_assoc, ihx, mul_assoc, ihy, ← mul_assoc]
  exact congrFun (Continuous.ext_on hdense hL hR hEq) f

/-! ### The J-conjugation of the continuous functional calculus, and the spectral reflection

  Toward the CGP spectral balance: the modular conjugation `J` conjugates a continuous function of `R`
  by the reflection `r ↦ 2−r`, `J·f(R)·J = (twΩ f)(R)`.  This extends `J R J = 2 − R` to the whole
  continuous FC, via the `D`-intertwiner `cfcΩ_intertwine` (`D·f(R) = (twΩ f)(R)·D`) transported through
  `J(Tξ)=Dξ` on the dense range of `T`.  Its inner-product form is the spectral reflection
  `⟪Jη, f(R) Jη⟫_ℝ = ⟪η, (twΩ f)(R) η⟫_ℝ` — the engine of the measure reflection `μ_{Jη} = (2−·)_* μ_η`. -/

/-- A continuous function of `R` commutes with `R` (the `cfcΩ` image is commutative). -/
theorem cfcΩ_commute_rvdRC (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    Commute (cfcΩ S f) (rvdRC S) := by
  rw [← cfcΩ_coordΩ S, Commute, SemiconjBy, ← cfcΩ_mul, ← cfcΩ_mul, mul_comm]

/-- A continuous function of `R` commutes with `T`. -/
theorem cfcΩ_commute_rvdT (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) :
    Commute (cfcΩ S f) (rvdT S) := by
  have hcR : Commute (cfcΩ S f) (rvdRC S) := cfcΩ_commute_rvdRC S f
  have hc2R : Commute (cfcΩ S f) (rvdTwoSubRC S) := by
    rw [rvdTwoSubRC]
    exact ((Commute.one_right (cfcΩ S f)).smul_right (2 : ℂ)).sub_right hcR
  have hSR : Commute (cfcΩ S f) (rvdSqrtR S) := (hcR.symm.cfcₙ_nnreal NNReal.sqrt).symm
  have hST : Commute (cfcΩ S f) (rvdSqrtTwoSubR S) := (hc2R.symm.cfcₙ_nnreal NNReal.sqrt).symm
  rw [rvdT]; exact hSR.mul_right hST

/-- **★ Continuous operator `J`-conjugation:** `J·f(R) = (twΩ f)(R)·J` (`twΩ f = conj(f∘(2−·))`).
    The extension of `J R J = 2 − R` to the whole continuous functional calculus. -/
theorem modConj_cfcΩ (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) (η : H) :
    modConj S (cfcΩ S f η) = cfcΩ S (twΩ S f) (modConj S η) := by
  refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
    ((modConj S).continuous.comp (cfcΩ S f).continuous)
    ((cfcΩ S (twΩ S f)).continuous.comp (modConj S).continuous) ?_) η
  rintro v ⟨x, rfl⟩
  show modConj S (cfcΩ S f (rvdT S x)) = cfcΩ S (twΩ S f) (modConj S (rvdT S x))
  have hcomm : cfcΩ S f (rvdT S x) = rvdT S (cfcΩ S f x) :=
    DFunLike.congr_fun (cfcΩ_commute_rvdT S f).eq x
  rw [hcomm, modConj_rvdT, modConj_rvdT]
  simpa using DFunLike.congr_fun (cfcΩ_intertwine S f) x

/-- **★ Spectral reflection (inner-product form):** `⟪Jη, f(R) Jη⟫_ℝ = ⟪η, (twΩ f)(R) η⟫_ℝ`.  This is
    the measure reflection `∫ f dμ_{Jη} = ∫ (twΩ f) dμ_η` at the level of the real bilinear form, from the
    `J`-conjugation of `f(R)` and the `J`-invariance of the real inner product. -/
theorem reInner_modConj_cfcΩ (f : C(Set.Icc (-covM S) (2 + covM S), ℂ)) (η : H) :
    inner ℝ (modConj S η) (cfcΩ S f (modConj S η)) = inner ℝ η (cfcΩ S (twΩ S f) η) := by
  have key : modConj S (cfcΩ S f (modConj S η)) = cfcΩ S (twΩ S f) η := by
    rw [modConj_cfcΩ, modConj_sq]
  have key2 : cfcΩ S f (modConj S η) = modConj S (cfcΩ S (twΩ S f) η) := by
    rw [← key, modConj_sq]
  rw [key2, modConj_inner_map]

/-! ### The covariance `[U_t, D] = 0` — apply the intertwiner to the damped modular function -/

/-- The **damped modular function** `r ↦ u_t(r)·r·(2−r)` is CONTINUOUS on `ℝ`: `u_t` is bounded and
    discontinuous only at the endpoints `r = 0, 2`, where the factor `r·(2−r)` vanishes — so the
    product is continuous (squeeze at the endpoints; `u_t` continuous on `(0,2)` and `≡ 1` outside). -/
theorem modChar_damp_continuous (t : ℝ) :
    Continuous (fun r : ℝ => modChar t r * ((r : ℂ) * ((2 : ℂ) - (r : ℂ)))) := by
  refine continuous_iff_continuousAt.mpr fun r₀ => ?_
  have hdamp : Continuous (fun r : ℝ => (r : ℂ) * ((2 : ℂ) - (r : ℂ))) := by fun_prop
  have hsqueeze : ∀ a : ℝ, ((a : ℂ) * ((2 : ℂ) - (a : ℂ))) = 0 →
      ContinuousAt (fun r : ℝ => modChar t r * ((r : ℂ) * ((2 : ℂ) - (r : ℂ)))) a := by
    intro a ha
    rw [ContinuousAt, show modChar t a * ((a : ℂ) * ((2 : ℂ) - (a : ℂ))) = 0 by rw [ha, mul_zero]]
    refine squeeze_zero_norm (fun r => le_of_eq (show
        ‖modChar t r * ((r : ℂ) * ((2 : ℂ) - (r : ℂ)))‖ = ‖(r : ℂ) * ((2 : ℂ) - (r : ℂ))‖ by
        rw [norm_mul, modChar_norm, one_mul])) ?_
    have hc : Filter.Tendsto (fun r : ℝ => ‖(r : ℂ) * ((2 : ℂ) - (r : ℂ))‖) (nhds a)
        (nhds ‖(a : ℂ) * ((2 : ℂ) - (a : ℂ))‖) := (hdamp.norm).continuousAt
    rwa [ha, norm_zero] at hc
  rcases eq_or_ne r₀ 0 with h0 | h0
  · exact hsqueeze r₀ (by rw [h0]; simp)
  rcases eq_or_ne r₀ 2 with h2 | h2
  · exact hsqueeze r₀ (by rw [h2]; simp)
  have hmc : ContinuousAt (modChar t) r₀ := by
    by_cases hI : r₀ ∈ Set.Ioo (0 : ℝ) 2
    · refine ContinuousAt.congr (f := fun r : ℝ =>
        Complex.exp (Complex.I * (t : ℂ) * (Real.log ((2 - r) / r) : ℂ))) ?_ ?_
      · refine Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul ?_)
        refine Complex.continuous_ofReal.continuousAt.comp ?_
        exact ((continuousAt_const.sub continuousAt_id).div continuousAt_id (ne_of_gt hI.1)).log
          (div_pos (sub_pos.mpr hI.2) hI.1).ne'
      · filter_upwards [Ioo_mem_nhds hI.1 hI.2] with r hr
        simp only [modChar]
        rw [Set.piecewise_eq_of_mem _ _ _ hr]
    · refine ContinuousAt.congr (f := fun _ : ℝ => (1 : ℂ)) continuousAt_const ?_
      have hr0 : r₀ < 0 ∨ 2 < r₀ := by
        rcases not_and_or.mp hI with h | h
        · exact Or.inl (lt_of_le_of_ne (not_lt.mp h) h0)
        · exact Or.inr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm h2))
      rcases hr0 with hlt | hgt
      · filter_upwards [Iio_mem_nhds hlt] with r hr
        have hni : r ∉ Set.Ioo (0 : ℝ) 2 :=
          fun hm => absurd hm.1 (not_lt.mpr (Set.mem_Iio.mp hr).le)
        simp only [modChar]
        rw [Set.piecewise_eq_of_notMem _ _ _ hni]
      · filter_upwards [Ioi_mem_nhds hgt] with r hr
        have hni : r ∉ Set.Ioo (0 : ℝ) 2 :=
          fun hm => absurd hm.2 (not_lt.mpr (Set.mem_Ioi.mp hr).le)
        simp only [modChar]
        rw [Set.piecewise_eq_of_notMem _ _ _ hni]
  exact hmc.mul hdamp.continuousAt

/-- **`u_t` is θ-fixed:** `conj(u_t(2−r)) = u_t(r)`.  (`u_t(2−r)=exp(it·log(r/(2−r)))=conj(u_t(r))`.) -/
theorem modChar_reflect (t r : ℝ) : (starRingEnd ℂ) (modChar t (2 - r)) = modChar t r := by
  unfold modChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 2
  · have h' : 2 - r ∈ Set.Ioo (0 : ℝ) 2 := ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.piecewise_eq_of_mem _ _ _ h', Set.piecewise_eq_of_mem _ _ _ h, ← Complex.exp_conj]
    congr 1
    have hlog : Real.log ((2 - (2 - r)) / (2 - r)) = -Real.log ((2 - r) / r) := by
      rw [show (2 : ℝ) - (2 - r) = r by ring, ← Real.log_inv, inv_div]
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal, hlog]
    push_cast
    ring
  · have h' : 2 - r ∉ Set.Ioo (0 : ℝ) 2 :=
      fun hm => h ⟨by linarith [hm.2], by linarith [hm.1]⟩
    rw [Set.piecewise_eq_of_notMem _ _ _ h', Set.piecewise_eq_of_notMem _ _ _ h, map_one]

/-- The **damped modular function** as a continuous map on `Ω`. -/
noncomputable def hΩ (t : ℝ) : C(Set.Icc (-covM S) (2 + covM S), ℂ) where
  toFun x := modChar t x.1 * ((x.1 : ℂ) * ((2 : ℂ) - (x.1 : ℂ)))
  continuous_toFun := (modChar_damp_continuous t).comp continuous_subtype_val

/-- `hΩ` is θ-fixed: `twΩ (hΩ) = hΩ` (the damped modular function is invariant under `r↦2−r` + conj). -/
theorem twΩ_hΩ (t : ℝ) : twΩ S (hΩ S t) = hΩ S t := by
  ext x
  show (starRingEnd ℂ) (modChar t (2 - x.1) *
      ((↑(2 - x.1) : ℂ) * ((2 : ℂ) - (↑(2 - x.1) : ℂ))))
    = modChar t x.1 * ((↑x.1 : ℂ) * ((2 : ℂ) - (↑x.1 : ℂ)))
  rw [map_mul, modChar_reflect, map_mul, Complex.conj_ofReal, map_sub, map_ofNat,
      Complex.conj_ofReal]
  push_cast
  ring

/-- `cfcΩ(hΩ) = U_t · A` with `A = R(2−R)` — the damped FC factors as the modular unitary times the
    polynomial damping (`borelFC_mul`). -/
theorem cfcΩ_hΩ (t : ℝ) :
    cfcΩ S (hΩ S t) = modUnitary S t * (rvdRC S * rvdTwoSubRC S) := by
  have hgA : rvdRC S * rvdTwoSubRC S = cfcΩ S (coordΩ S * twΩ S (coordΩ S)) := by
    rw [cfcΩ_mul, cfcΩ_coordΩ, cfcΩ_twΩ_coordΩ]
  have hfeq : (fun ω => modSpecFun S t ω *
        (((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)) ω))
      = (((hΩ S t).comp (inclΩ S)) : spectrum ℝ (rvdRC S) → ℂ) := by
    funext ω
    show modChar t ω.1 * ((coordΩ S) (inclΩ S ω) * (twΩ S (coordΩ S)) (inclΩ S ω))
      = modChar t ω.1 * ((↑ω.1 : ℂ) * ((2 : ℂ) - (↑ω.1 : ℂ)))
    rw [show (coordΩ S) (inclΩ S ω) = (↑ω.1 : ℂ) from rfl,
        show (twΩ S (coordΩ S)) (inclΩ S ω) = (2 : ℂ) - (↑ω.1 : ℂ) by
          show (starRingEnd ℂ) ((coordΩ S) (tauΩ S (inclΩ S ω))) = (2 : ℂ) - (↑ω.1 : ℂ)
          rw [show (coordΩ S) (tauΩ S (inclΩ S ω)) = (↑(2 - ω.1) : ℂ) from rfl,
              Complex.conj_ofReal, Complex.ofReal_sub, Complex.ofReal_ofNat]]
  have hbound : ∀ ω, ‖modSpecFun S t ω *
        (((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)) ω)‖
      ≤ ‖(coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)‖ := fun ω => by
    rw [norm_mul]
    calc ‖modSpecFun S t ω‖ * ‖((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)) ω‖
        ≤ 1 * ‖(coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)‖ :=
          mul_le_mul (modSpecFun_norm_le S t ω) (ContinuousMap.norm_coe_le_norm _ ω)
            (norm_nonneg _) zero_le_one
      _ = ‖(coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)‖ := one_mul _
  have hmul := borelFC_mul (rvdRC S) (rvdRC_isSelfAdjoint S)
    (modSpecFun_measurable S t) zero_le_one (modSpecFun_norm_le S t)
    (map_continuous ((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S))).measurable
    (norm_nonneg ((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)))
    (fun ω => ContinuousMap.norm_coe_le_norm ((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S)) ω)
    ((modSpecFun_measurable S t).mul
      (map_continuous ((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S))).measurable)
    (norm_nonneg ((coordΩ S * twΩ S (coordΩ S)).comp (inclΩ S))) hbound
  rw [hgA, cfcΩ, cfcΩ, cfcCont, cfcCont, modUnitary, ← hmul]
  exact borelFC_congr (rvdRC S) (rvdRC_isSelfAdjoint S) _ _ _ _ _ _ hfeq.symm

/-- `A = R(2−R)` is self-adjoint. -/
theorem rvdRC_mul_rvdTwoSubRC_isSelfAdjoint : IsSelfAdjoint (rvdRC S * rvdTwoSubRC S) := by
  have h2 : IsSelfAdjoint (rvdTwoSubRC S) := by
    have : star (rvdTwoSubRC S) = rvdTwoSubRC S := by
      simp [rvdTwoSubRC, star_sub, star_smul, (rvdRC_isSelfAdjoint S).star_eq]
    exact this
  show star (rvdRC S * rvdTwoSubRC S) = rvdRC S * rvdTwoSubRC S
  rw [star_mul, h2.star_eq, (rvdRC_isSelfAdjoint S).star_eq]
  exact (rvdRC_commute_rvdTwoSubRC S).symm

/-- `A = R(2−R) = D²` is injective (`D` injective). -/
theorem rvdRC_mul_rvdTwoSubRC_injective :
    Function.Injective (rvdRC S * rvdTwoSubRC S) := by
  intro a b hab
  rw [rvdRC_mul_rvdTwoSubRC_apply, rvdRC_mul_rvdTwoSubRC_apply] at hab
  exact rvdPmQ_injective S (rvdPmQ_injective S hab)

/-- `A.restrictScalars ℝ` has dense range (self-adjoint + injective). -/
theorem rvdRC_mul_rvdTwoSubRC_denseRange :
    DenseRange ((rvdRC S * rvdTwoSubRC S).restrictScalars ℝ) := by
  have hadj : ContinuousLinearMap.adjoint ((rvdRC S * rvdTwoSubRC S).restrictScalars ℝ)
      = (rvdRC S * rvdTwoSubRC S).restrictScalars ℝ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← restrictScalars_star,
        (rvdRC_mul_rvdTwoSubRC_isSelfAdjoint S).star_eq]
  have hbot : (LinearMap.range ((rvdRC S * rvdTwoSubRC S).restrictScalars ℝ).toLinearMap)ᗮ = ⊥ := by
    rw [ContinuousLinearMap.orthogonal_range, hadj, LinearMap.ker_eq_bot]
    intro a b hab; exact rvdRC_mul_rvdTwoSubRC_injective S hab
  have hdense : Dense (↑(LinearMap.range
      ((rvdRC S * rvdTwoSubRC S).restrictScalars ℝ).toLinearMap) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
        ← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]
  rw [DenseRange, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range]
  exact hdense

/-- **★ The modular covariance `[U_t, D] = 0`** (operator form): the modular flow commutes with the
    antilinear `D = P−Q`.  From the intertwiner applied to the θ-fixed damped function `hΩ`
    (`D·(U_t·A)=(U_t·A)·D`), `D·A=A·D`, and cancelling `A` by its dense range. -/
theorem modUnitary_commute_rvdPmQ_rs (t : ℝ) :
    rvdPmQ S * (modUnitary S t).restrictScalars ℝ
      = (modUnitary S t).restrictScalars ℝ * rvdPmQ S := by
  -- the intertwiner at `hΩ`, with `twΩ hΩ = hΩ` and `cfcΩ hΩ = U_t·A`
  have hint := cfcΩ_intertwine S (hΩ S t)
  rw [twΩ_hΩ, cfcΩ_hΩ] at hint
  -- both operators agree on the (dense) range of `A.restrictScalars ℝ`, so they are equal
  refine ContinuousLinearMap.ext fun η =>
    congrFun (Continuous.ext_on (rvdRC_mul_rvdTwoSubRC_denseRange S)
      (rvdPmQ S * (modUnitary S t).restrictScalars ℝ).continuous
      ((modUnitary S t).restrictScalars ℝ * rvdPmQ S).continuous ?_) η
  rintro v ⟨ξ, rfl⟩
  have h1 := DFunLike.congr_fun hint ξ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.coe_restrictScalars'] at h1 ⊢
  rw [h1]
  congr 1
  simpa [ContinuousLinearMap.mul_apply] using (rvdPmQ_commute_A S ξ).symm

/-- **★ The modular covariance `[U_t, D] = 0`** (pointwise): `U_t(D ξ) = D(U_t ξ)`.  Combined with
    `[U_t, R] = 0` this gives full standard-subspace invariance `U_t 𝒦 = 𝒦`. -/
theorem modUnitary_commute_rvdPmQ (t : ℝ) (ξ : H) :
    modUnitary S t (rvdPmQ S ξ) = rvdPmQ S (modUnitary S t ξ) := by
  have h := DFunLike.congr_fun (modUnitary_commute_rvdPmQ_rs S t) ξ
  simpa [ContinuousLinearMap.mul_apply] using h.symm

/-- **★ Full standard-subspace invariance `U_t 𝒦 ⊆ 𝒦`** — both obligations (`[U_t,R]=0` and the
    covariance `[U_t,D]=0`) now discharged. -/
theorem modUnitary_mapsTo_K (S : StandardSubspace H) (t : ℝ) :
    ∀ ξ ∈ S.toClosedSubmodule, modUnitary S t ξ ∈ S.toClosedSubmodule :=
  modUnitary_mapsTo_K_of_commute_D S t (modUnitary_commute_rvdPmQ S t)

/-! ### `J Δ^{it} = Δ^{it} J` — the modular conjugation commutes with the flow (unblocked by `[U_t,D]=0`) -/

/-- `U_t` commutes with `T = √(R(2−R))` (both functions of `R`; via `[U_t,R]=0` and `Commute.cfc_real`). -/
theorem modUnitary_commute_rvdT (t : ℝ) : Commute (modUnitary S t) (rvdT S) := by
  have hcomm_R : Commute (modUnitary S t) (rvdRC S) := modUnitary_commute_rvdRC S t
  have hcomm_2R : Commute (modUnitary S t) (rvdTwoSubRC S) := by
    rw [rvdTwoSubRC]
    exact ((Commute.one_right (modUnitary S t)).smul_right (2 : ℂ)).sub_right hcomm_R
  have hSR : Commute (modUnitary S t) (rvdSqrtR S) :=
    (hcomm_R.symm.cfcₙ_nnreal NNReal.sqrt).symm
  have hST : Commute (modUnitary S t) (rvdSqrtTwoSubR S) :=
    (hcomm_2R.symm.cfcₙ_nnreal NNReal.sqrt).symm
  rw [rvdT]
  exact hSR.mul_right hST

/-- **★ `J Δ^{it} = Δ^{it} J`** — the modular conjugation `J` commutes with the modular flow.  Now
    UNBLOCKED by the covariance `[U_t,D]=0`: since `D = J·T` and `U_t` commutes with both `D` and `T`,
    `J` commutes with `U_t` on the dense `range T`.  (One of the canonical Tomita–Takesaki relations.) -/
theorem modConj_commute_modUnitary (t : ℝ) (η : H) :
    modConj S (modUnitary S t η) = modUnitary S t (modConj S η) := by
  refine congrFun (Continuous.ext_on (rvdT_restrictScalars_denseRange S)
    ((modConj S).continuous.comp (modUnitary S t).continuous)
    ((modUnitary S t).continuous.comp (modConj S).continuous) ?_) η
  rintro v ⟨ξ, rfl⟩
  show modConj S (modUnitary S t (rvdT S ξ)) = modUnitary S t (modConj S (rvdT S ξ))
  have hUT := DFunLike.congr_fun (modUnitary_commute_rvdT S t) ξ
  simp only [ContinuousLinearMap.mul_apply] at hUT
  rw [hUT, modConj_rvdT, modConj_rvdT, modUnitary_commute_rvdPmQ]

/-- **★★★ `Δ^{it} 𝒦 = 𝒦`** — the modular flow PRESERVES the standard subspace, both ways.  The
    inclusion `U_t 𝒦 ⊆ 𝒦` (`modUnitary_mapsTo_K`) plus the group law (`U_{-t}` is the inverse) upgrades
    to the membership equivalence `U_t ξ ∈ 𝒦 ↔ ξ ∈ 𝒦`. -/
theorem modUnitary_mem_K_iff (t : ℝ) (ξ : H) :
    modUnitary S t ξ ∈ S.toClosedSubmodule ↔ ξ ∈ S.toClosedSubmodule := by
  refine ⟨fun h => ?_, fun h => modUnitary_mapsTo_K S t ξ h⟩
  have h2 := modUnitary_mapsTo_K S (-t) (modUnitary S t ξ) h
  rwa [show modUnitary S (-t) (modUnitary S t ξ) = ξ by
        rw [← ContinuousLinearMap.mul_apply, ← modUnitary_add, neg_add_cancel, modUnitary_zero,
            ContinuousLinearMap.one_apply]] at h2

/-! ### Entire-vector smearing (toward RvD Theorem 3.8 KMS-uniqueness) -/

open MeasureTheory in
/-- The **Gaussian-smeared vector** `(n/π)^{1/2}∫ e^{−n t²} V_t η dt` (without the normalisation constant):
    the construction RvD use to produce a dense set of entire vectors inside the real subspace `K`. -/
noncomputable def gaussSmear (V : ℝ → (H →L[ℂ] H)) (n : ℝ) (η : H) : H :=
  ∫ t : ℝ, Real.exp (-n * t ^ 2) • V t η

open MeasureTheory in
/-- The smeared integrand is Bochner-integrable: dominated by `e^{−n t²}·‖η‖` (a Gaussian), since `V_t` is
    norm-non-increasing and the orbit is continuous. -/
theorem gaussSmear_integrable {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    Integrable (fun t : ℝ => Real.exp (-n * t ^ 2) • V t η) := by
  have hexp : Continuous (fun t : ℝ => Real.exp (-n * t ^ 2)) := by fun_prop
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hn).mul_const ‖η‖)
    (hexp.smul hcont).aestronglyMeasurable ?_
  filter_upwards with t
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hbd t) (Real.exp_pos _).le

open MeasureTheory in
/-- **★ The smeared vector lands in `K`.**  Since `e^{−n t²} ≥ 0` is a real scalar and `V_t η ∈ K`
    (real-subspace invariance), the Bochner integral stays in the closed real subspace `K` — because the
    `ℝ`-linear orthogonal projection `projK` commutes with the integral and fixes the integrand
    (`ContinuousLinearMap.integral_comp_comm`).  First brick of the entire-vector construction. -/
theorem gaussSmear_mem_K (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) {η : H}
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hinv : ∀ t, V t η ∈ S.toClosedSubmodule) :
    gaussSmear V n η ∈ S.toClosedSubmodule := by
  rw [mem_K_iff_projK, gaussSmear,
    ← ContinuousLinearMap.integral_comp_comm (projK S) (gaussSmear_integrable hn η hcont hbd)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show projK S (Real.exp (-n * t ^ 2) • V t η) = Real.exp (-n * t ^ 2) • V t η
  rw [map_smul, (mem_K_iff_projK S (V t η)).mp (hinv t)]

open MeasureTheory in
/-- **The translation property of the smeared vector**: `V_s (gaussSmear V n η) = ∫ e^{−n t²}·V_{s+t} η dt`.
    Applying the unitary `V_s` (a continuous linear map) commutes with the Bochner integral
    (`integral_comp_comm`) and, via the group law, shifts the orbit.  After the change of variables
    `u = s + t` the right side is `∫ e^{−n (u−s)²}·V_u η du`, whose integrand is *entire* in the parameter
    `s` — this is what makes `gaussSmear V n η` an entire vector for `V` (RvD's key property toward
    Theorem 3.8). -/
theorem gaussSmear_smul_left {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (s : ℝ) :
    V s (gaussSmear V n η) = ∫ t : ℝ, Real.exp (-n * t ^ 2) • V (s + t) η := by
  rw [gaussSmear,
    ← ContinuousLinearMap.integral_comp_comm (V s) (gaussSmear_integrable hn η hcont hbd)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show V s (Real.exp (-n * t ^ 2) • V t η) = Real.exp (-n * t ^ 2) • V (s + t) η
  rw [(V s).map_smul_of_tower (Real.exp (-n * t ^ 2)) (V t η), hgrp s t]

/-- **The Gaussian normalisation** `√(n/π)·∫ e^{−n t²} dt = 1` — so `√(n/π)` is the right constant to make
    `gaussSmear` an approximate identity (`integral_gaussian`: `∫ e^{−n t²} = √(π/n)`). -/
theorem gaussian_normalization {n : ℝ} (hn : 0 < n) :
    Real.sqrt (n / Real.pi) * ∫ t : ℝ, Real.exp (-n * t ^ 2) = 1 := by
  rw [integral_gaussian, ← Real.sqrt_mul (by positivity), div_mul_div_comm,
    mul_comm n Real.pi, div_self (by positivity), Real.sqrt_one]

/-- The **normalised entire vector** `η_n = √(n/π)·gaussSmear V n η` — RvD's dense entire vectors in `K`. -/
noncomputable def entireVec (V : ℝ → (H →L[ℂ] H)) (n : ℝ) (η : H) : H :=
  Real.sqrt (n / Real.pi) • gaussSmear V n η

/-- The normalised entire vector lands in the real subspace `K` (scaling `gaussSmear_mem_K` by a real). -/
theorem entireVec_mem_K (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) {η : H}
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hinv : ∀ t, V t η ∈ S.toClosedSubmodule) :
    entireVec V n η ∈ S.toClosedSubmodule :=
  Submodule.smul_mem _ _ (gaussSmear_mem_K S hn hcont hbd hinv)

open MeasureTheory in
/-- **Mollifier form of the error** `η_n − η = √(n/π)·∫ e^{−n t²}·(V_t η − η) dt`.  Subtracting the
    normalised constant `η = √(n/π)·∫ e^{−n t²}·η dt` (Gaussian normalisation) from the smeared vector.  This
    is the setup for the density `η_n → η`: as `n → ∞` the Gaussian concentrates at `t = 0`, where
    `V_t η → η` by strong continuity. -/
theorem entireVec_sub {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    entireVec V n η - η
      = Real.sqrt (n / Real.pi) • ∫ t : ℝ, Real.exp (-n * t ^ 2) • (V t η - η) := by
  have hint1 : Integrable (fun t : ℝ => Real.exp (-n * t ^ 2) • V t η) :=
    gaussSmear_integrable hn η hcont hbd
  have hint2 : Integrable (fun t : ℝ => Real.exp (-n * t ^ 2) • η) :=
    (integrable_exp_neg_mul_sq hn).smul_const η
  have hη : η = Real.sqrt (n / Real.pi) • ∫ t : ℝ, Real.exp (-n * t ^ 2) • η := by
    rw [integral_smul_const, integral_gaussian, smul_smul, ← Real.sqrt_mul (by positivity),
      div_mul_div_comm, mul_comm Real.pi n, div_self (by positivity), Real.sqrt_one, one_smul]
  rw [entireVec, gaussSmear,
    show (fun t : ℝ => Real.exp (-n * t ^ 2) • (V t η - η))
        = fun t => Real.exp (-n * t ^ 2) • V t η - Real.exp (-n * t ^ 2) • η from
      funext (fun t => smul_sub _ _ _),
    integral_sub hint1 hint2, smul_sub, ← hη]

open MeasureTheory in
/-- **The density error bound** `‖η_n − η‖ ≤ √(n/π)·∫ e^{−n t²}·‖V_t η − η‖ dt`.  Reduces the vector density
    to a *scalar* Gaussian-mollifier limit of `t ↦ ‖V_t η − η‖`, a bounded continuous function vanishing at
    `t = 0` (`V_0 η = η` + strong continuity).  From `entireVec_sub` + `norm_integral_le_integral_norm`. -/
theorem entireVec_sub_norm_le {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    ‖entireVec V n η - η‖
      ≤ Real.sqrt (n / Real.pi) * ∫ t : ℝ, Real.exp (-n * t ^ 2) * ‖V t η - η‖ := by
  rw [entireVec_sub hn η hcont hbd, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (Real.sqrt_nonneg _)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show ‖Real.exp (-n * t ^ 2) • (V t η - η)‖ = Real.exp (-n * t ^ 2) * ‖V t η - η‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

open MeasureTheory in
/-- **Change of variables for the Gaussian mollifier** `u = √n·t`: `∫ e^{−u²}·f(u/√n) du = √n·∫ e^{−n t²}·f(t) dt`.
    The substitution that turns the *concentrating* Gaussian kernel into a *fixed* Gaussian `e^{−u²}` against
    the rescaled `f(u/√n)`, so the mollifier limit follows from dominated convergence (`f(u/√n) → f(0)`). -/
theorem gauss_mollifier_change_of_var {n : ℝ} (hn : 0 < n) (f : ℝ → ℝ) :
    ∫ u : ℝ, Real.exp (-u ^ 2) * f (u / Real.sqrt n)
      = Real.sqrt n * ∫ t : ℝ, Real.exp (-n * t ^ 2) * f t := by
  have hkey := Measure.integral_comp_div (fun v : ℝ => Real.exp (-n * v ^ 2) * f v) (Real.sqrt n)
  rw [abs_of_nonneg (Real.sqrt_nonneg _), smul_eq_mul] at hkey
  rw [← hkey]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  have harg : -n * (u / Real.sqrt n) ^ 2 = -u ^ 2 := by
    have hne : n ≠ 0 := ne_of_gt hn
    rw [div_pow, Real.sq_sqrt hn.le]; field_simp
  show Real.exp (-u ^ 2) * f (u / Real.sqrt n)
      = Real.exp (-n * (u / Real.sqrt n) ^ 2) * f (u / Real.sqrt n)
  rw [harg]

open MeasureTheory Filter Topology in
/-- **The fixed-Gaussian mollifier limit** (dominated convergence): for bounded continuous `f`,
    `∫ e^{−u²}·f(u/√n) du → ∫ e^{−u²}·f(0) du` as `n → ∞`.  Since `u/√n → 0` and `f` is continuous,
    `f(u/√n) → f(0)` pointwise, dominated by `e^{−u²}·M`. -/
theorem gauss_mollifier_integral_tendsto {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f) (hM : ∀ t, |f t| ≤ M) :
    Tendsto (fun n : ℝ => ∫ u, Real.exp (-u ^ 2) * f (u / Real.sqrt n)) atTop
      (𝓝 (∫ u, Real.exp (-u ^ 2) * f 0)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u => Real.exp (-u ^ 2) * M)
    (Filter.Eventually.of_forall (fun n => (by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-u ^ 2) * f (u / Real.sqrt n)).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (fun u => ?_)))
    (by simpa only [neg_one_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)).mul_const M)
    (Filter.Eventually.of_forall (fun u => ?_))
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
  · have h0 : Tendsto (fun n : ℝ => u / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    exact (hf.continuousAt.tendsto.comp h0).const_mul (Real.exp (-u ^ 2))

open MeasureTheory Filter Topology in
/-- **The scalar Gaussian density** `√(n/π)·∫ e^{−n t²}·f(t) dt → f(0)` as `n → ∞`, for bounded
    continuous `f`.  Combines the change of variables `u = √n·t` (`gauss_mollifier_change_of_var`)
    with the fixed-Gaussian limit (`gauss_mollifier_integral_tendsto`):
    `√(n/π)·∫ e^{−n t²}f = √(1/π)·∫ e^{−u²}f(u/√n) → √(1/π)·∫ e^{−u²}f(0) = f(0)`.
    Applied to `f(t) = ‖V_t η − η‖` (bounded by `2‖η‖`, vanishing at `0`) this lands the RvD
    entire-vector density `η_n → η`. -/
theorem gauss_density_tendsto {f : ℝ → ℝ} {M : ℝ} (hf : Continuous f) (hM : ∀ t, |f t| ≤ M) :
    Tendsto (fun n : ℝ => Real.sqrt (n / Real.pi) * ∫ t : ℝ, Real.exp (-n * t ^ 2) * f t) atTop
      (𝓝 (f 0)) := by
  have hg : (∫ u : ℝ, Real.exp (-u ^ 2)) = Real.sqrt Real.pi := by
    have := integral_gaussian 1
    simpa only [neg_one_mul, div_one] using this
  have hsqrt : Real.sqrt (1 / Real.pi) * Real.sqrt Real.pi = 1 := by
    rw [← Real.sqrt_mul (by positivity), one_div_mul_cancel Real.pi_ne_zero, Real.sqrt_one]
  have hlim : Real.sqrt (1 / Real.pi) * ∫ u : ℝ, Real.exp (-u ^ 2) * f 0 = f 0 := by
    rw [integral_mul_const, hg, ← mul_assoc, hsqrt, one_mul]
  have base : Tendsto (fun n : ℝ => Real.sqrt (1 / Real.pi)
      * ∫ u : ℝ, Real.exp (-u ^ 2) * f (u / Real.sqrt n)) atTop
      (𝓝 (Real.sqrt (1 / Real.pi) * ∫ u : ℝ, Real.exp (-u ^ 2) * f 0)) :=
    (gauss_mollifier_integral_tendsto hf hM).const_mul _
  rw [hlim] at base
  refine Tendsto.congr' ?_ base
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  show Real.sqrt (1 / Real.pi) * ∫ u : ℝ, Real.exp (-u ^ 2) * f (u / Real.sqrt n)
      = Real.sqrt (n / Real.pi) * ∫ t : ℝ, Real.exp (-n * t ^ 2) * f t
  rw [gauss_mollifier_change_of_var hn f, ← mul_assoc]
  congr 1
  rw [← Real.sqrt_mul (by positivity), one_div_mul_eq_div]

open MeasureTheory Filter Topology in
/-- **RvD entire-vector density** `η_n → η`: the normalised entire vectors `η_n = √(n/π)·∫ e^{−n t²}·V_t η dt`
    converge to `η` as `n → ∞`, for any strongly-continuous one-parameter contraction `V` with `V_0 η = η`.
    Squeeze: `0 ≤ ‖η_n − η‖ ≤ √(n/π)·∫ e^{−n t²}·‖V_t η − η‖ → ‖V_0 η − η‖ = 0`
    (`entireVec_sub_norm_le` + `gauss_density_tendsto` on the bounded continuous `t ↦ ‖V_t η − η‖`).
    With `entireVec_mem_K` this makes the entire vectors a *dense* subset of the real subspace `K` —
    the totality input for the RvD Theorem 3.8 KMS-uniqueness argument (`hUniq`). -/
theorem entireVec_tendsto {V : ℝ → (H →L[ℂ] H)} (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) (hV0 : V 0 η = η) :
    Tendsto (fun n : ℝ => entireVec V n η) atTop (𝓝 η) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hf : Continuous (fun t => ‖V t η - η‖) := (hcont.sub continuous_const).norm
  have hM : ∀ t, |‖V t η - η‖| ≤ 2 * ‖η‖ := by
    intro t
    rw [abs_of_nonneg (norm_nonneg _)]
    calc ‖V t η - η‖ ≤ ‖V t η‖ + ‖η‖ := norm_sub_le _ _
      _ ≤ ‖η‖ + ‖η‖ := by linarith [hbd t]
      _ = 2 * ‖η‖ := by ring
  have hdens := gauss_density_tendsto hf hM
  rw [hV0, sub_self, norm_zero] at hdens
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hdens
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
  exact entireVec_sub_norm_le hn η hcont hbd

/-! ### The complex orbit of an entire vector (toward RvD Theorem 3.8 operator assembly)

The smeared vector `gaussSmear V n η` is *entire* for `V`: the orbit `s ↦ V_s(gaussSmear V n η)`,
which on the real axis equals `∫ e^{−n(u−s)²}·V_u η du` (change of variables in `gaussSmear_smul_left`),
extends to a holomorphic `H`-valued function of a **complex** time `z` because the Gaussian kernel
`e^{−n(u−z)²}` is entire in `z` and damps the orbit.  This `gaussSmearC` is the analytic continuation;
on the KMS strip it makes the correlation `z ↦ ⟨gaussSmearC … z, η'⟩` holomorphic, which (with
`StripUniqueness`) is what forces `U_t = Δ^{it}` in `hUniq`. -/

open MeasureTheory in
/-- The **complex orbit** of the smeared vector: `G(z) = ∫ e^{−n(u−z)²}·V_u η du`, an `H`-valued function
    of complex time `z`.  On the real axis it is `V_s(gaussSmear V n η)`; it is entire in `z`. -/
noncomputable def gaussSmearC (V : ℝ → (H →L[ℂ] H)) (n : ℝ) (η : H) (z : ℂ) : H :=
  ∫ u : ℝ, Complex.exp (-(n : ℂ) * ((u : ℂ) - z) ^ 2) • V u η

open MeasureTheory in
/-- The complex-orbit integrand is Bochner-integrable for every fixed `z`: dominated by the shifted Gaussian
    `e^{n·(Im z)²}·e^{−n(u−Re z)²}·‖η‖` (since `Re(−n(u−z)²) = −n(u−Re z)² + n(Im z)²`). -/
theorem gaussSmearC_integrable {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) (z : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (-(n : ℂ) * ((u : ℂ) - z) ^ 2) • V u η) := by
  have hscal : Continuous (fun u : ℝ => Complex.exp (-(n : ℂ) * ((u : ℂ) - z) ^ 2)) := by fun_prop
  refine Integrable.mono'
    (((integrable_exp_neg_mul_sq hn).comp_sub_right z.re).mul_const
      (Real.exp (n * z.im ^ 2) * ‖η‖))
    (hscal.smul hcont).aestronglyMeasurable ?_
  filter_upwards with u
  have hre : (-(n : ℂ) * ((u : ℂ) - z) ^ 2).re = -n * (u - z.re) ^ 2 + n * z.im ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [norm_smul, Complex.norm_exp, hre, Real.exp_add]
  calc Real.exp (-n * (u - z.re) ^ 2) * Real.exp (n * z.im ^ 2) * ‖V u η‖
      ≤ Real.exp (-n * (u - z.re) ^ 2) * Real.exp (n * z.im ^ 2) * ‖η‖ :=
        mul_le_mul_of_nonneg_left (hbd u) (by positivity)
    _ = Real.exp (-n * (u - z.re) ^ 2) * (Real.exp (n * z.im ^ 2) * ‖η‖) := by ring

open MeasureTheory in
/-- **Real-axis agreement** `gaussSmearC V n η ↑s = V_s(gaussSmear V n η)`.  On the real axis the complex
    orbit reduces to the genuine unitary-group orbit of the smeared vector: the complex Gaussian kernel
    `e^{−n(u−s)²}` collapses to its real value and, after the translation `u = s + t`, equals
    `∫ e^{−n t²}·V_{s+t} η dt = V_s(gaussSmear V n η)` (`gaussSmear_smul_left`).  This anchors the entire
    extension `gaussSmearC` to the actual flow `V`. -/
theorem gaussSmearC_ofReal {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (s : ℝ) :
    gaussSmearC V n η (s : ℂ) = V s (gaussSmear V n η) := by
  rw [gaussSmear_smul_left hn η hcont hbd hgrp s, gaussSmearC]
  have hcoe : ∀ u : ℝ, Complex.exp (-(n : ℂ) * ((u : ℂ) - (s : ℂ)) ^ 2) • V u η
      = Real.exp (-n * (u - s) ^ 2) • V u η := by
    intro u
    rw [show (-(n : ℂ) * ((u : ℂ) - (s : ℂ)) ^ 2) = ((-n * (u - s) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← algebraMap_smul ℂ (Real.exp (-n * (u - s) ^ 2)) (V u η),
      Complex.coe_algebraMap]
  simp_rw [hcoe]
  rw [← integral_add_left_eq_self (fun u : ℝ => Real.exp (-n * (u - s) ^ 2) • V u η) s]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show Real.exp (-n * (s + t - s) ^ 2) • V (s + t) η = Real.exp (-n * t ^ 2) • V (s + t) η
  rw [add_sub_cancel_left]

open MeasureTheory in
/-- **Linear×Gaussian integrability** `Integrable (u ↦ (|u| + c)·e^{−b u²})` for `b > 0` — a degree-one
    polynomial against a Gaussian.  `|u|·e^{−b u²}` is integrable (norm of `u·e^{−b u²}`,
    `integrable_mul_exp_neg_mul_sq`) and `c·e^{−b u²}` is integrable; their sum dominates the derivative
    of the complex orbit (the `‖2n(u−z)·e^{−n(u−z)²}‖` bound), so this is the integrable dominating
    function for the holomorphy of `gaussSmearC`. -/
theorem integrable_abs_add_mul_exp_neg_mul_sq {b c : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℝ => (|u| + c) * Real.exp (-b * u ^ 2)) := by
  have h1 : Integrable (fun u : ℝ => |u| * Real.exp (-b * u ^ 2)) := by
    have hnorm := (integrable_mul_exp_neg_mul_sq hb).norm
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at hnorm
    exact hnorm
  have h2 : Integrable (fun u : ℝ => c * Real.exp (-b * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul c
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun u => ?_))
  show |u| * Real.exp (-b * u ^ 2) + c * Real.exp (-b * u ^ 2) = (|u| + c) * Real.exp (-b * u ^ 2)
  ring

open MeasureTheory Filter Topology in
/-- **The complex orbit is entire**: `gaussSmearC V n η` is complex-differentiable at every `z₀`, with
    `HasDerivAt` given by differentiation under the integral sign,
    `(gaussSmearC V n η)'(z₀) = ∫ (2n(u−z₀)·e^{−n(u−z₀)²})·V_u η du`.  The derivative integrand is
    dominated, uniformly for `z` in a unit ball around `z₀`, by the integrable linear×Gaussian
    `2n·C₁·‖η‖·(|u−Re z₀|+|Im z₀|+2)·e^{−(n/2)(u−Re z₀)²}` — using `Re(−n(u−z)²) = −n(u−Re z)²+n(Im z)²`,
    the AM-GM bound `(u−Re z)² ≥ (u−Re z₀)²/2 − 2`, and `|Im z| ≤ |Im z₀|+1`.  This entirety is what makes
    the KMS correlation `z ↦ ⟨gaussSmearC … z, ·⟩` holomorphic on the strip (RvD Theorem 3.8). -/
theorem hasDerivAt_gaussSmearC {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) (z₀ : ℂ) :
    HasDerivAt (gaussSmearC V n η)
      (∫ u : ℝ, (2 * (n : ℂ) * ((u : ℂ) - z₀) * Complex.exp (-(n : ℂ) * ((u : ℂ) - z₀) ^ 2)) • V u η)
      z₀ := by
  have hFmeas : ∀ x : ℂ, AEStronglyMeasurable
      (fun u : ℝ => Complex.exp (-(n : ℂ) * ((u : ℂ) - x) ^ 2) • V u η) volume := fun x =>
    ((by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-(n : ℂ) * ((u : ℂ) - x) ^ 2)).smul hcont).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun u : ℝ => (2 * (n : ℂ) * ((u : ℂ) - z₀) *
        Complex.exp (-(n : ℂ) * ((u : ℂ) - z₀) ^ 2)) • V u η) volume :=
    ((by fun_prop : Continuous fun u : ℝ =>
      2 * (n : ℂ) * ((u : ℂ) - z₀) *
        Complex.exp (-(n : ℂ) * ((u : ℂ) - z₀) ^ 2)).smul hcont).aestronglyMeasurable
  -- the derivative under the integral
  have hdiff : ∀ u : ℝ, ∀ x : ℂ, HasDerivAt
      (fun y : ℂ => Complex.exp (-(n : ℂ) * ((u : ℂ) - y) ^ 2) • V u η)
      ((2 * (n : ℂ) * ((u : ℂ) - x) *
        Complex.exp (-(n : ℂ) * ((u : ℂ) - x) ^ 2)) • V u η) x := by
    intro u x
    have h1 : HasDerivAt (fun y : ℂ => (u : ℂ) - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (u : ℂ)
    have h2 := ((h1.pow 2).const_mul (-(n : ℂ))).cexp.smul_const (V u η)
    simp only [Pi.pow_apply] at h2
    convert h2 using 2
    push_cast
    ring
  -- the uniform integrable bound
  set C₁ : ℝ := Real.exp (2 * n + n * (|z₀.im| + 1) ^ 2) with hC₁
  have hbound_int : Integrable
      (fun u : ℝ => (2 * n * C₁ * ‖η‖) *
        ((|u - z₀.re| + (|z₀.im| + 2)) * Real.exp (-(n / 2) * (u - z₀.re) ^ 2))) volume :=
    ((integrable_abs_add_mul_exp_neg_mul_sq (b := n / 2) (c := |z₀.im| + 2)
      (by positivity)).comp_sub_right z₀.re).const_mul _
  have hbd_ineq : ∀ᵐ u : ℝ, ∀ x ∈ Metric.ball z₀ 1,
      ‖(2 * (n : ℂ) * ((u : ℂ) - x) *
        Complex.exp (-(n : ℂ) * ((u : ℂ) - x) ^ 2)) • V u η‖
        ≤ (2 * n * C₁ * ‖η‖) *
          ((|u - z₀.re| + (|z₀.im| + 2)) * Real.exp (-(n / 2) * (u - z₀.re) ^ 2)) := by
    refine Filter.Eventually.of_forall (fun u x hx => ?_)
    rw [Metric.mem_ball, Complex.dist_eq] at hx
    have hre : |x.re - z₀.re| ≤ 1 := le_of_lt (lt_of_le_of_lt (by
      simpa using Complex.abs_re_le_norm (x - z₀)) hx)
    have him : |x.im - z₀.im| ≤ 1 := le_of_lt (lt_of_le_of_lt (by
      simpa using Complex.abs_im_le_norm (x - z₀)) hx)
    -- norm of the scalar coefficient
    have hw : (-(n : ℂ) * ((u : ℂ) - x) ^ 2).re = -n * (u - x.re) ^ 2 + n * x.im ^ 2 := by
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [norm_smul, norm_mul, norm_mul, norm_mul, Complex.norm_exp, hw]
    have h2n : ‖(2 : ℂ)‖ * ‖(n : ℂ)‖ = 2 * n := by
      simp [abs_of_pos hn]
    -- bound the pieces
    have hnorm_ux : ‖(u : ℂ) - x‖ ≤ |u - z₀.re| + (|z₀.im| + 2) := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e1 : ((u : ℂ) - x).re = u - x.re := by simp
      have e2 : ((u : ℂ) - x).im = -x.im := by simp
      rw [e1, e2, abs_neg]
      have hb1 : |u - x.re| ≤ |u - z₀.re| + 1 := by
        calc |u - x.re| = |(u - z₀.re) + (z₀.re - x.re)| := by ring_nf
          _ ≤ |u - z₀.re| + |z₀.re - x.re| := abs_add_le _ _
          _ ≤ |u - z₀.re| + 1 := by rw [abs_sub_comm z₀.re x.re]; linarith [hre]
      have hb2 : |x.im| ≤ |z₀.im| + 1 := by
        calc |x.im| = |z₀.im + (x.im - z₀.im)| := by ring_nf
          _ ≤ |z₀.im| + |x.im - z₀.im| := abs_add_le _ _
          _ ≤ |z₀.im| + 1 := by linarith [him]
      linarith [hb1, hb2]
    have hC1pos : 0 < C₁ := by rw [hC₁]; positivity
    have hdle := abs_le.mp hre
    have hexp_bound : Real.exp (-n * (u - x.re) ^ 2 + n * x.im ^ 2)
        ≤ C₁ * Real.exp (-(n / 2) * (u - z₀.re) ^ 2) := by
      rw [hC₁, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hamgm : (u - x.re) ^ 2 ≥ (u - z₀.re) ^ 2 / 2 - 2 := by
        nlinarith [sq_nonneg (u - 2 * x.re + z₀.re),
          mul_nonneg (by linarith [hdle.1] : (0:ℝ) ≤ 1 + (x.re - z₀.re))
            (by linarith [hdle.2] : (0:ℝ) ≤ 1 - (x.re - z₀.re)), hdle.1, hdle.2]
      have himsq : x.im ^ 2 ≤ (|z₀.im| + 1) ^ 2 := by
        have habs : |x.im| ≤ |z₀.im| + 1 := by
          calc |x.im| = |z₀.im + (x.im - z₀.im)| := by ring_nf
            _ ≤ |z₀.im| + |x.im - z₀.im| := abs_add_le _ _
            _ ≤ |z₀.im| + 1 := by linarith [him]
        nlinarith [sq_abs x.im, habs, abs_nonneg x.im, abs_nonneg z₀.im]
      have e1 : -n * (u - x.re) ^ 2 ≤ -(n / 2) * (u - z₀.re) ^ 2 + 2 * n := by
        nlinarith [mul_nonneg hn.le
          (by linarith [hamgm] : (0:ℝ) ≤ (u - x.re) ^ 2 - ((u - z₀.re) ^ 2 / 2 - 2))]
      have e2 : n * x.im ^ 2 ≤ n * (|z₀.im| + 1) ^ 2 := by
        nlinarith [mul_nonneg hn.le (by linarith [himsq] : (0:ℝ) ≤ (|z₀.im| + 1) ^ 2 - x.im ^ 2)]
      linarith [e1, e2]
    -- assemble
    rw [h2n]
    have hVu : ‖V u η‖ ≤ ‖η‖ := hbd u
    have h2n0 : (0 : ℝ) ≤ 2 * n := by linarith
    have hd_nn : (0:ℝ) ≤ C₁ * Real.exp (-(n / 2) * (u - z₀.re) ^ 2) :=
      mul_nonneg hC1pos.le (Real.exp_pos _).le
    have hinner : ‖(u : ℂ) - x‖ * Real.exp (-n * (u - x.re) ^ 2 + n * x.im ^ 2) * ‖V u η‖
        ≤ (|u - z₀.re| + (|z₀.im| + 2)) *
            (C₁ * Real.exp (-(n / 2) * (u - z₀.re) ^ 2)) * ‖η‖ := by
      refine mul_le_mul ?_ hVu (norm_nonneg _) (mul_nonneg (by positivity) hd_nn)
      exact mul_le_mul hnorm_ux hexp_bound (Real.exp_pos _).le (by positivity)
    calc 2 * n * ‖(u : ℂ) - x‖ * Real.exp (-n * (u - x.re) ^ 2 + n * x.im ^ 2) * ‖V u η‖
        = 2 * n * (‖(u : ℂ) - x‖ * Real.exp (-n * (u - x.re) ^ 2 + n * x.im ^ 2) * ‖V u η‖) := by
          ring
      _ ≤ 2 * n * ((|u - z₀.re| + (|z₀.im| + 2)) *
            (C₁ * Real.exp (-(n / 2) * (u - z₀.re) ^ 2)) * ‖η‖) :=
          mul_le_mul_of_nonneg_left hinner h2n0
      _ = (2 * n * C₁ * ‖η‖) *
            ((|u - z₀.re| + (|z₀.im| + 2)) * Real.exp (-(n / 2) * (u - z₀.re) ^ 2)) := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x u => Complex.exp (-(n : ℂ) * ((u : ℂ) - x) ^ 2) • V u η)
    (bound := fun u : ℝ => (2 * n * C₁ * ‖η‖) *
      ((|u - z₀.re| + (|z₀.im| + 2)) * Real.exp (-(n / 2) * (u - z₀.re) ^ 2)))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall hFmeas)
    (gaussSmearC_integrable hn η hcont hbd z₀)
    hF'meas hbd_ineq hbound_int
    (Filter.Eventually.of_forall (fun u x _ => hdiff u x))
  exact key.2

open MeasureTheory in
/-- **The complex orbit is entire.**  `gaussSmearC V n η` is complex-differentiable on all of `ℂ`
    (`HasDerivAt` at every point, `hasDerivAt_gaussSmearC`).  Composed with a continuous-linear functional
    this gives the entire KMS correlation needed for the strip-uniqueness step of RvD Theorem 3.8. -/
theorem differentiable_gaussSmearC {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    Differentiable ℂ (gaussSmearC V n η) :=
  fun z₀ => (hasDerivAt_gaussSmearC hn η hcont hbd z₀).differentiableAt

/-- The **KMS two-point correlation** of two entire vectors, `corrC ξ V n η z = ⟨ξ, gaussSmearC V n η z⟩`
    — the analytic object the strip-uniqueness step compares between two candidate modular flows. -/
noncomputable def corrC (ξ : H) (V : ℝ → (H →L[ℂ] H)) (n : ℝ) (η : H) (z : ℂ) : ℂ :=
  innerSL ℂ ξ (gaussSmearC V n η z)

/-- **The KMS correlation is entire**: `z ↦ ⟨ξ, gaussSmearC V n η z⟩` is complex-differentiable on all of
    `ℂ`, being the continuous-linear functional `innerSL ℂ ξ` composed with the entire orbit
    (`differentiable_gaussSmearC`). -/
theorem differentiable_corrC {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    Differentiable ℂ (corrC ξ V n η) :=
  (innerSL ℂ ξ).differentiable.comp (differentiable_gaussSmearC hn η hcont hbd)

/-- **Real-axis value of the correlation**: on the real axis the KMS correlation is the genuine
    matrix element of the flow, `corrC ξ V n η ↑s = ⟨ξ, V_s(gaussSmear V n η)⟩` (`gaussSmearC_ofReal`). -/
theorem corrC_ofReal {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (s : ℝ) :
    corrC ξ V n η (s : ℂ) = innerSL ℂ ξ (V s (gaussSmear V n η)) := by
  rw [corrC, gaussSmearC_ofReal hn η hcont hbd hgrp s]

/-! ### Analytic continuation of the modular character to the KMS strip

The modular character `u_t(r) = exp(i·t·log((2−r)/r))` continues to an entire function of a *complex*
time `z`.  Evaluated on the boundary of the KMS strip `{0 ≤ Im z ≤ 1}` it implements the modular weight:
`u_{z+i}(r) = u_z(r)·(r/(2−r))`.  These scalar facts seed the modular flow's own strip/KMS property —
the regularity that makes `Δ^{it}` a participant in the strip-uniqueness comparison toward discharging the
labelled `hUniq` of one-particle Bisognano–Wichmann. -/

/-- The **complexified modular character** `u_z(r) = exp(i·z·log((2−r)/r))` on `(0,2)` (and `1` outside) —
    the analytic continuation of `modChar` to complex time `z`. -/
noncomputable def modCharC (z : ℂ) : ℝ → ℂ :=
  (Set.Ioo (0 : ℝ) 2).piecewise
    (fun r => Complex.exp (Complex.I * z * (Real.log ((2 - r) / r) : ℂ)))
    (fun _ => 1)

/-- The complexified character is Borel measurable (in `r`, for fixed `z`). -/
theorem measurable_modCharC (z : ℂ) : Measurable (modCharC z) := by
  apply Measurable.piecewise measurableSet_Ioo _ measurable_const
  apply Complex.continuous_exp.measurable.comp
  apply Measurable.mul measurable_const
  exact Complex.continuous_ofReal.measurable.comp
    (Real.measurable_log.comp ((measurable_const.sub measurable_id).div measurable_id))

/-- On `(0,2)` the complexified character is the bare exponential. -/
theorem modCharC_of_mem {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) (z : ℂ) :
    modCharC z r = Complex.exp (Complex.I * z * (Real.log ((2 - r) / r) : ℂ)) :=
  Set.piecewise_eq_of_mem _ _ _ hr

/-- On the real axis the complexification recovers `modChar`. -/
theorem modCharC_ofReal (t : ℝ) (r : ℝ) : modCharC (t : ℂ) r = modChar t r := rfl

/-- **The complexified modular character is entire** in `z` for each fixed `r`. -/
theorem differentiable_modCharC (r : ℝ) : Differentiable ℂ (fun z => modCharC z r) := by
  by_cases hr : r ∈ Set.Ioo (0 : ℝ) 2
  · have h : (fun z => modCharC z r)
        = fun z => Complex.exp (Complex.I * z * (Real.log ((2 - r) / r) : ℂ)) :=
      funext (fun z => modCharC_of_mem hr z)
    rw [h]
    exact Complex.differentiable_exp.comp
      (((differentiable_const _).mul differentiable_id).mul (differentiable_const _))
  · have h : (fun z => modCharC z r) = fun _ => (1 : ℂ) :=
      funext (fun z => Set.piecewise_eq_of_notMem _ _ _ hr)
    rw [h]; exact differentiable_const _

/-- **The modular-frequency `log((2−r)/r)` is uniformly bounded on the regular window** `[a, 2−a]`:
    `|log((2−r)/r)| ≤ log((2−a)/a)`.  This bounds the derivative of the modular character `i·log·u_z`, the
    domination needed for holomorphy of the strip extension under the integral. -/
theorem abs_log_div_le {a r : ℝ} (ha0 : 0 < a) (hr1 : a ≤ r) (hr2 : r ≤ 2 - a) :
    |Real.log ((2 - r) / r)| ≤ Real.log ((2 - a) / a) := by
  have hr0 : 0 < r := lt_of_lt_of_le ha0 hr1
  have h2r : 0 < 2 - r := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hnegL : -Real.log ((2 - r) / r) = Real.log (r / (2 - r)) := by rw [← Real.log_inv, inv_div]
    have h : Real.log (r / (2 - r)) ≤ Real.log ((2 - a) / a) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ h2r ha0]; nlinarith
    linarith
  · apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hr0 ha0]; nlinarith

/-- **The complex `z`-derivative of the modular character**: `d/dz u_z(r) = i·log((2−r)/r)·u_z(r)`.  This is
    the pointwise derivative that, integrated against the spectral measure and dominated in the regular
    regime, gives holomorphy of the strip extension `z ↦ ∫ u_z dμ` under the integral sign. -/
theorem hasDerivAt_modCharC {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) (z : ℂ) :
    HasDerivAt (fun z => modCharC z r)
      (Complex.I * (Real.log ((2 - r) / r) : ℂ) * modCharC z r) z := by
  have hfun : (fun z => modCharC z r)
      = fun z => Complex.exp (Complex.I * z * (Real.log ((2 - r) / r) : ℂ)) :=
    funext (fun z => modCharC_of_mem hr z)
  rw [hfun, modCharC_of_mem hr]
  have hlin : HasDerivAt (fun z => Complex.I * z * (Real.log ((2 - r) / r) : ℂ))
      (Complex.I * (Real.log ((2 - r) / r) : ℂ)) z := by
    simpa using (((hasDerivAt_id z).const_mul Complex.I).mul_const (Real.log ((2 - r) / r) : ℂ))
  have hexp := hlin.cexp
  convert hexp using 1
  ring

/-- **The KMS boundary flip** `u_{z+i}(r) = u_z(r)·(r/(2−r))`: shifting the imaginary part by the inverse
    temperature `β = 1` multiplies by the modular weight `r/(2−r) = exp(−log((2−r)/r))`.  This is the scalar
    core of the modular KMS condition. -/
theorem modCharC_kms_flip {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) (z : ℂ) :
    modCharC (z + Complex.I) r = modCharC z r * ((r / (2 - r) : ℝ) : ℂ) := by
  obtain ⟨hr0, hr2⟩ := hr
  have hpos : (0 : ℝ) < (2 - r) / r := by positivity
  rw [modCharC_of_mem ⟨hr0, hr2⟩, modCharC_of_mem ⟨hr0, hr2⟩]
  have hexp : Complex.I * (z + Complex.I) * (Real.log ((2 - r) / r) : ℂ)
      = Complex.I * z * (Real.log ((2 - r) / r) : ℂ) + (-(Real.log ((2 - r) / r) : ℂ)) := by
    linear_combination (Real.log ((2 - r) / r) : ℂ) * Complex.I_mul_I
  rw [hexp, Complex.exp_add]
  congr 1
  rw [show (-(Real.log ((2 - r) / r) : ℂ)) = ((-Real.log ((2 - r) / r) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos, inv_div]

/-- **The exact modulus of the complexified character on the strip**: `‖u_z(r)‖ = exp(−Im(z)·log((2−r)/r))`.
    On the real axis (`Im z = 0`) this is `1`; for `Im z ∈ (0,1]` it is the modular weight raised to `−Im z`.
    This is the seed of the *boundedness* of the strip extension of `⟪ξ, Δ^{it} ξ⟫` in the regular spectral
    regime (`σ(R) ⊆ [a, 2−a]`), where the exponent stays bounded. -/
theorem modCharC_norm {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 2) (z : ℂ) :
    ‖modCharC z r‖ = Real.exp (-z.im * Real.log ((2 - r) / r)) := by
  rw [modCharC_of_mem hr, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_sub, mul_zero, sub_zero, add_zero, zero_add]

/-- **Uniform bound on the strip in the regular spectral regime.**  For `r ∈ [a, 2−a]` (with `0 < a ≤ 1`)
    and `z` in the KMS strip (`0 ≤ Im z ≤ 1`), the complexified character is bounded by the constant
    `(2−a)/a`.  This is the boundedness that lets `z ↦ ∫ u_z dμ^R_ξ` be a *bounded* holomorphic strip
    extension of the modular correlation `⟪ξ, Δ^{it} ξ⟫` — the hypothesis the strip-uniqueness principle
    consumes — whenever the RvD spectrum lies in `[a, 2−a]`. -/
theorem modCharC_norm_le {a r : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hr1 : a ≤ r) (hr2 : r ≤ 2 - a)
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    ‖modCharC z r‖ ≤ (2 - a) / a := by
  have hr0 : 0 < r := lt_of_lt_of_le ha0 hr1
  have h2r : 0 < 2 - r := by linarith
  have hrmem : r ∈ Set.Ioo (0 : ℝ) 2 := ⟨hr0, by linarith⟩
  rw [modCharC_norm hrmem]
  set L := Real.log ((2 - r) / r) with hLdef
  set M := Real.log ((2 - a) / a) with hMdef
  have hMpos : 0 ≤ M := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hL_ub : L ≤ M := by
    rw [hLdef, hMdef]
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ hr0 ha0]; nlinarith
  have hnegL : -L = Real.log (r / (2 - r)) := by rw [hLdef, ← Real.log_inv, inv_div]
  have hL_lb : -M ≤ L := by
    have h : Real.log (r / (2 - r)) ≤ M := by
      rw [hMdef]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ h2r ha0]; nlinarith
    rw [← hnegL] at h; linarith
  have habsL : |L| ≤ M := abs_le.mpr ⟨hL_lb, hL_ub⟩
  have hkey : -z.im * L ≤ M :=
    calc -z.im * L = -(z.im * L) := by ring
      _ ≤ |z.im * L| := neg_le_abs _
      _ = z.im * |L| := by rw [abs_mul, abs_of_nonneg hz0]
      _ ≤ 1 * M := mul_le_mul hz1 habsL (abs_nonneg _) (by norm_num)
      _ = M := one_mul M
  calc Real.exp (-z.im * L) ≤ Real.exp M := Real.exp_le_exp.mpr hkey
    _ = (2 - a) / a := by rw [hMdef, Real.exp_log (div_pos (by linarith) ha0)]

end QIQTH.StandardSubspaceModular
