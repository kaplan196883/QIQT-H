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

end QIQTH.StandardSubspaceModular
