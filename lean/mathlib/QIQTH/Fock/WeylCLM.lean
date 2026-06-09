/-
  The completed-Fock / CLM lift (optional increment, GPT consult #3): bundle the bounded Weyl operators
  as genuine **continuous linear maps on the Fock Hilbert space** `Fock H = Completion(FockPre H)`, and
  read the Weyl-bit Born weights as expectations of bounded positive effects in the genuine continuum
  vacuum state `vacuumState`.

  Earlier modules build the Weyl operators only on the pre-Hilbert space `FockPre H` (as `LinearMap`s /
  `LinearIsometry`s), with the vacuum functional `re⟪Ω,·Ω⟫` taken at the pre-completion level.  Here we
  lift everything to the genuine Hilbert space: a bounded `FockPre` operator extends uniquely to a
  `ContinuousLinearMap` on the completion (`ContinuousLinearMap.extend` along the dense isometric
  embedding `toComplL`), giving:

    * `weylCLM u : Fock H →L[ℂ] Fock H` — the bounded Weyl operator, with `W(0)=1`, `W(−u)W(u)=1`
      (unitary), isometric;
    * the genuine vacuum two-point matrix element `⟪Ω, W(u)Ω⟫ = exp(−½⟪u,u⟫)` ON THE HILBERT SPACE;
    * `weylBitEffectCLM u s = (2·1 + s·W(u) + s·W(−u))/4` — a bounded self-adjoint effect with the operator
      POVM completeness `E(u,+1)+E(u,−1)=1`, whose **vacuum-state expectation is the Weyl-bit Born weight**
      `vacuumState (E(u,+1)) = (1+exp(−½‖u‖²))/2 = weylBitWeight u`.

  This is GPT's "single load-bearing operator-level theorem" (bounded `W(u):Fock→Fock`, CCR-unitary, with
  the quasifree two-point function) made literal on the completed Hilbert space, plus the operational
  C\*-state reading of the single-mode Born weight.  Axiom-free.
-/
import QIQTH.Fock.WeylOp
import QIQTH.Fock.VacuumState
import QIQTH.Fock.WeylCovariance
import QIQTH.Fock.WeylBitMeasure
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace
open UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Bundled lift of a bounded FockPre operator to the Fock Hilbert space -/

/-- **The bundled lift** of a bounded `FockPre` operator to a continuous linear map on the Fock Hilbert
    space, via `ContinuousLinearMap.extend` along the dense isometric embedding `toComplL`. -/
noncomputable def clmLift (T : FockPre H →L[ℂ] FockPre H) : Fock H →L[ℂ] Fock H :=
  ContinuousLinearMap.extend (Completion.toComplL.comp T) Completion.toComplL

theorem clmLift_coe (T : FockPre H →L[ℂ] FockPre H) (φ : FockPre H) :
    clmLift T (φ : Fock H) = (T φ : Fock H) := by
  have hde : DenseRange (Completion.toComplL : FockPre H →L[ℂ] Fock H) := by
    rw [Completion.coe_toComplL]; exact Completion.denseRange_coe
  have hui : IsUniformInducing (Completion.toComplL : FockPre H →L[ℂ] Fock H) := by
    rw [Completion.coe_toComplL]; exact Completion.isUniformInducing_coe _
  have h := ContinuousLinearMap.extend_eq (Completion.toComplL.comp T) hde hui φ
  simpa only [clmLift, Completion.coe_toComplL, ContinuousLinearMap.comp_apply] using h

/-- The lift is functorial on the dense subspace, hence on all of `Fock H`: `clmLift (T∘S)=clmLift T∘clmLift S`. -/
theorem clmLift_comp (T S : FockPre H →L[ℂ] FockPre H) :
    clmLift (T.comp S) = (clmLift T).comp (clmLift S) := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Completion.induction_on x
    (isClosed_eq (clmLift (T.comp S)).continuous
      ((clmLift T).comp (clmLift S)).continuous) fun φ => ?_
  rw [clmLift_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    clmLift_coe, clmLift_coe]

/-- `clmLift 1 = 1`. -/
theorem clmLift_one : clmLift (1 : FockPre H →L[ℂ] FockPre H) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Completion.induction_on x
    (isClosed_eq (clmLift 1).continuous (1 : Fock H →L[ℂ] Fock H).continuous) fun φ => ?_
  rw [clmLift_coe, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]

/-! ### The bounded Weyl operator on the Fock Hilbert space -/

/-- **The bounded Weyl operator** `W(u)` as a continuous linear map on the Fock Hilbert space. -/
noncomputable def weylCLM (u : H) : Fock H →L[ℂ] Fock H :=
  clmLift (weylₗᵢ u).toContinuousLinearMap

theorem weylCLM_coe (u : H) (φ : FockPre H) :
    weylCLM u (φ : Fock H) = (weylPre u φ : Fock H) :=
  clmLift_coe _ φ

/-- `W(0) = 1`. -/
theorem weylCLM_zero : weylCLM (0 : H) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Completion.induction_on x
    (isClosed_eq (weylCLM 0).continuous (1 : Fock H →L[ℂ] Fock H).continuous) fun φ => ?_
  rw [weylCLM_coe, weylPre_zero, LinearMap.id_apply, ContinuousLinearMap.one_apply]

/-- **CCR-unitarity**: `W(−u) W(u) = 1` (so `W(u)` is invertible with inverse `W(−u)`). -/
theorem weylCLM_neg_cancel (u : H) : (weylCLM (-u)).comp (weylCLM u) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Completion.induction_on x
    (isClosed_eq ((weylCLM (-u)).comp (weylCLM u)).continuous
      (1 : Fock H →L[ℂ] Fock H).continuous) fun φ => ?_
  rw [ContinuousLinearMap.comp_apply, weylCLM_coe, weylCLM_coe, ContinuousLinearMap.one_apply,
    weylPre_neg_cancel u φ]

/-- **`W(u)` is isometric on the Fock Hilbert space** (norm-preserving), since `weylPre u` is. -/
theorem weylCLM_norm (u : H) (x : Fock H) : ‖weylCLM u x‖ = ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_eq ((weylCLM u).continuous.norm) continuous_norm) fun φ => ?_
  rw [weylCLM_coe, Completion.norm_coe, Completion.norm_coe]
  exact (weylₗᵢ u).norm_map φ

/-! ### The genuine vacuum two-point function on the Hilbert space -/

/-- **The vacuum two-point matrix element on the Fock Hilbert space**: `⟪Ω, W(u)Ω⟫ = exp(−½⟪u,u⟫)`. -/
theorem weylCLM_vacuum_inner (u : H) :
    (⟪(Fock.vacuum : Fock H), weylCLM u Fock.vacuum⟫_ℂ : ℂ)
      = Complex.exp (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ) := by
  have hw : weylCLM u (Fock.vacuum : Fock H)
      = ((weylPre u (FockPre.expVec 0) : FockPre H) : Fock H) := by
    rw [Fock.vacuum, Fock.expVec, weylCLM_coe]
  rw [hw]
  simp only [Fock.vacuum, Fock.expVec, UniformSpace.Completion.inner_coe]
  exact fockInner_vacuum_weyl u

/-- `⟪u,u⟫` is a nonnegative real, as a complex number: `⟪u,u⟫ = ↑‖u‖²`. -/
theorem inner_self_ofReal (u : H) : (⟪u, u⟫_ℂ : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

/-- The Weyl exponent as a real cast: `−½⟪u,u⟫ = ↑(−‖u‖²/2)`. -/
theorem weyl_exponent_ofReal (u : H) :
    (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ) = ((-(‖u‖ ^ 2) / 2 : ℝ) : ℂ) := by
  rw [inner_self_ofReal]; push_cast; ring

/-- The complex vacuum two-point function has real part `exp(−‖u‖²/2)` (the inner product `⟪u,u⟫` is a
    nonnegative real). -/
theorem weyl_vacuum_re (u : H) :
    RCLike.re (Complex.exp (-(1 / 2 : ℂ) * ⟪u, u⟫_ℂ)) = Real.exp (-(‖u‖ ^ 2) / 2) := by
  rw [weyl_exponent_ofReal, ← Complex.ofReal_exp]
  exact RCLike.ofReal_re _

/-- **The vacuum-state value of the Weyl operator** is the quasifree two-point function `exp(−‖u‖²/2)`. -/
theorem vacuumState_weylCLM (u : H) :
    vacuumState (weylCLM u) = Real.exp (-(‖u‖ ^ 2) / 2) := by
  rw [vacuumState, weylCLM_vacuum_inner, weyl_vacuum_re]

/-! ### The Weyl-bit effect on the Hilbert space and the Born weight as a vacuum-state expectation -/

/-- **The Weyl-bit effect** `E(u,s) = (2·1 + s·W(u) + s·W(−u))/4` as a bounded operator on the Fock
    Hilbert space (`s = ±1`). -/
noncomputable def weylBitEffectCLM (u : H) (s : ℂ) : Fock H →L[ℂ] Fock H :=
  (1 / 4 : ℂ) • ((2 : ℂ) • 1 + s • weylCLM u + s • weylCLM (-u))

/-- **Operator POVM completeness on the Hilbert space**: `E(u,+1) + E(u,−1) = 1`. -/
theorem weylBitEffectCLM_complete (u : H) :
    weylBitEffectCLM u 1 + weylBitEffectCLM u (-1) = 1 := by
  simp only [weylBitEffectCLM, one_smul, neg_smul]
  module

/-- The vacuum two-point function as a real-cast value: `⟪Ω, W(u)Ω⟫ = exp(−‖u‖²/2)` (a real number). -/
theorem weylCLM_vacuum_inner_ofReal (u : H) :
    (⟪(Fock.vacuum : Fock H), weylCLM u Fock.vacuum⟫_ℂ : ℂ) = ((Real.exp (-(‖u‖ ^ 2) / 2) : ℝ) : ℂ) := by
  rw [weylCLM_vacuum_inner, weyl_exponent_ofReal, ← Complex.ofReal_exp]

/-- The complex vacuum matrix element of the Weyl-bit effect `E(u,+1)` is the (real) Born weight. -/
theorem weylBitEffectCLM_true_inner (u : H) :
    (⟪(Fock.vacuum : Fock H), weylBitEffectCLM u 1 Fock.vacuum⟫_ℂ : ℂ)
      = ((weylBitWeight u : ℝ) : ℂ) := by
  rw [weylBitEffectCLM]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, one_smul, inner_smul_right, inner_add_right]
  rw [Fock.inner_vacuum, weylCLM_vacuum_inner_ofReal, weylCLM_vacuum_inner_ofReal]
  have hn : Real.exp (-(‖(-u)‖ ^ 2) / 2) = Real.exp (-(‖u‖ ^ 2) / 2) := by rw [norm_neg]
  rw [hn]
  simp only [weylBitWeight]
  push_cast
  ring

/-- **The single-mode Weyl-bit Born weight is a genuine vacuum C\*-state expectation of a bounded effect**
    on the completed Fock Hilbert space: `vacuumState (E(u,+1)) = (1+exp(−½‖u‖²))/2 = weylBitWeight u`.
    Together with `weylBitEffectCLM_complete` this exhibits the Weyl-bit Born law as a genuine
    two-outcome POVM `{E(u,±1)}` of bounded operators read in the continuum vacuum state. -/
theorem vacuumState_weylBitEffectCLM_true (u : H) :
    vacuumState (weylBitEffectCLM u 1) = weylBitWeight u := by
  rw [vacuumState, weylBitEffectCLM_true_inner]
  simp

/-! ### The JOINT multi-mode effect on the Hilbert space (closing the pre-Hilbert gap) -/

section Joint

variable {ι : Type*} [DecidableEq ι]

/-- The single-mode bit operator `A(u,s)=(I+s·W(u))/2` as a continuous linear map on `FockPre H`. -/
noncomputable def bitOpCLM (u : H) (s : ℂ) : FockPre H →L[ℂ] FockPre H :=
  (1 / 2 : ℂ) • (1 + s • (weylₗᵢ u).toContinuousLinearMap)

theorem bitOpCLM_apply (u : H) (s : ℂ) (φ : FockPre H) : bitOpCLM u s φ = bitOp u s φ := by
  rw [bitOp_apply]
  simp only [bitOpCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, LinearIsometry.coe_toContinuousLinearMap]
  rfl

/-- The bit CLMs commute under the isotropy (microcausality) condition. -/
theorem bitOpCLM_commute {u : ι → H} (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {i j : ι} (hij : i ≠ j) (s s' : ℂ) :
    Commute (bitOpCLM (u i) s) (bitOpCLM (u j) s') := by
  show bitOpCLM (u i) s * bitOpCLM (u j) s' = bitOpCLM (u j) s' * bitOpCLM (u i) s
  ext φ
  show bitOpCLM (u i) s (bitOpCLM (u j) s' φ) = bitOpCLM (u j) s' (bitOpCLM (u i) s φ)
  rw [bitOpCLM_apply, bitOpCLM_apply, bitOpCLM_apply, bitOpCLM_apply]
  exact bitOp_comm (u i) (u j) s s' (hiso i j hij) φ

/-- The joint product operator `∏_{i∈J} A(uᵢ,sᵢ)` as a CLM on `FockPre H` (order-independent). -/
noncomputable def bornProdOpCLM (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (s : ι → ℂ) (J : Finset ι) :
    FockPre H →L[ℂ] FockPre H :=
  J.noncommProd (fun i => bitOpCLM (u i) (s i))
    (fun i _ j _ hij => bitOpCLM_commute hiso hij (s i) (s j))

/-- The joint product CLM applied to the vacuum is the Born history vector `bornVecTot`. -/
theorem bornProdOpCLM_vac (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (s : ι → ℂ) (J : Finset ι) :
    bornProdOpCLM u hiso s J (vac H) = bornVecTot u hiso s J := by
  classical
  induction J using Finset.induction with
  | empty =>
    rw [bornProdOpCLM, Finset.noncommProd_empty, bornVecTot_empty, ContinuousLinearMap.one_apply]
  | @insert a J' ha ih =>
    rw [bornProdOpCLM, Finset.noncommProd_insert_of_notMem _ _ _ _ ha, bornVecTot_insert u hiso s ha,
      ContinuousLinearMap.mul_apply, bitOpCLM_apply]
    show bitOp (u a) (s a) (bornProdOpCLM u hiso s J' (vac H)) = _
    rw [ih]

/-- **The JOINT Weyl-bit effect** `E_σ = (∏ A(uᵢ,σᵢ))* (∏ A(uᵢ,σᵢ))` as a bounded operator on the completed
    Fock Hilbert space. -/
noncomputable def jointEffectCLM (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (σ : ∀ j : J, Bool) :
    Fock H →L[ℂ] Fock H :=
  let P := clmLift (bornProdOpCLM u hiso (signExt J σ) J)
  (ContinuousLinearMap.adjoint P) ∘L P

/-- The joint effect is a positive bounded operator (it is `P*P`). -/
theorem jointEffectCLM_isPositive (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (σ : ∀ j : J, Bool) :
    (jointEffectCLM u hiso J σ).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- **The JOINT Born weight is a genuine vacuum C\*-state expectation of a bounded positive effect on the
    completed Fock Hilbert space**: `vacuumState (E_σ) = bornWeight u J σ`.  This closes the pre-Hilbert gap —
    the full multi-mode Born law (not just single-mode) is realized by bounded Hilbert-space POVM effects. -/
theorem vacuumState_jointEffectCLM (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (σ : ∀ j : J, Bool) :
    vacuumState (jointEffectCLM u hiso J σ) = bornWeight u hiso J σ := by
  have hP : (clmLift (bornProdOpCLM u hiso (signExt J σ) J)) (Fock.vacuum : Fock H)
      = ((bornVecTot u hiso (signExt J σ) J : FockPre H) : Fock H) := by
    have hv : (Fock.vacuum : Fock H) = ((vac H : FockPre H) : Fock H) := rfl
    rw [hv, clmLift_coe, bornProdOpCLM_vac]
  rw [vacuumState, jointEffectCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, hP, UniformSpace.Completion.inner_coe,
    inner_self_eq_norm_sq, bornWeight]

/-- `bornProdOpCLM` applied to a vector factors a bit off the head (insert form). -/
theorem bornProdOpCLM_insert_apply (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (s : ι → ℂ) {a : ι} {J' : Finset ι}
    (ha : a ∉ J') (φ : FockPre H) :
    bornProdOpCLM u hiso s (insert a J') φ
      = bitOp (u a) (s a) (bornProdOpCLM u hiso s J' φ) := by
  rw [bornProdOpCLM, Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
    ContinuousLinearMap.mul_apply, bitOpCLM_apply]
  rfl

/-- `bornProdOpCLM` depends only on the signs on `J`. -/
theorem bornProdOpCLM_congr (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) {s₁ s₂ : ι → ℂ} {J : Finset ι}
    (h : ∀ i ∈ J, s₁ i = s₂ i) (φ : FockPre H) :
    bornProdOpCLM u hiso s₁ J φ = bornProdOpCLM u hiso s₂ J φ := by
  have : bornProdOpCLM u hiso s₁ J = bornProdOpCLM u hiso s₂ J := by
    unfold bornProdOpCLM
    exact Finset.noncommProd_congr rfl (fun i hi => by rw [h i hi]) _
  rw [this]

/-- Insert form of the product-vector norm (factors a bit off the head; defeq-matches the split equiv). -/
theorem bornProdOpCLM_normSq_insert (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) {a : ι} {J' : Finset ι} (ha : a ∉ J')
    (φ : FockPre H) (σ : ∀ j : (insert a J' : Finset ι), Bool) :
    ‖bornProdOpCLM u hiso (signExt (insert a J') σ) (insert a J') φ‖ ^ 2
      = ‖bitOp (u a) (sgn (σ ⟨a, Finset.mem_insert_self a J'⟩))
          (bornProdOpCLM u hiso
            (signExt J' (fun j => σ ⟨j.1, Finset.mem_insert_of_mem j.2⟩)) J' φ)‖ ^ 2 := by
  have h1 : signExt (insert a J') σ a = sgn (σ ⟨a, Finset.mem_insert_self a J'⟩) := by
    rw [signExt, dif_pos (Finset.mem_insert_self a J')]
  have h2 : bornProdOpCLM u hiso (signExt (insert a J') σ) J' φ
      = bornProdOpCLM u hiso (signExt J' (fun j => σ ⟨j.1, Finset.mem_insert_of_mem j.2⟩)) J' φ := by
    refine bornProdOpCLM_congr u hiso (fun i hi => ?_) φ
    have hi' : i ∈ insert a J' := Finset.mem_insert_of_mem hi
    rw [signExt, signExt, dif_pos hi, dif_pos hi']
  rw [bornProdOpCLM_insert_apply u hiso _ ha, h1, h2]

/-- **Generalized normalization**: `∑_σ ‖(∏A(uᵢ,σᵢ)) φ‖² = ‖φ‖²` for ANY vector `φ` (not just the vacuum) —
    the operator analogue of `bornWeight_total`, the ingredient for joint POVM completeness. -/
theorem bornProdOpCLM_normSq_sum (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (φ : FockPre H) :
    ∑ σ : (∀ j : J, Bool), ‖bornProdOpCLM u hiso (signExt J σ) J φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  classical
  induction J using Finset.induction with
  | empty => simp [bornProdOpCLM, Finset.noncommProd_empty]
  | @insert a J' ha ih =>
    rw [Fintype.sum_equiv (insertBoolSplit ha)
        (fun σ => ‖bornProdOpCLM u hiso (signExt (insert a J') σ) (insert a J') φ‖ ^ 2)
        (fun p => ‖bitOp (u a) (sgn p.1)
          (bornProdOpCLM u hiso (signExt J' p.2) J' φ)‖ ^ 2)
        (fun σ => bornProdOpCLM_normSq_insert u hiso ha φ σ),
      Fintype.sum_prod_type, Finset.sum_comm, ← ih]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_bool]
    simp only [sgn, Bool.false_eq_true, reduceIte]
    exact bit_normSq_sum (u a) (bornProdOpCLM u hiso (signExt J' τ) J' φ)

/-- The generalized normalization lifted to the completed Hilbert space: `∑_σ ‖P_σ x‖² = ‖x‖²`. -/
theorem clmLift_bornProd_normSq_sum (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (x : Fock H) :
    ∑ σ : (∀ j : J, Bool),
      ‖clmLift (bornProdOpCLM u hiso (signExt J σ) J) x‖ ^ 2 = ‖x‖ ^ 2 := by
  refine Completion.induction_on x
    (isClosed_eq (continuous_finset_sum _ fun σ _ =>
      ((clmLift _).continuous.norm).pow 2) (continuous_norm.pow 2)) (fun φ => ?_)
  simp only [clmLift_coe, Completion.norm_coe]
  exact bornProdOpCLM_normSq_sum u hiso J φ

/-- **JOINT POVM COMPLETENESS on the Hilbert space**: `∑_σ E_σ = 1`.  Together with
    `jointEffectCLM_isPositive` and `vacuumState_jointEffectCLM`, this makes `{E_σ}` a genuine
    operator-level POVM on the completed Fock Hilbert space whose vacuum expectations are the Born weights. -/
theorem jointEffectCLM_complete (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) :
    ∑ σ : (∀ j : J, Bool), jointEffectCLM u hiso J σ = 1 := by
  have hterm : ∀ (x : Fock H) (σ : (∀ j : J, Bool)), ⟪jointEffectCLM u hiso J σ x, x⟫_ℂ
      = ((‖clmLift (bornProdOpCLM u hiso (signExt J σ) J) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x σ
    rw [jointEffectCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  have key : ∀ x : Fock H,
      ⟪((∑ σ : (∀ j : J, Bool), jointEffectCLM u hiso J σ) - 1) x, x⟫_ℂ = 0 := by
    intro x
    have hsum : ∑ σ : (∀ j : J, Bool), ⟪jointEffectCLM u hiso J σ x, x⟫_ℂ = ⟪x, x⟫_ℂ := by
      rw [Finset.sum_congr rfl (fun σ _ => hterm x σ), ← Complex.ofReal_sum,
        clmLift_bornProd_normSq_sum, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, ContinuousLinearMap.sum_apply, sum_inner,
      ContinuousLinearMap.one_apply, hsum, sub_self]
  have h0 : ((∑ σ : (∀ j : J, Bool), jointEffectCLM u hiso J σ) - 1).toLinearMap = 0 :=
    (inner_map_self_eq_zero _).mp key
  have h1 : (∑ σ : (∀ j : J, Bool), jointEffectCLM u hiso J σ) - 1 = 0 := by
    ext x
    simpa using LinearMap.congr_fun h0 x
  exact sub_eq_zero.mp h1

end Joint

end QIQTH.Fock
