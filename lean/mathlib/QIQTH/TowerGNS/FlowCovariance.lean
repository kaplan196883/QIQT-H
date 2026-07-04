/-
  B5 + B6 (THE_TRANSPORT_AND_ACCOUNTING_PLAN.md) — THE IMPLEMENTATION THEOREM + the
  invariance of the limit von Neumann algebra under the transported flow.

  B5 — THE IMPLEMENTATION THEOREM (the binding verdict): the covariance relation between the
  transported flow and the tower representation is EXACT AT THE PRE-LEVEL — NO germ gluing is
  needed. `flowRaw` acts stage-diagonally and `leftMulRaw` lands at the joined stage `C₀ ⊔ C`,
  and the two commute ON THE NOSE (`flowRaw_leftMulRaw`) because the per-corner flow is
  multiplicative (`cornerFlow_mul`) and tower-equivariant (`cornerFlow_cornerEmbed`): both
  sides are `of (C₀ ⊔ C) (σ_t(ι a) · σ_t(ι x))` — the SAME stage, the SAME matrix. Completion
  induction then transports the identity verbatim: `U_t π(a) = π(σ_t a) U_t`
  (`towerFlow_towerRep`), and the group law collapses the conjugation form
  `U_t π(a) U_{−t} = π(σ_t a)` (`towerFlow_conj_towerRep`) — the transported flow IMPLEMENTS
  the per-corner modular flows in the tower representation.

  B6 — the stage algebras are conjugation-invariant SETWISE (`towerStageAlg_flow_conj`:
  σ_t is a bijection of each corner, `σ_t ∘ σ_{−t} = id`), so SOT-approximability from the
  union of stages is preserved under conjugation by the norm-preserving `towerFlow`
  (`SOTApprox.conj` — a general B(H) lemma: one approximant at the pulled-back tuple), and
  the LIMIT VON NEUMANN ALGEBRA IS INVARIANT under the transported flow
  (`towerLimitVN_flow_invariant`, iff form `towerLimitVN_flow_conj_mem_iff`).

  HONEST SCOPE (binding): the flow is the TRANSPORTED one (B3) — no Tomita operator, no Δ, no
  J, no separating property, and no type classification of `towerLimitVN` is claimed. The
  invariance is the algebraic covariance of the directed-union limit, nothing more.

  LEAN ARCHITECTURE (the R3 lesson, binding): the working lemma (`flowRaw_leftMulRaw`) lives
  at the RAW `⨁` type; completion-level proofs use the GNS-file incantations verbatim
  (`UniformSpace.Completion.induction_on` with `isClosed_eq <;> fun_prop`); the synonym is
  crossed only in application position, never by `rw`.
-/
import Mathlib
import QIQTH.TowerGNS.Flow
import QIQTH.TowerGNS.LimitVN

/-! ### The general SOT-approximation conjugation lemma (B6 tool — plain B(H), no tower) -/

namespace QIQTH.VonNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Conjugation preserves SOT-approximability**: if `T` is SOT-approximable from `A` and `U`
    is norm-nonincreasing, then `U ∘L T ∘L V` is SOT-approximable from the conjugated set
    `(fun a => U ∘L a ∘L V) '' A` — approximate at the pulled-back tuple `V ∘ ξ` and dominate
    `‖U ((T − a)(V ξᵢ))‖` by `‖(T − a)(V ξᵢ)‖`. -/
theorem SOTApprox.conj {A : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} (hT : SOTApprox A T)
    (U V : H →L[ℂ] H) (hU : ∀ ξ, ‖U ξ‖ ≤ ‖ξ‖) :
    SOTApprox ((fun a => U ∘L a ∘L V) '' A) (U ∘L T ∘L V) := by
  intro n ξ ε hε
  obtain ⟨a, ha, hclose⟩ := hT n (fun i => V (ξ i)) ε hε
  refine ⟨U ∘L a ∘L V, Set.mem_image_of_mem _ ha, fun i => ?_⟩
  have hpt : (U ∘L T ∘L V) (ξ i) - (U ∘L a ∘L V) (ξ i)
      = U (T (V (ξ i)) - a (V (ξ i))) := by
    simp only [ContinuousLinearMap.comp_apply, map_sub]
  rw [hpt]
  exact lt_of_le_of_lt (hU _) (hclose i)

end QIQTH.VonNeumann

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### B5 — the implementation theorem: covariance EXACT at the pre-level (no germ) -/

/-- **B5 KEY (raw) — THE PRE-LEVEL COVARIANCE, EXACT**: `flowRaw` commutes with `leftMulRaw`
    ON THE NOSE — no germ gluing. On a pure component both sides land at the SAME stage
    `C₀ ⊔ C` with the SAME matrix: `σ_t(ι a · ι x) = σ_t(ι a) · σ_t(ι x) = ι(σ_t a) · ι(σ_t x)`
    by `cornerFlow_mul` + `cornerFlow_cornerEmbed`. -/
theorem flowRaw_leftMulRaw (t : ℝ) (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    flowRaw L ω β t (leftMulRaw L C₀ a x)
      = leftMulRaw L C₀ (cornerFlow L ω β C₀ t a) (flowRaw L ω β t x) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (leftMulRaw L C₀ a), map_zero (flowRaw L ω β t),
      map_zero (leftMulRaw L C₀ (cornerFlow L ω β C₀ t a))]
  | of C v =>
    rw [leftMulRaw_of, flowRaw_of, flowRaw_of, leftMulRaw_of, cornerFlow_mul,
      cornerFlow_cornerEmbed, cornerFlow_cornerEmbed]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (leftMulRaw L C₀ a), map_add (flowRaw L ω β t), h₁, h₂,
      map_add (flowRaw L ω β t), map_add (leftMulRaw L C₀ (cornerFlow L ω β C₀ t a))]

/-- **The composition form of the implementation theorem**: `U_t ∘ π(a) = π(σ_t a) ∘ U_t` on
    the completion — the pre-level identity is EXACT, so completion induction transports it
    verbatim. -/
theorem towerFlow_towerRep (t : ℝ) (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerFlow L ω β t ∘L towerRep L ω β C₀ a
      = towerRep L ω β C₀ (cornerFlow L ω β C₀ t a) ∘L towerFlow L ω β t := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, towerRep_apply,
      towerRepCLM_coe, towerFlow_coe, towerFlow_coe, towerRep_apply, towerRepCLM_coe]
    have h : flowPre L ω β t (towerLeftMul L ω β C₀ a x)
        = towerLeftMul L ω β C₀ (cornerFlow L ω β C₀ t a) (flowPre L ω β t x) :=
      flowRaw_leftMulRaw L ω β t C₀ a x
    rw [h]

/-- **B5 CAPSTONE — THE IMPLEMENTATION THEOREM (conjugation form)**:
    `U_t π(a) U_{−t} = π(σ_t a)` — the transported flow implements the per-corner Gibbs
    modular flows in the tower representation. The covariance was EXACT at the pre-level
    (`flowRaw_leftMulRaw` — no germ), and the group law `U_t U_{−t} = U_0 = 1` collapses the
    conjugation. -/
theorem towerFlow_conj_towerRep (t : ℝ) (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerFlow L ω β t ∘L towerRep L ω β C₀ a ∘L towerFlow L ω β (-t)
      = towerRep L ω β C₀ (cornerFlow L ω β C₀ t a) := by
  rw [← ContinuousLinearMap.comp_assoc, towerFlow_towerRep,
    ContinuousLinearMap.comp_assoc, towerFlow_comp, add_neg_cancel, towerFlow_zero,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

/-! ### B6 — the limit von Neumann algebra is invariant under the transported flow -/

/-- The transported flow preserves the norm (from `towerFlow_inner` — the B3 unitarity, in
    norm form). -/
theorem towerFlow_norm_eq (t : ℝ) (ξ : TowerGNS L ω β) :
    ‖towerFlow L ω β t ξ‖ = ‖ξ‖ := by
  have hinner : ⟪towerFlow L ω β t ξ, towerFlow L ω β t ξ⟫_ℂ = ⟪ξ, ξ⟫_ℂ :=
    towerFlow_inner L ω β t ξ ξ
  have h2 : ‖towerFlow L ω β t ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (towerFlow L ω β t ξ),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) ξ, hinner]
  calc ‖towerFlow L ω β t ξ‖
      = Real.sqrt (‖towerFlow L ω β t ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖ξ‖ ^ 2) := by rw [h2]
    _ = ‖ξ‖ := Real.sqrt_sq (norm_nonneg _)

/-- The reversed flow undoes the flow pointwise: `U_{−t} (U_t ξ) = ξ`. -/
theorem towerFlow_neg_towerFlow (t : ℝ) (ξ : TowerGNS L ω β) :
    towerFlow L ω β (-t) (towerFlow L ω β t ξ) = ξ := by
  have h : (towerFlow L ω β (-t) ∘L towerFlow L ω β t) ξ
      = towerFlow L ω β (-t) (towerFlow L ω β t ξ) := rfl
  rw [towerFlow_comp, neg_add_cancel, towerFlow_zero, ContinuousLinearMap.one_apply] at h
  exact h.symm

/-- **B6 KEY — conjugation by the flow maps each stage algebra ONTO itself**:
    `U_t (π_C₀(A)) U_{−t} = π_C₀(A)` as SETS — `⊆` is the implementation theorem
    (`U_t π(a) U_{−t} = π(σ_t a)`), and `⊇` is the surjectivity of `σ_t` on the corner
    (`σ_t ∘ σ_{−t} = σ_0 = id`). -/
theorem towerStageAlg_flow_conj (t : ℝ) (C₀ : Finset M) :
    (fun T => towerFlow L ω β t ∘L T ∘L towerFlow L ω β (-t)) ''
        (towerStageAlg L ω β C₀ : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
      = (towerStageAlg L ω β C₀ : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨a, rfl⟩ := hS
    show towerFlow L ω β t ∘L towerRep L ω β C₀ a ∘L towerFlow L ω β (-t)
        ∈ (towerStageAlg L ω β C₀ : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
    rw [towerFlow_conj_towerRep]
    exact ⟨cornerFlow L ω β C₀ t a, rfl⟩
  · intro hT
    obtain ⟨a, rfl⟩ := hT
    refine ⟨towerRep L ω β C₀ (cornerFlow L ω β C₀ (-t) a),
      ⟨cornerFlow L ω β C₀ (-t) a, rfl⟩, ?_⟩
    show towerFlow L ω β t ∘L towerRep L ω β C₀ (cornerFlow L ω β C₀ (-t) a)
          ∘L towerFlow L ω β (-t)
        = towerRep L ω β C₀ a
    rw [towerFlow_conj_towerRep, cornerFlow_comp, add_neg_cancel, cornerFlow_zero]

/-- **B6 CAPSTONE — THE LIMIT VON NEUMANN ALGEBRA IS INVARIANT UNDER THE TRANSPORTED FLOW**:
    `T ∈ towerLimitVN → U_t T U_{−t} ∈ towerLimitVN` — SOT-approximability from the union of
    the stages is preserved by conjugation (`SOTApprox.conj`, `U_t` is norm-preserving), and
    the conjugated union of stages IS the union of stages (`towerStageAlg_flow_conj`). -/
theorem towerLimitVN_flow_invariant (t : ℝ) {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    towerFlow L ω β t ∘L T ∘L towerFlow L ω β (-t) ∈ towerLimitVN L ω β := by
  rw [mem_towerLimitVN_iff] at hT ⊢
  have hU : ∀ ξ : TowerGNS L ω β, ‖towerFlow L ω β t ξ‖ ≤ ‖ξ‖ := fun ξ =>
    le_of_eq (towerFlow_norm_eq L ω β t ξ)
  have hconj := hT.conj (towerFlow L ω β t) (towerFlow L ω β (-t)) hU
  have himg : (fun a => towerFlow L ω β t ∘L a ∘L towerFlow L ω β (-t)) ''
        (⋃ C, (towerStageAlg L ω β C : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)))
      = ⋃ C, (towerStageAlg L ω β C : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) := by
    rw [Set.image_iUnion]
    exact Set.iUnion_congr fun C => towerStageAlg_flow_conj L ω β t C
  rw [← himg]
  exact hconj

/-- **The iff form of the invariance**: conjugation by the flow is a BIJECTION of the limit
    von Neumann algebra — `U_{−t} (U_t T U_{−t}) U_t = T` recovers `T`. -/
theorem towerLimitVN_flow_conj_mem_iff (t : ℝ) (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    towerFlow L ω β t ∘L T ∘L towerFlow L ω β (-t) ∈ towerLimitVN L ω β
      ↔ T ∈ towerLimitVN L ω β := by
  constructor
  · intro h
    have h2 := towerLimitVN_flow_invariant L ω β (-t) h
    have heq : towerFlow L ω β (-t)
          ∘L (towerFlow L ω β t ∘L T ∘L towerFlow L ω β (-t)) ∘L towerFlow L ω β (- -t)
        = T := by
      ext ξ
      simp only [ContinuousLinearMap.comp_apply]
      rw [neg_neg, towerFlow_neg_towerFlow, towerFlow_neg_towerFlow]
    rwa [heq] at h2
  · exact towerLimitVN_flow_invariant L ω β t

end QIQTH.TowerGNS
