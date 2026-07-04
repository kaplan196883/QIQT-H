/-
  THE SEPARATION S5–S8 (THE_SEPARATION_PLAN.md) — THE STANDARD-FORM BANNER:

  Ω is CYCLIC AND SEPARATING for towerLimitVN — the standard-form hypothesis pair of
  Tomita–Takesaki theory. Separation is the HYPOTHESIS for that theory, not the theory:
  no Tomita operator S₀, no Δ, no J, no KMS condition at the limit, no type classification
  is constructed or claimed here. The right action is bounded with a weighted Frobenius
  constant, never claimed contractive; no right ⋆-anti-representation laws are stated.

  S5 — the raw left–right exchange (binding verdict A2: COMPLETION-ONLY via the germ at a
  FRESH DEEP STAGE `D := (C₁ ⊔ (C₀ ⊔ C)) ⊔ (C₀ ⊔ (C₁ ⊔ C))` — no pre-level equation, no
  HEq, no sup_comm casts), then the CLM commutation `towerRightMul_comm_towerRep`: the
  right multiplications lie in the commutant of every stage algebra.

  S6 — `commute_of_mem_limitVN` (binding verdict A3: PURE BICOMMUTANT ALGEBRA — the limit
  is the double centralizer of the union of the stages, and Set.centralizer membership is
  DEFINITIONAL, so an operator commuting with every stage commutes with the whole limit by
  direct application) + `towerRightMul_comm_limitVN`.

  S7 — CAPSTONE `towerCyclicVec_separating`: T ∈ towerLimitVN, TΩ = 0 ⟹ T = 0 — T vanishes
  on R8's EXISTING orbit (T(R_aΩ) = R_a(TΩ) = 0, binding verdict A4: no new right-orbit
  density lemma) and `ContinuousLinearMap.ext_on` closes over R8's density.

  S8 — Ω cyclic for the LIMIT (`dense_span_limitVN_orbit_cyclicVec`: the limit orbit
  contains R8's stage orbit) and `towerLimitVN_eq_of_apply_cyclicVec` (TΩ = SΩ ⟹ T = S —
  the well-definedness germ of a future Tomita S₀; S₀ itself is NOT constructed).
-/
import Mathlib
import QIQTH.TowerGNS.RightMul
import QIQTH.TowerGNS.LimitVN

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### S5 — the raw left–right exchange (the deep-stage double germ) -/

/-- **S5 — THE EXCHANGE**: in the completion, the left action of `b` and the right action of
    `a` commute on every raw vector — `↑(π₀(b)(x·ι a)) = ↑((π₀(b) x)·ι a)`. The two sides
    land at the DIFFERENT stages `C₁ ⊔ (C₀ ⊔ C)` and `C₀ ⊔ (C₁ ⊔ C)`; both are glued by the
    germ identity to the FRESH DEEP STAGE `D := (C₁ ⊔ (C₀ ⊔ C)) ⊔ (C₀ ⊔ (C₁ ⊔ C))` (bare
    subset proofs — no HEq, no sup_comm cast), where the embedded matrices agree by
    functoriality and `mul_assoc`. -/
theorem towerCoe_leftMul_rightMul_exchange (C₁ C₀ : Finset M) (b : DiamondAlg L C₁)
    (a : DiamondAlg L C₀) (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (leftMulRaw L C₁ b (rightMulRaw L C₀ a x))
      = towerCoe L ω β (rightMulRaw L C₀ a (leftMulRaw L C₁ b x)) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of C v =>
    simp only [rightMulRaw_of, leftMulRaw_of]
    have hL : C₁ ⊔ (C₀ ⊔ C) ⊆ (C₁ ⊔ (C₀ ⊔ C)) ⊔ (C₀ ⊔ (C₁ ⊔ C)) :=
      Finset.subset_union_left
    have hR : C₀ ⊔ (C₁ ⊔ C) ⊆ (C₁ ⊔ (C₀ ⊔ C)) ⊔ (C₀ ⊔ (C₁ ⊔ C)) :=
      Finset.subset_union_right
    show ((towerOf L ω β (C₁ ⊔ (C₀ ⊔ C))
            (cornerEmbed L C₁ (C₁ ⊔ (C₀ ⊔ C)) Finset.subset_union_left b
              * cornerEmbed L (C₀ ⊔ C) (C₁ ⊔ (C₀ ⊔ C)) Finset.subset_union_right
                  (cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right v
                    * cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a))
          : TowerPre L ω β) : TowerGNS L ω β)
        = ((towerOf L ω β (C₀ ⊔ (C₁ ⊔ C))
            (cornerEmbed L (C₁ ⊔ C) (C₀ ⊔ (C₁ ⊔ C)) Finset.subset_union_right
                (cornerEmbed L C₁ (C₁ ⊔ C) Finset.subset_union_left b
                  * cornerEmbed L C (C₁ ⊔ C) Finset.subset_union_right v)
              * cornerEmbed L C₀ (C₀ ⊔ (C₁ ⊔ C)) Finset.subset_union_left a)
          : TowerPre L ω β) : TowerGNS L ω β)
    rw [← towerGerm L ω β hL, ← towerGerm L ω β hR]
    simp only [cornerEmbed_mul, cornerEmbed_trans, mul_assoc]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add]
    rw [towerCoe_add_raw, towerCoe_add_raw, h₁, h₂]

/-- **S5 — the CLM commutation**: the right multiplication commutes with EVERY represented
    stage operator — `π(b) · R_a = R_a · π(b)` on the tower Hilbert space (the completion
    incantation over the raw exchange). The right multiplications lie in the commutant of
    every stage algebra. -/
theorem towerRightMul_comm_towerRep (C₁ C₀ : Finset M) (b : DiamondAlg L C₁)
    (a : DiamondAlg L C₀) :
    towerRepCLM L ω β C₁ b * towerRightMulCLM L ω β C₀ a
      = towerRightMulCLM L ω β C₀ a * towerRepCLM L ω β C₁ b := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      towerRightMulCLM_coe, towerRepCLM_coe, towerRepCLM_coe, towerRightMulCLM_coe]
    exact towerCoe_leftMul_rightMul_exchange L ω β C₁ C₀ b a x

/-! ### S6 — pure bicommutant transport to the limit -/

/-- **S6 — the general bicommutant application**: an operator commuting with every element of
    the union of a directed family of ⋆-subalgebras commutes with the WHOLE limit von Neumann
    algebra — the limit is the double centralizer of the union (`generatedBy_coe_of_starClosed`),
    and `Set.centralizer` membership is DEFINITIONAL: `hT R hR` is the commutation. No
    SOT-approximation is needed. -/
theorem commute_of_mem_limitVN {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {ι : Type*} [Nonempty ι] {A : ι → StarSubalgebra ℂ (H →L[ℂ] H)}
    (hdir : Directed (· ≤ ·) A) {R T : H →L[ℂ] H}
    (hR : R ∈ Set.centralizer (⋃ i, (A i : Set (H →L[ℂ] H))))
    (hT : T ∈ QIQTH.VonNeumann.limitVN A hdir) : R * T = T * R := by
  have hstar : ∀ a ∈ (⋃ i, (A i : Set (H →L[ℂ] H))),
      star a ∈ ⋃ i, (A i : Set (H →L[ℂ] H)) := by
    intro a ha
    rw [Set.mem_iUnion] at ha ⊢
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, star_mem hi⟩
  have hcoe : (QIQTH.VonNeumann.limitVN A hdir : Set (H →L[ℂ] H))
      = Set.centralizer (Set.centralizer (⋃ i, (A i : Set (H →L[ℂ] H)))) :=
    QIQTH.VonNeumann.generatedBy_coe_of_starClosed hstar
  have hmem : T ∈ (QIQTH.VonNeumann.limitVN A hdir : Set (H →L[ℂ] H)) := hT
  rw [hcoe, Set.mem_centralizer_iff] at hmem
  exact hmem R hR

/-- **S6 — the right multiplications commute with the LIMIT**: `R_a` commutes with every
    element of the tower limit von Neumann algebra — S5 puts `R_a` in the centralizer of the
    union of the stages, and the bicommutant application transports the commutation to the
    whole limit, purely algebraically. -/
theorem towerRightMul_comm_limitVN (C₀ : Finset M) (a : DiamondAlg L C₀)
    {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β} (hT : T ∈ towerLimitVN L ω β) :
    towerRightMulCLM L ω β C₀ a * T = T * towerRightMulCLM L ω β C₀ a := by
  refine commute_of_mem_limitVN (towerStageAlg_mono L ω β).directed_le ?_ hT
  rw [Set.mem_centralizer_iff]
  intro m hm
  rw [Set.mem_iUnion] at hm
  obtain ⟨C₁, hm⟩ := hm
  obtain ⟨b, rfl⟩ := hm
  exact towerRightMul_comm_towerRep L ω β C₁ C₀ b a

/-! ### S7 — CAPSTONE: Ω is SEPARATING for the tower limit von Neumann algebra -/

/-- **S7 CAPSTONE — Ω IS SEPARATING FOR towerLimitVN**: an element of the tower limit von
    Neumann algebra vanishing on the cyclic vector is ZERO — `T(R_aΩ) = R_a(TΩ) = 0` on R8's
    orbit (the right action commutes with the limit, and the right orbit of Ω IS R8's orbit),
    and R8's density closes by `ContinuousLinearMap.ext_on`. Together with
    `dense_span_towerRep_cyclicVec` this is THE STANDARD-FORM HYPOTHESIS PAIR of
    Tomita–Takesaki theory — the hypothesis for that theory, not the theory: no S₀, no Δ,
    no J, no KMS at the limit, no type is claimed. -/
theorem towerCyclicVec_separating {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) (h0 : T (towerCyclicVec L ω β) = 0) : T = 0 := by
  refine ContinuousLinearMap.ext_on (dense_span_towerRep_cyclicVec L ω β) ?_
  rintro v ⟨C, a, rfl⟩
  have hRa : towerRep L ω β C a (towerCyclicVec L ω β)
      = towerRightMulCLM L ω β C a (towerCyclicVec L ω β) :=
    (towerRep_cyclicVec_of L ω β C a).trans (towerRightMul_cyclicVec L ω β C a).symm
  rw [hRa, ContinuousLinearMap.zero_apply, ← ContinuousLinearMap.mul_apply,
    ← towerRightMul_comm_limitVN L ω β C a hT, ContinuousLinearMap.mul_apply, h0,
    map_zero]

/-! ### S8 — Ω is cyclic for the LIMIT, and the vector determines the operator -/

/-- **S8 — Ω IS CYCLIC FOR towerLimitVN**: the span of the orbit of Ω under the LIMIT algebra
    is dense — the limit orbit contains R8's stage orbit (`towerRep_mem_towerLimitVN`), so
    R8's density transfers by monotonicity. -/
theorem dense_span_limitVN_orbit_cyclicVec :
    Dense (↑(Submodule.span ℂ {v : TowerGNS L ω β | ∃ T ∈ towerLimitVN L ω β,
        v = T (towerCyclicVec L ω β)}) : Set (TowerGNS L ω β)) := by
  have hsub : {v : TowerGNS L ω β | ∃ (C : Finset M) (a : DiamondAlg L C),
        v = towerRep L ω β C a (towerCyclicVec L ω β)}
      ⊆ {v : TowerGNS L ω β | ∃ T ∈ towerLimitVN L ω β,
        v = T (towerCyclicVec L ω β)} := by
    rintro v ⟨C, a, rfl⟩
    exact ⟨towerRep L ω β C a, towerRep_mem_towerLimitVN L ω β C a, rfl⟩
  exact (dense_span_towerRep_cyclicVec L ω β).mono
    (SetLike.coe_subset_coe.mpr (Submodule.span_mono hsub))

/-- **S8 — the cyclic vector determines the operator on the limit**: two elements of the
    tower limit von Neumann algebra agreeing on Ω are EQUAL — separation applied to `T − S`.
    (The well-definedness germ of a future Tomita `S₀`; `S₀` itself is NOT constructed.) -/
theorem towerLimitVN_eq_of_apply_cyclicVec {T S : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) (hS : S ∈ towerLimitVN L ω β)
    (h : T (towerCyclicVec L ω β) = S (towerCyclicVec L ω β)) : T = S := by
  have hTS : T - S ∈ towerLimitVN L ω β := sub_mem hT hS
  have h0 : (T - S) (towerCyclicVec L ω β) = 0 := by
    rw [ContinuousLinearMap.sub_apply, h, sub_self]
  exact sub_eq_zero.mp (towerCyclicVec_separating L ω β hTS h0)

end QIQTH.TowerGNS
