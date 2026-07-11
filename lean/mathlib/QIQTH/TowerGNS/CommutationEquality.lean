/-
  THE COMMUTATION EQUALITY — Tomita's theorem in full, J·M·J = M′, for the tower limit
  (duality campaign, brick D2a; closes LA1′'s Kaplansky gap).

  LA1′ (CommutationTheorem.lean) built the whole corridor: the finite-stage commutation
  theorem, `rightLimitVN` = J·M·J as a genuine von Neumann algebra with
  `rightLimitVN ⊆ M′`, and the orbit-level compression — every `T ∈ M′` is, pointwise on
  the cyclic orbit, the limit of the right multiplications `R_{b_C}` by the compressed
  symbols `b_C := commutantSymbol T C`. LA1′ then NAMED the remaining gap: the approximants'
  operator norms looked uncontrolled, because the held bound `‖R_b‖ ≤ √(rightFrobBound b)`
  is RATIO-weighted while the compression controls only the COLUMN-weighted GNS norm of
  `b_C` — inequivalent quadratic forms ("the Kaplansky gap").

  THE GAP WAS AN ARTIFACT OF THE WRONG ESTIMATE (consult-identified; classical
  Rieffel–van Daele/Takesaki content). The uniform operator-norm bound on `R_{b_C}` does
  NOT come from the GNS norm of the symbol at all — it comes from RIGHT-BOUNDEDNESS:

  1. BIMODULARITY (`starProjection_comm_towerRep`): the stage subspace `V_C` is invariant
     under the ⋆-closed stage algebra `π_C(M_C)`, so its orthogonal projection `P_C` lies
     in the commutant of the stage algebra (the C1 invariant-projection engine).
  2. THE RIGHT-BOUNDEDNESS ESTIMATE (`commutant_symbol_right_bounded`): for `T ∈ M′`,
       ‖π_C(a)(germ b_C)‖ = ‖π_C(a)(P_C(TΩ))‖ = ‖P_C(π_C(a)(TΩ))‖ [bimodularity]
         = ‖P_C(T(π_C(a)Ω))‖ [commutation] ≤ ‖T‖·‖π_C(a)Ω‖ [P contractive, T bounded].
  3. THE STAGE-NORM IDENTIFICATION (`rightMul_symbol_norm_le`): `‖R_{b_C}‖ ≤ ‖T‖`,
     GLOBALLY and UNIFORMLY IN C. The J-partner route: `R_{b_C} = J·π_C(jStage b_C)·J`
     (LA1′'s stage identity), the estimate of step 2 flips through the anti-unitary J into
     a left-multiplication bound for `c_C := jStage b_C`; a COLUMN-WITNESS in the stage GNS
     form (a matrix supported on one column — the Gibbs weight of the column CANCELS
     exactly) converts it into the Euclidean quadratic bound `‖c_C v‖ ≤ ‖T‖·‖v‖ for EVERY
     v (`mulVec_bound_of_germ_bound`), whence the matrix Loewner bound
     `‖T‖²·1 − c_Cᴴc_C ⪰ 0` (`colBound_posSemidef`) and, transported through the corner
     embeddings exactly as R5/R6 transported the Frobenius bound, the operator-norm bound
     `‖π_C(c_C)‖ ≤ ‖T‖` on the WHOLE tower Hilbert space (`towerRepCLM_opNorm_le`).
     (No auxiliary matrix norm is ever chosen: the column witness gives the quadratic
     bound at every vector directly, so no attainment/singular-vector argument is needed.)
  4. SOT CONVERGENCE (`commutant_sotApprox`): with the uniform bound, the orbit-level
     convergence of LA1′ upgrades to strong-operator approximation on arbitrary finite
     tuples (the ε/3 argument through the dense stage subspaces), hence
     `T ∈ rightLimitVN` (`commutant_mem_rightLimitVN`) — rightLimitVN is SOT-closed.
  5. ★★ THE CAPSTONES: `commutant_le_rightLimitVN` (M′ ⊆ J·M·J) and, with LA1′'s held
     Tomita II inclusion `rightLimitVN ⊆ M′`,
       `tomita_commutation_equality : rightLimitVN = M′`  —  i.e.  **J·M·J = M′**
     (`jconj_image_eq_commutant`), TOMITA'S COMMUTATION THEOREM IN FULL for the tower
     limit state. With the held Tomita I (Δ^{it}·M·Δ^{-it} = M), the S̄/Δ/J polar data,
     non-traciality and the KMS boundary condition, this completes the full
     Tomita–Takesaki commutation theorem for the tower limit — to our knowledge the first
     complete (both-halves) Tomita commutation theorem in any proof assistant.

  MANDATORY FIREWALL (binding): finite-stage Gibbs inductive limit only (an ITPFI-type
  tower). The TYPE CLASSIFICATION of the limit algebra (III₁, the S-invariant,
  Araki–Woods/Powers factors, Connes' classification) remains ABSENT — no type API exists
  anywhere in this development and none is claimed (Araki–Woods 1968 and Connes 1973 stay
  cited, never invoked). No strip-analyticity/KMS-analytic-continuation is used or claimed.
  The contractivity/column-witness lemmas are for THIS tower's product-Gibbs structure
  (faithful diagonal Gibbs states at every stage), not a general C*-norm theory. NOT the
  strong holographic principle, NOT quantum gravity. No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.TowerGNS.CommutationTheorem
import QIQTH.VonNeumann.InvariantProjection

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.VonNeumann
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### Step 1 — BIMODULARITY: the stage projection commutes with the stage algebra

    The stage subspace `V_C = germ(M_C)` is invariant under every represented stage
    operator `π_C(a)` (the germ absorbs left multiplication: `π_C(a)(germ x) = germ (a·x)`),
    and the stage algebra is ⋆-closed — so the C1 invariant-projection engine puts the
    orthogonal projection `P_C` in the commutant of the stage algebra. -/

/-- **The germ absorbs the stage action**: `π_C(a)(germ x) = germ (a·x)` — the stage
    subspace is invariant under its own represented algebra. Route: both germs are orbit
    vectors (`germ z = π_C(z) Ω`) and the representation is multiplicative. -/
theorem towerRep_stageGermL (C : Finset M) (a x : DiamondAlg L C) :
    towerRep L ω β C a (stageGermL L ω β C x) = stageGermL L ω β C (a * x) := by
  have hx : stageGermL L ω β C x = towerRep L ω β C x (towerCyclicVec L ω β) := by
    rw [stageGermL_apply]
    exact (towerRep_cyclicVec_of L ω β C x).symm
  have hax : stageGermL L ω β C (a * x)
      = towerRep L ω β C (a * x) (towerCyclicVec L ω β) := by
    rw [stageGermL_apply]
    exact (towerRep_cyclicVec_of L ω β C (a * x)).symm
  rw [hx, hax, map_mul, ContinuousLinearMap.mul_apply]

/-- The stage subspace `V_C` is invariant under the stage algebra `π_C(M_C)`. -/
theorem stageSubspace_invariant {C : Finset M}
    {S : TowerGNS L ω β →L[ℂ] TowerGNS L ω β} (hS : S ∈ towerStageAlg L ω β C)
    {v : TowerGNS L ω β} (hv : v ∈ stageSubspace L ω β C) :
    S v ∈ stageSubspace L ω β C := by
  obtain ⟨a, rfl⟩ := hS
  obtain ⟨x, rfl⟩ := (mem_stageSubspace_iff L ω β).mp hv
  exact (mem_stageSubspace_iff L ω β).mpr ⟨a * x, (towerRep_stageGermL L ω β C a x).symm⟩

/-- **BIMODULARITY — the stage projection commutes with the stage representation**:
    `π_C(a)·P_C = P_C·π_C(a)`. The stage subspace is invariant under the ⋆-CLOSED stage
    algebra, so the C1 invariant-projection engine (`starProjection_mem_centralizer`)
    puts `P_C` in its commutant. -/
theorem starProjection_comm_towerRep (C : Finset M) (a : DiamondAlg L C) :
    towerRep L ω β C a * (stageSubspace L ω β C).starProjection
      = (stageSubspace L ω β C).starProjection * towerRep L ω β C a := by
  have hcen : (stageSubspace L ω β C).starProjection
      ∈ Set.centralizer
        ((towerStageAlg L ω β C : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))) :=
    QIQTH.VonNeumann.starProjection_mem_centralizer (towerStageAlg L ω β C)
      fun _ hS x hx => stageSubspace_invariant L ω β hS hx
  exact Set.mem_centralizer_iff.mp hcen (towerRep L ω β C a)
    (SetLike.mem_coe.mpr ⟨a, rfl⟩)

/-- The pointwise form of bimodularity: `π_C(a)(P_C ξ) = P_C(π_C(a) ξ)`. -/
theorem starProjection_comm_towerRep_apply (C : Finset M) (a : DiamondAlg L C)
    (ξ : TowerGNS L ω β) :
    towerRep L ω β C a ((stageSubspace L ω β C).starProjection ξ)
      = (stageSubspace L ω β C).starProjection (towerRep L ω β C a ξ) := by
  have happ := congrArg
    (fun F : TowerGNS L ω β →L[ℂ] TowerGNS L ω β => F ξ)
    (starProjection_comm_towerRep L ω β C a)
  simpa only [ContinuousLinearMap.mul_apply] using happ

/-! ### Step 2 — THE RIGHT-BOUNDEDNESS ESTIMATE (the key)

    The estimate LA1′ was missing: the stage orbit of the COMPRESSED SYMBOL is dominated
    by `‖T‖` times the stage orbit of Ω — because the projection is bimodular and `T`
    commutes with the stage operators. The GNS norm of `b_C` never enters. -/

/-- **★ THE RIGHT-BOUNDEDNESS ESTIMATE**: for `T ∈ M′` and `b_C := commutantSymbol T C`,
    `‖π_C(a)(germ b_C)‖ ≤ ‖T‖·‖π_C(a) Ω‖` for EVERY `a` — chase
    `π_C(a)(P_C(TΩ)) = P_C(π_C(a)(TΩ)) = P_C(T(π_C(a)Ω))` (bimodularity, then commutation)
    and use that the projection is contractive and `T` is bounded. -/
theorem commutant_symbol_right_bounded {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ (towerLimitVN L ω β).commutant) (C : Finset M) (a : DiamondAlg L C) :
    ‖towerRep L ω β C a (stageGermL L ω β C (commutantSymbol L ω β T C))‖
      ≤ ‖T‖ * ‖towerRep L ω β C a (towerCyclicVec L ω β)‖ := by
  have hcommT : towerRep L ω β C a * T = T * towerRep L ω β C a :=
    VonNeumannAlgebra.mem_commutant_iff.mp hT (towerRep L ω β C a)
      (towerRep_mem_towerLimitVN L ω β C a)
  have hswap : towerRep L ω β C a (T (towerCyclicVec L ω β))
      = T (towerRep L ω β C a (towerCyclicVec L ω β)) := by
    rw [← ContinuousLinearMap.mul_apply, hcommT, ContinuousLinearMap.mul_apply]
  calc ‖towerRep L ω β C a (stageGermL L ω β C (commutantSymbol L ω β T C))‖
      = ‖(stageSubspace L ω β C).starProjection
          (T (towerRep L ω β C a (towerCyclicVec L ω β)))‖ := by
        rw [stageGerm_commutantSymbol, starProjection_comm_towerRep_apply, hswap]
    _ ≤ ‖T (towerRep L ω β C a (towerCyclicVec L ω β))‖ :=
        (stageSubspace L ω β C).norm_starProjection_apply_le _
    _ ≤ ‖T‖ * ‖towerRep L ω β C a (towerCyclicVec L ω β)‖ := T.le_opNorm _

/-- The germ form of the right-boundedness estimate:
    `‖germ (a·b_C)‖ ≤ ‖T‖·‖germ a‖` for every `a` — right multiplication by the compressed
    symbol is `‖T‖`-bounded on the whole stage subspace. -/
theorem commutant_symbol_germ_bounded {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ (towerLimitVN L ω β).commutant) (C : Finset M) (a : DiamondAlg L C) :
    ‖stageGermL L ω β C (a * commutantSymbol L ω β T C)‖
      ≤ ‖T‖ * ‖stageGermL L ω β C a‖ := by
  have h := commutant_symbol_right_bounded L ω β hT C a
  rwa [towerRep_stageGermL, towerRep_cyclicVec_of, ← stageGermL_apply] at h

/-! ### Step 3 — the contractivity toolkit

    From a stage-GNS quadratic bound to a GLOBAL operator-norm bound for the tower
    representation. The chain: column witness (the Gibbs weight cancels) → Euclidean
    quadratic bound → matrix Loewner bound `K²·1 − cᴴc ⪰ 0` → GNS bound at every deep
    stage (the R5 transport, with the Loewner hypothesis in place of the Frobenius bound)
    → pre-space norm bound → completion. -/

/-- **The column witness**: a stage-GNS quadratic bound for left multiplication by `c`
    forces the EUCLIDEAN quadratic bound `Σ‖(c·v)ₘ‖² ≤ K²·Σ‖vₘ‖²` for every vector `v` —
    test on the matrix supported on a single column `j` with entries `v`; the Gibbs weight
    `w_j` of the column multiplies BOTH sides of the GNS form and cancels exactly. -/
theorem mulVec_bound_of_germ_bound (C : Finset M) (c : DiamondAlg L C) (K : ℝ)
    (hgerm : ∀ y : DiamondAlg L C,
      RCLike.re (gnsInner L ω β C (c * y) (c * y))
        ≤ K ^ 2 * RCLike.re (gnsInner L ω β C y y))
    (v : Micro L C → ℂ) :
    (∑ m, ‖(c *ᵥ v) m‖ ^ 2) ≤ K ^ 2 * ∑ m, ‖v m‖ ^ 2 := by
  obtain ⟨j⟩ : Nonempty (Micro L C) := inferInstance
  have hcol : ∀ w : Micro L C → ℂ,
      (∑ n, gibbsWeight L C ω β n * ∑ m, Complex.normSq
          ((Matrix.of fun m n : Micro L C => if n = j then w m else 0) m n))
        = gibbsWeight L C ω β j * ∑ m, ‖w m‖ ^ 2 := by
    intro w
    rw [Finset.sum_eq_single j (fun n _ hn => by simp [Matrix.of_apply, hn])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp [Matrix.of_apply, Complex.normSq_eq_norm_sq]
  have hcy : c * (Matrix.of fun m n : Micro L C => if n = j then v m else 0)
      = Matrix.of fun m n : Micro L C => if n = j then (c *ᵥ v) m else 0 := by
    ext m n
    rw [Matrix.mul_apply]
    by_cases hn : n = j
    · subst hn
      simp [Matrix.of_apply, Matrix.mulVec, dotProduct]
    · simp [Matrix.of_apply, hn]
  have key := hgerm (Matrix.of fun m n : Micro L C => if n = j then v m else 0)
  rw [hcy, gnsInner_self_entrywise, gnsInner_self_entrywise] at key
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at key
  rw [hcol (c *ᵥ v), hcol v] at key
  have hw := gibbsWeight_pos L C ω β j
  have key2 : gibbsWeight L C ω β j * ∑ m, ‖(c *ᵥ v) m‖ ^ 2
      ≤ gibbsWeight L C ω β j * (K ^ 2 * ∑ m, ‖v m‖ ^ 2) := by
    calc gibbsWeight L C ω β j * ∑ m, ‖(c *ᵥ v) m‖ ^ 2
        ≤ K ^ 2 * (gibbsWeight L C ω β j * ∑ m, ‖v m‖ ^ 2) := key
      _ = gibbsWeight L C ω β j * (K ^ 2 * ∑ m, ‖v m‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left key2 hw

/-- **The Loewner bound from the quadratic bound**: `K²·1 − cᴴc ⪰ 0` when
    `Σ‖(c·v)ₘ‖² ≤ K²·Σ‖vₘ‖²` for every `v` — the frobBound recipe with the hypothesis in
    place of Cauchy–Schwarz (`star v ⬝ᵥ (cᴴc *ᵥ v) = ‖c·v‖²`, entrywise real reduction). -/
theorem colBound_posSemidef (C : Finset M) (c : DiamondAlg L C) (K : ℝ)
    (hv : ∀ v : Micro L C → ℂ,
      (∑ m, ‖(c *ᵥ v) m‖ ^ 2) ≤ K ^ 2 * ∑ m, ‖v m‖ ^ 2) :
    (((K ^ 2 : ℝ) : ℂ) • (1 : DiamondAlg L C) - cᴴ * c).PosSemidef := by
  have hsa : IsSelfAdjoint ((K ^ 2 : ℝ) : ℂ) := by
    rw [isSelfAdjoint_iff]
    exact Complex.conj_ofReal _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul hsa).sub (Matrix.isHermitian_conjTranspose_mul_self c))
    fun v => ?_
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star, star_dotProduct_self_eq,
    star_dotProduct_self_eq, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.zero_le_real, sub_nonneg]
  exact hv v

/-- **The GNS bound at every deep stage from the Loewner bound** (the R5 transport with a
    hypothesis in place of the Frobenius bound): if `B·1 − cᴴc ⪰ 0` at stage `C`, then
    `⟪ιc·x, ιc·x⟫_K ≤ B·⟪x, x⟫_K` at every stage `K ⊇ C` — PSD transport through the
    corner embedding + the Gibbs state's positivity on PSD sandwiches. -/
theorem gnsInner_leftMul_le_of (C K : Finset M) (h : C ⊆ K) (c : DiamondAlg L C) (B : ℝ)
    (hB : ((B : ℂ) • (1 : DiamondAlg L C) - cᴴ * c).PosSemidef)
    (x : DiamondAlg L K) :
    RCLike.re (gnsInner L ω β K (cornerEmbed L C K h c * x) (cornerEmbed L C K h c * x))
      ≤ B * RCLike.re (gnsInner L ω β K x x) := by
  have hgap : ((B : ℂ) • (1 : DiamondAlg L K)
      - cornerEmbed L C K h (cᴴ * c)).PosSemidef := by
    have h1 := cornerEmbed_posSemidef L h hB
    rwa [cornerEmbed_sub, cornerEmbed_smul, cornerEmbed_one] at h1
  have h0 := stateOf_posSemidef_nonneg L ω β K (hgap.conjTranspose_mul_mul_same x)
  have hkey : (cornerEmbed L C K h c * x)ᴴ * (cornerEmbed L C K h c * x)
      = xᴴ * cornerEmbed L C K h (cᴴ * c) * x := by
    rw [Matrix.conjTranspose_mul, cornerEmbed_mul, cornerEmbed_star]
    simp only [Matrix.mul_assoc]
  have hexpand : xᴴ * ((B : ℂ) • (1 : DiamondAlg L K)
        - cornerEmbed L C K h (cᴴ * c)) * x
      = (B : ℂ) • (xᴴ * x)
        - (cornerEmbed L C K h c * x)ᴴ * (cornerEmbed L C K h c * x) := by
    rw [hkey, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one]
  rw [hexpand] at h0
  rw [stateOf, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul] at h0
  have hre := (Complex.le_def.mp h0).1
  rw [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul] at hre
  rw [gnsInner_def, gnsInner_def, RCLike.re_to_complex, RCLike.re_to_complex]
  linarith

/-- The raw tower form of the conditional GNS bound (the R6 collapse, with the Loewner
    hypothesis): `re ⟪π₀(c)x, π₀(c)x⟫ ≤ B·re ⟪x, x⟫` at the raw direct sum. -/
theorem leftMulRaw_re_inner_le_of (C₀ : Finset M) (c : DiamondAlg L C₀) (B : ℝ)
    (hB : ((B : ℂ) • (1 : DiamondAlg L C₀) - cᴴ * c).PosSemidef)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    RCLike.re (rawInner L ω β (leftMulRaw L C₀ c x) (leftMulRaw L C₀ c x))
      ≤ B * RCLike.re (rawInner L ω β x x) := by
  classical
  set K : Finset M := (DFinsupp.support x).sup id with hK
  have hx : ∀ C, x C ≠ 0 → C ⊆ K := fun C hC =>
    Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hC)
  have hxK : ∀ C, x C ≠ 0 → C ⊆ C₀ ⊔ K := fun C hC =>
    (hx C hC).trans Finset.subset_union_right
  have hTx : leftMulRaw L C₀ c x
      = ∑ C ∈ DFinsupp.support x,
          DirectSum.of (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)
            (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left c
              * cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right (x C)) := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    rw [map_sum (leftMulRaw L C₀ c) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
    exact Finset.sum_congr rfl fun C _ => leftMulRaw_of L C₀ c C (x C)
  have hx' : ∀ C', (leftMulRaw L C₀ c x) C' ≠ 0 → C' ⊆ C₀ ⊔ K := by
    intro C' hC'
    by_contra hnot
    apply hC'
    rw [hTx]
    erw [DFinsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    refine DirectSum.of_eq_of_ne _ _ _ fun he => hnot ?_
    rw [he]
    exact Finset.union_subset_union_right (hx C (DFinsupp.mem_support_iff.mp hC))
  rw [rawInner_eq_collapse L ω β (C₀ ⊔ K) _ _ hx' hx',
    rawInner_eq_collapse L ω β (C₀ ⊔ K) x x hxK hxK,
    collapse_leftMul L C₀ c K x hx]
  exact gnsInner_leftMul_le_of L ω β C₀ (C₀ ⊔ K) Finset.subset_union_left c B hB
    (collapseRaw L (C₀ ⊔ K) x)

/-- The pre-space norm bound from the Loewner bound: `‖π₀(c) x‖ ≤ K·‖x‖`. -/
theorem towerLeftMul_norm_le_of (C : Finset M) (c : DiamondAlg L C) (K : ℝ) (hK : 0 ≤ K)
    (hPSD : (((K ^ 2 : ℝ) : ℂ) • (1 : DiamondAlg L C) - cᴴ * c).PosSemidef)
    (x : TowerPre L ω β) :
    ‖towerLeftMulₗ L ω β C c x‖ ≤ K * ‖x‖ := by
  have key := leftMulRaw_re_inner_le_of L ω β C c (K ^ 2) hPSD x
  have hsq : ‖towerLeftMulₗ L ω β C c x‖ ^ 2 ≤ K ^ 2 * ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (towerLeftMulₗ L ω β C c x),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) x]
    exact key
  calc ‖towerLeftMulₗ L ω β C c x‖
      = Real.sqrt (‖towerLeftMulₗ L ω β C c x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (K ^ 2 * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (K ^ 2) * Real.sqrt (‖x‖ ^ 2) := Real.sqrt_mul (sq_nonneg K) _
    _ = K * ‖x‖ := by rw [Real.sqrt_sq hK, Real.sqrt_sq (norm_nonneg _)]

/-- **The operator-norm bound for the tower representation from the Loewner bound**:
    `‖π_C(c)‖ ≤ K` on the WHOLE tower Hilbert space when `K²·1 − cᴴc ⪰ 0` — the dense
    pre-space bound extends to the completion by continuity. -/
theorem towerRepCLM_opNorm_le (C : Finset M) (c : DiamondAlg L C) (K : ℝ) (hK : 0 ≤ K)
    (hPSD : (((K ^ 2 : ℝ) : ℂ) • (1 : DiamondAlg L C) - cᴴ * c).PosSemidef) :
    ‖towerRepCLM L ω β C c‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun ξ => ?_
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih x =>
    rw [towerRepCLM_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact towerLeftMul_norm_le_of L ω β C c K hK hPSD x

/-- `jconj` does not increase the operator norm: `‖J·S·J‖ ≤ ‖S‖` (`towerJ` is isometric on
    both flanks; with involutivity this is in fact an equality — only `≤` is needed). -/
theorem jconj_opNorm_le (S : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    ‖jconj L ω β S‖ ≤ ‖S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun ξ => ?_
  rw [jconj_norm_apply]
  calc ‖S (towerJ L ω β ξ)‖ ≤ ‖S‖ * ‖towerJ L ω β ξ‖ := S.le_opNorm _
    _ = ‖S‖ * ‖ξ‖ := by rw [towerJ_norm]

/-! ### Step 3 assembled — THE UNIFORM NORM BOUND ON THE APPROXIMANTS

    `‖R_{b_C}‖ ≤ ‖T‖`, uniformly in the stage `C` — LA1′'s Kaplansky gap, closed. -/

/-- **★★ THE UNIFORM NORM BOUND — the Kaplansky gap closes**: for `T ∈ M′`, the right
    multiplication by the compressed symbol satisfies `‖R_{b_C}‖ ≤ ‖T‖`, GLOBALLY and
    UNIFORMLY IN `C`. Route: the right-boundedness estimate flips through the anti-unitary
    `J` into a left bound for the partner `c_C := jStage b_C` on the stage germs; the
    column witness turns it into the Euclidean bound `‖c_C v‖ ≤ ‖T‖·‖v‖`; the Loewner
    bound transports through every corner embedding to `‖π_C(c_C)‖ ≤ ‖T‖` on all of `H`;
    and `R_{b_C} = J·π_C(c_C)·J` with `J` isometric. -/
theorem rightMul_symbol_norm_le {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ (towerLimitVN L ω β).commutant) (C : Finset M) :
    ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)‖ ≤ ‖T‖ := by
  have hgermnorm : ∀ z : DiamondAlg L C,
      RCLike.re (gnsInner L ω β C z z) = ‖stageGermL L ω β C z‖ ^ 2 := by
    intro z
    rw [← stageGermL_inner]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  -- the J-flip: the right bound for b_C becomes a left bound for c_C = jStage b_C
  have hleft : ∀ y : DiamondAlg L C,
      ‖stageGermL L ω β C (jStage L ω β C (commutantSymbol L ω β T C) * y)‖
        ≤ ‖T‖ * ‖stageGermL L ω β C y‖ := by
    intro y
    have key := commutant_symbol_germ_bounded L ω β hT C (jStage L ω β C y)
    have hJ1 : towerJ L ω β
        (stageGermL L ω β C (jStage L ω β C y * commutantSymbol L ω β T C))
        = stageGermL L ω β C (jStage L ω β C (commutantSymbol L ω β T C) * y) := by
      rw [stageGermL_apply, stageGermL_apply, towerJ_of, jStage_anti_mul, jStage_involutive]
    have hJ2 : towerJ L ω β (stageGermL L ω β C y)
        = stageGermL L ω β C (jStage L ω β C y) := by
      rw [stageGermL_apply, stageGermL_apply, towerJ_of]
    calc ‖stageGermL L ω β C (jStage L ω β C (commutantSymbol L ω β T C) * y)‖
        = ‖towerJ L ω β (stageGermL L ω β C
            (jStage L ω β C y * commutantSymbol L ω β T C))‖ := by rw [hJ1]
      _ = ‖stageGermL L ω β C (jStage L ω β C y * commutantSymbol L ω β T C)‖ :=
          towerJ_norm L ω β _
      _ ≤ ‖T‖ * ‖stageGermL L ω β C (jStage L ω β C y)‖ := key
      _ = ‖T‖ * ‖towerJ L ω β (stageGermL L ω β C y)‖ := by rw [hJ2]
      _ = ‖T‖ * ‖stageGermL L ω β C y‖ := by rw [towerJ_norm]
  -- the stage-GNS quadratic bound for c_C
  have hgerm : ∀ y : DiamondAlg L C,
      RCLike.re (gnsInner L ω β C
          (jStage L ω β C (commutantSymbol L ω β T C) * y)
          (jStage L ω β C (commutantSymbol L ω β T C) * y))
        ≤ ‖T‖ ^ 2 * RCLike.re (gnsInner L ω β C y y) := by
    intro y
    rw [hgermnorm, hgermnorm]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hleft y) 2
    rwa [mul_pow] at h
  -- Loewner bound and the global representation bound
  have hPSD : (((‖T‖ ^ 2 : ℝ) : ℂ) • (1 : DiamondAlg L C)
      - (jStage L ω β C (commutantSymbol L ω β T C))ᴴ
        * jStage L ω β C (commutantSymbol L ω β T C)).PosSemidef :=
    colBound_posSemidef L C _ ‖T‖
      (fun v => mulVec_bound_of_germ_bound L ω β C _ ‖T‖ hgerm v)
  have hrep : ‖towerRepCLM L ω β C (jStage L ω β C (commutantSymbol L ω β T C))‖ ≤ ‖T‖ :=
    towerRepCLM_opNorm_le L ω β C _ ‖T‖ (norm_nonneg T) hPSD
  -- assemble through the J-partner identity
  rw [towerRightMulCLM_eq_jconj]
  refine le_trans (jconj_opNorm_le L ω β _) ?_
  rw [towerRep_apply]
  exact hrep

/-! ### Step 4 — SOT convergence with the uniform bound

    LA1′'s orbit-level convergence + the uniform norm bound + joint density of the stage
    subspaces = strong-operator approximation of `T` on ARBITRARY finite tuples by the
    right-multiplication generators — the ε/3 argument. -/

/-- **★ THE SOT APPROXIMATION**: every `T ∈ M′` is strong-operator approximable by the
    right-multiplication generators — for any finite tuple and ε, take a deep enough stage:
    the compressed-symbol approximant is ε-close on each tuple entry (approximate each
    entry by a germ; the middle term vanishes by LA1′'s orbit convergence; the two outer
    terms are controlled by `‖T‖` and — THE NEW INGREDIENT — the uniform bound
    `‖R_{b_C}‖ ≤ ‖T‖`). -/
theorem commutant_sotApprox {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ (towerLimitVN L ω β).commutant) :
    SOTApprox (rightStageSet L ω β) T := by
  intro n ξ ε hε
  have hT1 : (0 : ℝ) < ‖T‖ + 1 := by positivity
  set δ : ℝ := ε / (3 * (‖T‖ + 1)) with hδdef
  have hδ : 0 < δ := div_pos hε (by positivity)
  -- germ approximations of the tuple entries
  have hgerms : ∀ i : Fin n, ∃ (C₁ : Finset M) (a : DiamondAlg L C₁),
      ‖ξ i - stageGermL L ω β C₁ a‖ < δ := by
    intro i
    obtain ⟨y, hy, hdist⟩ := (dense_iUnion_stageSubspace L ω β).exists_dist_lt (ξ i) hδ
    obtain ⟨C₁, hyC⟩ := Set.mem_iUnion.mp hy
    obtain ⟨a, rfl⟩ := (mem_stageSubspace_iff L ω β).mp hyC
    exact ⟨C₁, a, by rwa [dist_eq_norm] at hdist⟩
  choose Cv av hav using hgerms
  -- the middle terms are eventually small, uniformly over the finite tuple
  have hmid : ∀ᶠ C : Finset M in Filter.atTop, ∀ i : Fin n,
      ‖T (stageGermL L ω β (Cv i) (av i))
          - towerRightMulCLM L ω β C (commutantSymbol L ω β T C)
              (stageGermL L ω β (Cv i) (av i))‖ < ε / 3 := by
    refine Filter.eventually_all.mpr fun i => ?_
    exact (commutant_orbit_tendsto L ω β hT (Cv i) (av i)).eventually_lt_const
      (div_pos hε (by norm_num))
  obtain ⟨C, hC⟩ := hmid.exists
  refine ⟨towerRightMulCLM L ω β C (commutantSymbol L ω β T C),
    (mem_rightStageSet_iff L ω β).mpr ⟨C, commutantSymbol L ω β T C, rfl⟩, fun i => ?_⟩
  have hRnorm : ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)‖ ≤ ‖T‖ :=
    rightMul_symbol_norm_le L ω β hT C
  -- ‖T‖·δ ≤ ε/3
  have hεδ : δ * (3 * (‖T‖ + 1)) = ε := by
    rw [hδdef]
    exact div_mul_cancel₀ ε (by positivity)
  have hδT : ‖T‖ * δ ≤ ε / 3 := by
    nlinarith [hδ.le, norm_nonneg T]
  -- the outer terms
  have h1 : ‖T (ξ i) - T (stageGermL L ω β (Cv i) (av i))‖ ≤ ε / 3 := by
    rw [← map_sub]
    calc ‖T (ξ i - stageGermL L ω β (Cv i) (av i))‖
        ≤ ‖T‖ * ‖ξ i - stageGermL L ω β (Cv i) (av i)‖ := T.le_opNorm _
      _ ≤ ‖T‖ * δ := by
          have := (hav i).le
          gcongr
      _ ≤ ε / 3 := hδT
  have h3 : ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)
        (stageGermL L ω β (Cv i) (av i))
      - towerRightMulCLM L ω β C (commutantSymbol L ω β T C) (ξ i)‖ ≤ ε / 3 := by
    rw [← map_sub]
    calc ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)
          (stageGermL L ω β (Cv i) (av i) - ξ i)‖
        ≤ ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)‖
            * ‖stageGermL L ω β (Cv i) (av i) - ξ i‖ :=
          (towerRightMulCLM L ω β C (commutantSymbol L ω β T C)).le_opNorm _
      _ ≤ ‖T‖ * δ := by
          rw [norm_sub_rev]
          exact mul_le_mul hRnorm (hav i).le (norm_nonneg _) (norm_nonneg T)
      _ ≤ ε / 3 := hδT
  have h2 := hC i
  calc ‖T (ξ i) - towerRightMulCLM L ω β C (commutantSymbol L ω β T C) (ξ i)‖
      ≤ ‖T (ξ i) - T (stageGermL L ω β (Cv i) (av i))‖
        + ‖T (stageGermL L ω β (Cv i) (av i))
            - towerRightMulCLM L ω β C (commutantSymbol L ω β T C) (ξ i)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖T (ξ i) - T (stageGermL L ω β (Cv i) (av i))‖
        + (‖T (stageGermL L ω β (Cv i) (av i))
            - towerRightMulCLM L ω β C (commutantSymbol L ω β T C)
                (stageGermL L ω β (Cv i) (av i))‖
          + ‖towerRightMulCLM L ω β C (commutantSymbol L ω β T C)
                (stageGermL L ω β (Cv i) (av i))
              - towerRightMulCLM L ω β C (commutantSymbol L ω β T C) (ξ i)‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

/-- **★★ THE MEMBERSHIP — `M′ ⊆ rightLimitVN` pointwise**: every element of the commutant
    of the tower limit von Neumann algebra lies in the right-multiplication limit von
    Neumann algebra — `rightLimitVN` is the SOT closure of the ⋆-algebra of the right
    generators, and `commutant_sotApprox` provides the approximation. -/
theorem commutant_mem_rightLimitVN {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ (towerLimitVN L ω β).commutant) : T ∈ rightLimitVN L ω β := by
  have hR : SOTApprox
      ((StarAlgebra.adjoin ℂ (rightStageSet L ω β)
          : StarSubalgebra ℂ (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
        : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) T :=
    (commutant_sotApprox L ω β hT).mono (StarAlgebra.subset_adjoin ℂ _)
  have hmem : T ∈ (QIQTH.VonNeumann.generatedBy (rightStageSet L ω β)
      : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) := by
    rw [QIQTH.VonNeumann.generatedBy_carrier_eq]
    exact hR
  exact hmem

/-! ### Step 5 — ★★ THE CAPSTONES: the full commutation theorem -/

/-- **★★ THE HARD-HALF INCLUSION — `M′ ⊆ J·M·J`**: the commutant of the tower limit von
    Neumann algebra is contained in `rightLimitVN = J·M·J` (LA1′'s image identity). This
    is the reverse inclusion LA1′ named as the wall — Tomita's hard half. -/
theorem commutant_le_rightLimitVN :
    ((towerLimitVN L ω β).commutant : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
      ⊆ (rightLimitVN L ω β : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) := by
  intro T hT
  exact commutant_mem_rightLimitVN L ω β hT

/-- **★★★ THE COMMUTATION EQUALITY — TOMITA'S THEOREM, FULL**:
    `rightLimitVN = (towerLimitVN)′` as von Neumann algebras — both inclusions: LA1′'s
    Tomita II (`rightLimitVN_le_commutant`) and the new hard half
    (`commutant_le_rightLimitVN`). With LA1′'s image identity `J·M·J = rightLimitVN` this
    IS `J·M·J = M′` — the full Tomita commutation theorem for the tower limit state. -/
theorem tomita_commutation_equality :
    rightLimitVN L ω β = (towerLimitVN L ω β).commutant :=
  SetLike.coe_injective (Set.Subset.antisymm (rightLimitVN_le_commutant L ω β)
    (commutant_le_rightLimitVN L ω β))

/-- **★★★ `J·M·J = M′` AS SETS** — the headline form: the `jconj`-image of the tower limit
    von Neumann algebra IS its commutant. -/
theorem jconj_image_eq_commutant :
    jconj L ω β '' (towerLimitVN L ω β : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))
      = ((towerLimitVN L ω β).commutant
          : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) := by
  rw [jconj_image_towerLimitVN, tomita_commutation_equality]

/-- The membership form of the commutation equality. -/
theorem mem_commutant_iff_mem_rightLimitVN {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β} :
    T ∈ (towerLimitVN L ω β).commutant ↔ T ∈ rightLimitVN L ω β := by
  rw [tomita_commutation_equality]

/-- **Sanity: `(rightLimitVN)′ = M`** — the commutant of the right-multiplication algebra
    is the tower limit algebra (the commutation equality + `M″ = M`), the standard-form
    duality closed both ways. -/
theorem rightLimitVN_commutant_eq :
    (rightLimitVN L ω β).commutant = towerLimitVN L ω β := by
  rw [tomita_commutation_equality, VonNeumannAlgebra.commutant_commutant]

/-- **Ω IS CYCLIC FOR `M′`** — the corollary TomitaSecondHalf deferred, now free: the
    commutant IS `rightLimitVN`, for which Ω was already cyclic (LA1′). Together with Ω
    separating for `M′` (J8) this is the full standard-form symmetry: Ω is cyclic and
    separating for BOTH `M` and `M′`. -/
theorem dense_span_commutant_orbit_cyclicVec :
    Dense (↑(Submodule.span ℂ {v : TowerGNS L ω β | ∃ T ∈ (towerLimitVN L ω β).commutant,
        v = T (towerCyclicVec L ω β)}) : Set (TowerGNS L ω β)) := by
  rw [← tomita_commutation_equality]
  exact dense_span_rightLimitVN_orbit_cyclicVec L ω β

end QIQTH.TowerGNS
