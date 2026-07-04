/-
  G1 + G2 (THE_GENERATOR_PLAN.md) — THE SELF-ADJOINT STONE GENERATOR OF THE TRANSPORTED
  TOWER FLOW, AND THE CYCLIC VECTOR AS A ZERO-MODE.

  `towerGen := stoneGen (towerFlow)` — the general Stone-generator theorem
  (`QIQTH/Spectral/Stone.lean`, `QIQTH/Spectral/Garding.lean`) instantiated with the five
  held Track-B facts about the transported flow: the group law (`towerFlow_comp`, oriented
  here as the NAMED adapter `towerFlow_compL`), `U_0 = 1` (`towerFlow_zero`), unitarity
  (`towerFlow_inner`), the isometry bound (`towerFlow_norm_eq`), and strong continuity
  (`continuous_towerFlow_apply`). The result: `towerGen` is a genuine SELF-ADJOINT unbounded
  operator (`LinearPMap`, `K = K†` in Mathlib's adjoint sense) — `towerGen_isSelfAdjoint`.

  G2: the cyclic vector is a ZERO-MODE — the flow fixes Ω exactly (`towerFlow_cyclicVec`),
  so its orbit is constant, hence Ω lies in the smooth domain
  (`towerCyclicVec_mem_stoneDomain`) and `towerGen Ω = 0` (`towerGen_cyclicVec`), pinned by
  `stoneGen_eq_of_hasDerivAt`.

  HONEST SCOPE (binding): `towerGen` is the Stone generator of the TRANSPORTED flow — not
  constructed from the limit state's Tomita operator; NOT claimed to be a modular
  Hamiltonian in the Tomita sense. No Δ, J, S, separating property, KMS-at-the-limit, von
  Neumann type, spectral resolution (PVM) of the unbounded `towerGen`, or exponential
  recovery `U_t = exp(it·towerGen)` is claimed anywhere in this file.
-/
import Mathlib
import QIQTH.TowerGNS.FlowContinuity
import QIQTH.Spectral.Stone
import QIQTH.Spectral.Garding

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.Spectral
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### G1 — the named orientation adapter, the generator, self-adjointness -/

/-- **The group law in `∘L` form**: `U_{s+t} = U_s ∘L U_t` — the Stone `hgrp` hypothesis.
    The NAMED orientation adapter (never inlined): the held `towerFlow_comp` is stated as
    `U_t ∘L U_s = U_{t+s}`, so the Stone shape is its `symm` at the right instantiation. -/
theorem towerFlow_compL (s t : ℝ) :
    towerFlow L ω β (s + t) = towerFlow L ω β s ∘L towerFlow L ω β t :=
  (towerFlow_comp L ω β s t).symm

/-- **★ THE TOWER GENERATOR** — the Stone generator of the TRANSPORTED flow — not
    constructed from the limit state's Tomita operator; NOT claimed to be a modular
    Hamiltonian in the Tomita sense. -/
noncomputable def towerGen : (TowerGNS L ω β) →ₗ.[ℂ] (TowerGNS L ω β) :=
  QIQTH.Spectral.stoneGen (towerFlow L ω β)

/-- **★★★ The tower generator is SELF-ADJOINT**: `IsSelfAdjoint (towerGen L ω β)` — the
    general `stoneGen_isSelfAdjoint` instantiated with the five held Track-B facts (group
    law via the named adapter `towerFlow_compL`, `U_0 = 1`, unitarity, the isometry bound,
    strong continuity). So `towerGen` is a genuine self-adjoint unbounded operator
    (`K = K†` in Mathlib's `LinearPMap` adjoint sense) — obtained by TRANSPORT; no Tomita
    object of the limit state is used or claimed. -/
theorem towerGen_isSelfAdjoint : IsSelfAdjoint (towerGen L ω β) :=
  stoneGen_isSelfAdjoint (towerFlow L ω β) (towerFlow_compL L ω β) (towerFlow_zero L ω β)
    (fun t a b => towerFlow_inner L ω β t a b)
    (fun t y => le_of_eq (towerFlow_norm_eq L ω β t y))
    (fun y => continuous_towerFlow_apply L ω β y)

/-! ### G2 — the cyclic vector is a zero-mode -/

/-- **The cyclic vector lies in the smooth domain**: the flow fixes Ω exactly
    (`towerFlow_cyclicVec`), so the orbit `t ↦ U_t Ω` is the CONSTANT function, hence
    differentiable at `0`. -/
theorem towerCyclicVec_mem_stoneDomain :
    towerCyclicVec L ω β ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β) := by
  show DifferentiableAt ℝ (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β)) 0
  have h : (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β))
      = fun _ => towerCyclicVec L ω β :=
    funext fun t => towerFlow_cyclicVec L ω β t
  rw [h]
  exact differentiableAt_const _

/-- **★ THE ZERO-MODE**: `towerGen Ω = 0` — the orbit of the cyclic vector is constant, so
    its derivative at `0` is `0 = I • 0`, and `stoneGen_eq_of_hasDerivAt` pins the
    generator's value. (Transport, not Tomita: no Δ, J, S, or separating property is
    claimed.) -/
theorem towerGen_cyclicVec :
    towerGen L ω β ⟨towerCyclicVec L ω β, towerCyclicVec_mem_stoneDomain L ω β⟩ = 0 := by
  refine stoneGen_eq_of_hasDerivAt (towerFlow L ω β) (towerCyclicVec L ω β) 0
    (towerCyclicVec_mem_stoneDomain L ω β) ?_
  have h : (fun t : ℝ => towerFlow L ω β t (towerCyclicVec L ω β))
      = fun _ => towerCyclicVec L ω β :=
    funext fun t => towerFlow_cyclicVec L ω β t
  rw [h, smul_zero]
  exact hasDerivAt_const 0 _

/-! ### G3 — THE EXPLICIT CORE: the generator COMPUTED, not just certified, on a
constructively dense core

The transported flow acts on a pure component entrywise as fixed `Complex.exp` phases
(`cornerFlow_entry`), so the orbit of a coerced pure component is a FINITE sum of scalar
phase orbits — differentiable by hand. The derivative at `0` is `I •` the coerced image of
the EXPLICIT matrix `cornerGenMatrix C a` (entrywise `(log w_n − log w_m) · a n m` = the
diagonal-log commutator), so `stoneGen_eq_of_hasDerivAt` pins `towerGen` COMPUTED on every
coerced pure component (`towerGen_of`); raw finite support extends smooth-domain membership
to every coerced pre-vector (`coe_pre_mem_stoneDomain`), and density of the pre-space in the
completion makes the smooth domain DENSE (`dense_stoneDomain`).

LEAN ARCHITECTURE (the R3 lesson, binding): the orbit decomposition lives at the RAW `⨁`
type (the synonym is crossed in application position only); ONE isolated phase-derivative
lemma (`hasDerivAt_expPhase`); all action facts route through `stoneGen_eq_of_hasDerivAt`. -/

/-- **The isolated phase derivative**: `t ↦ exp(i·t·κ) • v` has derivative `(i·κ) • v` at
    `t = 0` — the ONE analytic input of G3 (chain rule through `Complex.exp` on the real
    line, then `smul_const`). -/
theorem hasDerivAt_expPhase (κ : ℝ) (v : TowerGNS L ω β) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * t * κ) • v) ((Complex.I * κ) • v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * (κ : ℂ))
      (Complex.I * (κ : ℂ)) 0 := by
    simpa using (h1.const_mul Complex.I).mul_const (κ : ℂ)
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ) * (κ : ℂ)))
      (Complex.I * (κ : ℂ)) 0 := by
    simpa using h2.cexp
  exact h3.smul_const v

/-- **The explicit corner generator matrix**: entrywise multiplication by the Gibbs
    log-weight difference — `(cornerGenMatrix C a) n m = (log w_n − log w_m) · a n m`.
    This is the finite-stage modular Hamiltonian ACTION in adjoint (commutator) form; see
    `cornerGenMatrix_eq_commutator`. -/
noncomputable def cornerGenMatrix (C : Finset M) (a : DiamondAlg L C) : DiamondAlg L C :=
  Matrix.of fun n m =>
    ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ) * a n m

/-- **The explicit generator matrix is the diagonal-log commutator**:
    `cornerGenMatrix C a = [diag(log w), a]` — the entrywise phase-rate matrix is exactly
    `ad_{diag(log w)}`. -/
theorem cornerGenMatrix_eq_commutator (C : Finset M) (a : DiamondAlg L C) :
    cornerGenMatrix L ω β C a
      = Matrix.diagonal (fun n => ((Real.log (gibbsWeight L C ω β n) : ℝ) : ℂ)) * a
        - a * Matrix.diagonal (fun n => ((Real.log (gibbsWeight L C ω β n) : ℝ) : ℂ)) := by
  ext n m
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  show ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ)
      * a n m = _
  push_cast
  ring

/-- The flow acts on a single-entry matrix as a PURE PHASE (entrywise from the held
    `cornerFlow_entry`): `σ_t (E_{nm} c) = exp(i·t·(log w_n − log w_m)) • E_{nm} c`. -/
theorem cornerFlow_single (C : Finset M) (t : ℝ) (n m : Micro L C) (c : ℂ) :
    cornerFlow L ω β C t (Matrix.single n m c)
      = Complex.exp (Complex.I * t
          * ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
        • Matrix.single n m c := by
  ext p q
  rw [Matrix.smul_apply, cornerFlow_entry]
  by_cases h : n = p ∧ m = q
  · obtain ⟨rfl, rfl⟩ := h
    rw [smul_eq_mul]
  · rw [Matrix.single_apply_of_ne n m c p q h, mul_zero, smul_zero]

/-- **The matrix-level orbit decomposition**: the flowed corner element is the finite sum of
    its phase-rotated single-entry components. -/
theorem cornerFlow_eq_sum_single (C : Finset M) (t : ℝ) (a : DiamondAlg L C) :
    cornerFlow L ω β C t a
      = ∑ n : Micro L C, ∑ m : Micro L C,
          Complex.exp (Complex.I * t * ((Real.log (gibbsWeight L C ω β n)
              - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
            • Matrix.single n m (a n m) := by
  have hl : ∀ x : DiamondAlg L C, cornerFlow L ω β C t x = cornerFlowₗ L ω β C t x :=
    fun _ => rfl
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  rw [hl, map_sum (cornerFlowₗ L ω β C t)
    (fun n => ∑ m : Micro L C, Matrix.single n m (a n m)) Finset.univ]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sum (cornerFlowₗ L ω β C t) (fun m => Matrix.single n m (a n m)) Finset.univ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← hl]
  exact cornerFlow_single L ω β C t n m (a n m)

/-- The explicit generator matrix as the weighted sum of single-entry components (the
    derivative-side counterpart of `cornerFlow_eq_sum_single`). -/
theorem cornerGenMatrix_eq_sum_single (C : Finset M) (a : DiamondAlg L C) :
    cornerGenMatrix L ω β C a
      = ∑ n : Micro L C, ∑ m : Micro L C,
          ((Real.log (gibbsWeight L C ω β n) - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ)
            • Matrix.single n m (a n m) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (cornerGenMatrix L ω β C a)]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.smul_single, smul_eq_mul]
  rfl

/-- Raw: the component inclusion commutes with weighted single-entry sums (`lof` linearity,
    crossed back to `of`). -/
theorem of_sum_single_smul (C : Finset M) (a : DiamondAlg L C)
    (c : Micro L C → Micro L C → ℂ) :
    DirectSum.of (fun C : Finset M => DiamondAlg L C) C
        (∑ n : Micro L C, ∑ m : Micro L C, c n m • Matrix.single n m (a n m))
      = ∑ n : Micro L C, ∑ m : Micro L C,
          c n m • DirectSum.of (fun C : Finset M => DiamondAlg L C) C
            (Matrix.single n m (a n m)) := by
  rw [map_sum (DirectSum.of (fun C : Finset M => DiamondAlg L C) C)
    (fun n => ∑ m : Micro L C, c n m • Matrix.single n m (a n m)) Finset.univ]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sum (DirectSum.of (fun C : Finset M => DiamondAlg L C) C)
    (fun m => c n m • Matrix.single n m (a n m)) Finset.univ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← DirectSum.lof_eq_of ℂ, map_smul, DirectSum.lof_eq_of]

/-- The coercion into the completion is FINITELY additive on raw vectors (induction on the
    index set through `towerCoe_add_raw`). -/
theorem towerCoe_sum_raw {ι : Type*} (s : Finset ι)
    (f : ι → ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β ((∑ i ∈ s, f i : ⨁ C : Finset M, DiamondAlg L C))
      = ∑ i ∈ s, towerCoe L ω β (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact UniformSpace.Completion.coe_zero (α := TowerPre L ω β)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact towerCoe_add_raw L ω β (f i) (∑ x ∈ s, f x)

/-- **The coerced orbit decomposition workhorse**: the coerced pure component of a weighted
    single-entry sum is the corresponding weighted sum of coerced pure components. -/
theorem towerOf_sum_single_smul_coe (C : Finset M) (a : DiamondAlg L C)
    (c : Micro L C → Micro L C → ℂ) :
    ((towerOf L ω β C (∑ n : Micro L C, ∑ m : Micro L C,
        c n m • Matrix.single n m (a n m)) : TowerPre L ω β) : TowerGNS L ω β)
      = ∑ n : Micro L C, ∑ m : Micro L C,
          c n m • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  show towerCoe L ω β (DirectSum.of (fun C : Finset M => DiamondAlg L C) C
      (∑ n : Micro L C, ∑ m : Micro L C, c n m • Matrix.single n m (a n m))) = _
  rw [of_sum_single_smul L C a c, towerCoe_sum_raw]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [towerCoe_sum_raw]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact towerCoe_smul_raw L ω β (c n m) _

/-- **The orbit of a coerced pure component is differentiable with EXPLICIT derivative**:
    `d/dt U_t ↑(of C a) |₀ = i • ↑(of C (cornerGenMatrix C a))` — the orbit is a FINITE sum
    of scalar phase orbits (`cornerFlow_eq_sum_single` pushed through `of` and the
    coercion), each differentiable by the isolated `hasDerivAt_expPhase`. -/
theorem hasDerivAt_towerFlow_of (C : Finset M) (a : DiamondAlg L C) :
    HasDerivAt (fun t : ℝ => towerFlow L ω β t
        ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β))
      (Complex.I • ((towerOf L ω β C (cornerGenMatrix L ω β C a) : TowerPre L ω β) :
        TowerGNS L ω β)) 0 := by
  classical
  have horbit : (fun t : ℝ => towerFlow L ω β t
        ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β))
      = fun t : ℝ => ∑ n : Micro L C, ∑ m : Micro L C,
          Complex.exp (Complex.I * t * ((Real.log (gibbsWeight L C ω β n)
              - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
            • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
                TowerGNS L ω β) := by
    funext t
    rw [towerFlow_coe]
    have h1 : flowPre L ω β t (towerOf L ω β C a)
        = towerOf L ω β C (cornerFlow L ω β C t a) := flowRaw_of L ω β t C a
    rw [h1]
    conv_lhs => rw [cornerFlow_eq_sum_single L ω β C t a]
    exact towerOf_sum_single_smul_coe L ω β C a _
  have hderiv : (∑ n : Micro L C, ∑ m : Micro L C,
        (Complex.I * ((Real.log (gibbsWeight L C ω β n)
            - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
          • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
              TowerGNS L ω β))
      = Complex.I • ((towerOf L ω β C (cornerGenMatrix L ω β C a) : TowerPre L ω β) :
          TowerGNS L ω β) := by
    have h1 : ((towerOf L ω β C (cornerGenMatrix L ω β C a) : TowerPre L ω β) :
          TowerGNS L ω β)
        = ∑ n : Micro L C, ∑ m : Micro L C,
            ((Real.log (gibbsWeight L C ω β n)
                - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ)
              • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
                  TowerGNS L ω β) := by
      conv_lhs => rw [cornerGenMatrix_eq_sum_single L ω β C a]
      exact towerOf_sum_single_smul_coe L ω β C a _
    rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact mul_smul Complex.I _ _
  rw [horbit, ← hderiv]
  apply HasDerivAt.fun_sum
  intro n _
  apply HasDerivAt.fun_sum
  intro m _
  exact hasDerivAt_expPhase L ω β _ _

/-- **Every coerced pure component lies in the smooth domain** (its orbit has an explicit
    derivative at `0`). -/
theorem towerOf_mem_stoneDomain (C : Finset M) (a : DiamondAlg L C) :
    ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β) := by
  show DifferentiableAt ℝ (fun t : ℝ => towerFlow L ω β t
    ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)) 0
  exact (hasDerivAt_towerFlow_of L ω β C a).differentiableAt

/-- **★★ G3 CAPSTONE — THE GENERATOR COMPUTED**: on every coerced pure component,
    `towerGen ↑(of C a) = ↑(of C (cornerGenMatrix C a))` — the abstract Stone generator of
    the transported flow acts as the EXPLICIT Gibbs log-weight commutator
    `a ↦ [diag(log w), a]` (`cornerGenMatrix_eq_commutator`), pinned by
    `stoneGen_eq_of_hasDerivAt`. (Transport, not Tomita: no Δ, J, S, or separating property
    is claimed.) -/
theorem towerGen_of (C : Finset M) (a : DiamondAlg L C) :
    towerGen L ω β ⟨((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
        towerOf_mem_stoneDomain L ω β C a⟩
      = ((towerOf L ω β C (cornerGenMatrix L ω β C a) : TowerPre L ω β) : TowerGNS L ω β) :=
  stoneGen_eq_of_hasDerivAt (towerFlow L ω β) _ _ (towerOf_mem_stoneDomain L ω β C a)
    (hasDerivAt_towerFlow_of L ω β C a)

/-- **Every coerced pre-vector lies in the smooth domain**: finite raw support decomposes it
    into pure components (`DirectSum.sum_support_of`), and the smooth domain is a submodule. -/
theorem coe_pre_mem_stoneDomain (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β x ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β) := by
  classical
  have hx : towerCoe L ω β x
      = ∑ C ∈ DFinsupp.support x,
          towerCoe L ω β (DirectSum.of (fun C : Finset M => DiamondAlg L C) C (x C)) := by
    conv_lhs => rw [show x = ∑ C ∈ DFinsupp.support x,
        DirectSum.of (fun C : Finset M => DiamondAlg L C) C (x C) from
      (DirectSum.sum_support_of x).symm]
    exact towerCoe_sum_raw L ω β _ _
  rw [hx]
  exact Submodule.sum_mem _ fun C _ => towerOf_mem_stoneDomain L ω β C (x C)

/-- **★ G3 — THE SMOOTH DOMAIN IS DENSE**: every coerced pre-vector is in the domain and the
    pre-space is dense in the completion — `towerGen` is computed (`towerGen_of`) on a
    CONSTRUCTIVELY DENSE core. -/
theorem dense_stoneDomain :
    Dense ((QIQTH.Spectral.stoneDomain (towerFlow L ω β) : Set (TowerGNS L ω β))) := by
  refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
  rintro ξ ⟨x, rfl⟩
  exact coe_pre_mem_stoneDomain L ω β x

/-! ### G4 — flow covariance of the generator

Both facts are free by instantiation of the general Stone theorems
(`stoneDomain_apply_mem`, `stoneGen_comm_flow`) with the transported flow and the named
group-law adapter `towerFlow_compL`. (Transport, not Tomita: no Δ, J, S, or separating
property is claimed.) -/

/-- **The flow preserves the smooth domain**: `U_s ξ ∈ stoneDomain` whenever
    `ξ ∈ stoneDomain` — `stoneDomain_apply_mem` instantiated with `towerFlow` and the group
    law `towerFlow_compL`. -/
theorem towerGen_domain_flow_mem (s : ℝ) {ξ : TowerGNS L ω β}
    (hξ : ξ ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β)) :
    towerFlow L ω β s ξ ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β) :=
  QIQTH.Spectral.stoneDomain_apply_mem (towerFlow L ω β) (towerFlow_compL L ω β) s ξ hξ

/-- **★★ G4 CAPSTONE — THE GENERATOR COMMUTES WITH THE FLOW**:
    `towerGen (U_s ξ) = U_s (towerGen ξ)` on the smooth domain, i.e. `[towerGen, U_s] = 0` —
    `stoneGen_comm_flow` instantiated with `towerFlow` and `towerFlow_compL`. The
    `U`-invariance of the generator: the transported flow's clock energy is compatible with
    the flow it is read off from. -/
theorem towerGen_comm_towerFlow (s : ℝ) {ξ : TowerGNS L ω β}
    (hξ : ξ ∈ QIQTH.Spectral.stoneDomain (towerFlow L ω β)) :
    towerGen L ω β ⟨towerFlow L ω β s ξ, towerGen_domain_flow_mem L ω β s hξ⟩
      = towerFlow L ω β s (towerGen L ω β ⟨ξ, hξ⟩) :=
  QIQTH.Spectral.stoneGen_comm_flow (towerFlow L ω β) (towerFlow_compL L ω β) s ⟨ξ, hξ⟩

end QIQTH.TowerGNS
