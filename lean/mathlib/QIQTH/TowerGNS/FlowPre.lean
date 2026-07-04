/-
  B1 (THE_TRANSPORT_AND_ACCOUNTING_PLAN.md) — the per-corner Gibbs modular flow's
  ⋆-automorphism + state-invariance laws, all through the rescale bridge.

  `cornerFlow C t = σ_t^{ρ_β}` (the diagonal modular flow at the Gibbs weights) is handled
  EXCLUSIVELY through the held KMS bridge `sigmaDiag_gibbs_eq_alpha_rescale`
  (`σ_t^{ρ_β} = α_{−βt}`) and the held `alpha` laws — no `Complex.cpow` and no `diagPow`
  entry computation appears anywhere in this file. Proved: the flow is a unital
  ⋆-automorphism at every `t` (`cornerFlow_one/_mul/_star/_add/_smul`), a real
  one-parameter group (`cornerFlow_zero`, `cornerFlow_comp`), state-preserving
  (`stateOf_cornerFlow` via `gibbs_stationary`), GNS-inner-product-preserving
  (`gnsInner_cornerFlow` — the capstone: the flow is a pre-unitary on every stage), and
  tower-equivariant (`cornerFlow_cornerEmbed` via T7's `cornerEmbed_sigmaDiag`).
-/
import Mathlib
import QIQTH.TowerGNS.StageInner

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **The per-corner Gibbs modular flow** — the diagonal modular flow at the Gibbs weights.
    Every fact about it below routes through the rescale bridge `σ_t^{ρ_β} = α_{−βt}`. -/
noncomputable def cornerFlow (C : Finset M) (t : ℝ) (x : DiamondAlg L C) : DiamondAlg L C :=
  QIQTH.FiniteModularTheory.sigmaDiag (fun n => gibbsWeight L C ω β n) t x

/-- **The rescale bridge** (the held DY3 capstone, restated for `cornerFlow`):
    `σ_t^{ρ_β} = α_{−βt}`. -/
theorem cornerFlow_eq_alpha (C : Finset M) (t : ℝ) (x : DiamondAlg L C) :
    cornerFlow L ω β C t x = alpha L C ω (-(β * t)) x :=
  sigmaDiag_gibbs_eq_alpha_rescale L C ω β t x

/-- `σ_0 = id`. -/
theorem cornerFlow_zero (C : Finset M) (x : DiamondAlg L C) :
    cornerFlow L ω β C 0 x = x := by
  rw [cornerFlow_eq_alpha, mul_zero, neg_zero, alpha_zero]

/-- The flow is multiplicative at every `t`. -/
theorem cornerFlow_mul (C : Finset M) (t : ℝ) (x y : DiamondAlg L C) :
    cornerFlow L ω β C t (x * y) = cornerFlow L ω β C t x * cornerFlow L ω β C t y := by
  rw [cornerFlow_eq_alpha, cornerFlow_eq_alpha, cornerFlow_eq_alpha, alpha_mul]

/-- The flow is a ⋆-map at every `t`. -/
theorem cornerFlow_star (C : Finset M) (t : ℝ) (x : DiamondAlg L C) :
    cornerFlow L ω β C t xᴴ = (cornerFlow L ω β C t x)ᴴ := by
  rw [cornerFlow_eq_alpha, cornerFlow_eq_alpha, alpha_star]

/-- The flow is unital at every `t` (the identity is diagonal, hence stationary). -/
theorem cornerFlow_one (C : Finset M) (t : ℝ) :
    cornerFlow L ω β C t 1 = 1 := by
  have h := alpha_diagonal L C ω (-(β * t)) (fun _ => (1 : ℂ))
  rw [Matrix.diagonal_one] at h
  rw [cornerFlow_eq_alpha]
  exact h

/-- The flow is additive at every `t` (distributivity over the opaque diagonal
    conjugators — no entry formula needed). -/
theorem cornerFlow_add (C : Finset M) (t : ℝ) (x y : DiamondAlg L C) :
    cornerFlow L ω β C t (x + y) = cornerFlow L ω β C t x + cornerFlow L ω β C t y := by
  simp only [cornerFlow, QIQTH.FiniteModularTheory.sigmaDiag, mul_add, add_mul]

/-- The flow is ℂ-homogeneous at every `t`. -/
theorem cornerFlow_smul (C : Finset M) (t : ℝ) (c : ℂ) (x : DiamondAlg L C) :
    cornerFlow L ω β C t (c • x) = c • cornerFlow L ω β C t x := by
  simp only [cornerFlow, QIQTH.FiniteModularTheory.sigmaDiag, Matrix.mul_smul,
    Matrix.smul_mul]

/-- **The Gibbs state is invariant under its own modular flow** (through the bridge:
    `φ_β ∘ σ_t = φ_β ∘ α_{−βt} = φ_β` by the held stationarity). -/
theorem stateOf_cornerFlow (C : Finset M) (t : ℝ) (x : DiamondAlg L C) :
    stateOf (gibbsDensity L C ω β) (cornerFlow L ω β C t x)
      = stateOf (gibbsDensity L C ω β) x := by
  rw [cornerFlow_eq_alpha]
  exact gibbs_stationary L C ω β (-(β * t)) x

/-- The flow is a real one-parameter group: `σ_t ∘ σ_s = σ_{t+s}` (the Gibbs weights are
    strictly positive, so the held diagonal group law applies). -/
theorem cornerFlow_comp (C : Finset M) (t s : ℝ) (x : DiamondAlg L C) :
    cornerFlow L ω β C t (cornerFlow L ω β C s x) = cornerFlow L ω β C (t + s) x :=
  sigmaDiag_comp (fun n => gibbsWeight L C ω β n)
    (fun n => Complex.ofReal_ne_zero.mpr (gibbsWeight_pos L C ω β n).ne') t s x

/-- **B1 CAPSTONE — the flow preserves the GNS form at every stage**:
    `⟪σ_t x, σ_t y⟫_C = ⟪x, y⟫_C` — the ⋆/mul laws pull the flow out of the form
    (`(σ_t x)ᴴ (σ_t y) = σ_t(xᴴ y)`), and state invariance collapses it. The flow is a
    pre-unitary on every stage's GNS pre-space. -/
theorem gnsInner_cornerFlow (C : Finset M) (t : ℝ) (x y : DiamondAlg L C) :
    gnsInner L ω β C (cornerFlow L ω β C t x) (cornerFlow L ω β C t y)
      = gnsInner L ω β C x y := by
  rw [gnsInner, gnsInner, ← cornerFlow_star, ← cornerFlow_mul, stateOf_cornerFlow]

/-- **Tower equivariance of the flow**: the corner inclusions intertwine the per-corner
    flows — `ι ∘ σ_t^C = σ_t^{C′} ∘ ι` (T7's modular-flow equivariance, restated for
    `cornerFlow`). -/
theorem cornerFlow_cornerEmbed (C C' : Finset M) (h : C ⊆ C') (t : ℝ)
    (x : DiamondAlg L C) :
    cornerEmbed L C C' h (cornerFlow L ω β C t x)
      = cornerFlow L ω β C' t (cornerEmbed L C C' h x) :=
  (cornerEmbed_sigmaDiag L C C' h ω β t x).symm

end QIQTH.TowerGNS
