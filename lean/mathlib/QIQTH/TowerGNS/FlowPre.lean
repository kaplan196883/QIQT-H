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
import QIQTH.TowerGNS.PreSpace

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

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

/-! ### B2 — the flow on the tower pre-space: `flowRaw` + isometry + `flowPre`

The per-corner flow acts DIAGONALLY on the raw direct sum (same stage, no stage shift —
unlike `leftMulRaw`); the B1 laws (`gnsInner_cornerFlow` + `cornerFlow_cornerEmbed`) make it
a raw ISOMETRY of the tower form, and `LinearMap.mkContinuous` with constant `1` packages
the continuous pre-unitary `flowPre : TowerPre →L[ℂ] TowerPre`. LEAN ARCHITECTURE (the R3
lesson, binding): the working lemmas (`flowRaw`, `flowRaw_of`, `rawInner_flowRaw`) live at
the RAW `⨁` type; the `TowerPre`-typed items (`flowPreₗ`, the norm bound, `flowPre`) are
final wrappers accepted by application-position definitional equality. -/

/-- The per-corner flow at a fixed stage, bundled as a ℂ-linear map (B1's
    `cornerFlow_add`/`cornerFlow_smul`). -/
noncomputable def cornerFlowₗ (C : Finset M) (t : ℝ) :
    DiamondAlg L C →ₗ[ℂ] DiamondAlg L C where
  toFun := cornerFlow L ω β C t
  map_add' x y := cornerFlow_add L ω β C t x y
  map_smul' c x := cornerFlow_smul L ω β C t c x

/-- **The raw flow pre-operator**: the component at stage `C` flows IN PLACE by the
    per-corner Gibbs modular flow — same stage, no stage shift. -/
noncomputable def flowRaw (t : ℝ) :
    (⨁ C : Finset M, DiamondAlg L C) →ₗ[ℂ] (⨁ C : Finset M, DiamondAlg L C) :=
  DirectSum.toModule ℂ (Finset M) (⨁ C : Finset M, DiamondAlg L C) fun C =>
    (DirectSum.lof ℂ (Finset M) (fun C : Finset M => DiamondAlg L C) C) ∘ₗ
      (cornerFlowₗ L ω β C t)

@[simp] theorem flowRaw_of (t : ℝ) (C : Finset M) (x : DiamondAlg L C) :
    flowRaw L ω β t (DirectSum.of _ C x)
      = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (cornerFlow L ω β C t x) := by
  rw [← DirectSum.lof_eq_of ℂ, flowRaw]
  erw [DirectSum.toModule_lof]
  rfl

/-- **B2 KEY (raw) — the flow is an isometry of the tower form**: double induction reduces
    to pure components, where B1's tower equivariance pushes the flow through the embeddings
    into the common stage `C ⊔ C'` and B1's capstone `gnsInner_cornerFlow` collapses it. -/
theorem rawInner_flowRaw (t : ℝ) (x y : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β (flowRaw L ω β t x) (flowRaw L ω β t y) = rawInner L ω β x y := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (flowRaw L ω β t), map_zero (rawInner L ω β),
      AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  | of C a =>
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (flowRaw L ω β t),
        map_zero (rawInner L ω β (flowRaw L ω β t (DirectSum.of _ C a))),
        map_zero (rawInner L ω β (DirectSum.of _ C a))]
    | of C' b =>
      rw [flowRaw_of, flowRaw_of, rawInner_of_of, rawInner_of_of]
      show gnsInner L ω β (C ⊔ C')
          (cornerEmbed L C (C ⊔ C') Finset.subset_union_left (cornerFlow L ω β C t a))
          (cornerEmbed L C' (C ⊔ C') Finset.subset_union_right (cornerFlow L ω β C' t b))
        = gnsInner L ω β (C ⊔ C')
            (cornerEmbed L C (C ⊔ C') Finset.subset_union_left a)
            (cornerEmbed L C' (C ⊔ C') Finset.subset_union_right b)
      rw [cornerFlow_cornerEmbed, cornerFlow_cornerEmbed, gnsInner_cornerFlow]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (flowRaw L ω β t),
        map_add (rawInner L ω β (flowRaw L ω β t (DirectSum.of _ C a))), h₁, h₂,
        map_add (rawInner L ω β (DirectSum.of _ C a))]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (flowRaw L ω β t),
      map_add (rawInner L ω β) (flowRaw L ω β t x₁) (flowRaw L ω β t x₂),
      AddMonoidHom.add_apply, h₁, h₂,
      map_add (rawInner L ω β) x₁ x₂, AddMonoidHom.add_apply]

/-! ### The synonym wrappers (application-position defeq only — the R3 lesson) -/

/-- The flow at the synonym, as a plain linear map (fields delegate to the raw map by
    definitional equality). -/
noncomputable def flowPreₗ (t : ℝ) : TowerPre L ω β →ₗ[ℂ] TowerPre L ω β where
  toFun x := flowRaw L ω β t x
  map_add' x y := (flowRaw L ω β t).map_add x y
  map_smul' r x := (flowRaw L ω β t).map_smul r x

@[simp] theorem flowPreₗ_apply (t : ℝ) (x : TowerPre L ω β) :
    flowPreₗ L ω β t x = flowRaw L ω β t x := rfl

/-- The flow preserves the tower seminorm (raw isometry + `√(‖·‖²)`). -/
theorem flowPreₗ_norm_eq (t : ℝ) (x : TowerPre L ω β) :
    ‖flowPreₗ L ω β t x‖ = ‖x‖ := by
  have hinner : ⟪flowPreₗ L ω β t x, flowPreₗ L ω β t x⟫_ℂ = ⟪x, x⟫_ℂ :=
    rawInner_flowRaw L ω β t x x
  have h2 : ‖flowPreₗ L ω β t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (flowPreₗ L ω β t x),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) x, hinner]
  calc ‖flowPreₗ L ω β t x‖
      = Real.sqrt (‖flowPreₗ L ω β t x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [h2]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The `mkContinuous`-shaped bound with constant `1` (the flow is norm-preserving, hence
    trivially bounded). -/
theorem flowRaw_norm_le (t : ℝ) (x : TowerPre L ω β) :
    ‖flowPreₗ L ω β t x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  exact le_of_eq (flowPreₗ_norm_eq L ω β t x)

/-- **B2 CAPSTONE — the continuous flow pre-operator**: the per-corner Gibbs modular flow
    as a CONTINUOUS linear isometry candidate on the tower pre-space (constant `1`), ready
    for extension to the completion. -/
noncomputable def flowPre (t : ℝ) : TowerPre L ω β →L[ℂ] TowerPre L ω β :=
  LinearMap.mkContinuous (flowPreₗ L ω β t) 1 fun x => flowRaw_norm_le L ω β t x

@[simp] theorem flowPre_apply (t : ℝ) (x : TowerPre L ω β) :
    flowPre L ω β t x = flowRaw L ω β t x := rfl

/-- The continuous flow pre-operator preserves the tower seminorm. -/
theorem flowPre_norm_eq (t : ℝ) (x : TowerPre L ω β) :
    ‖flowPre L ω β t x‖ = ‖x‖ :=
  flowPreₗ_norm_eq L ω β t x

end QIQTH.TowerGNS
