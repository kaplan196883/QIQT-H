/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The modular Hamiltonian `K` as a symmetric unbounded operator (Stone generator of `Δ^{it}`)

Applying the **general Stone generator** (`QIQTH/Spectral/Stone.lean`) to the modular flow
`Δ^{it} = modUnitary S t` on the one-particle space `H` (the C₀ unitary group built via the bounded Borel
functional calculus of `R = P+Q`, `QIQTH/StandardSubspaceModularFlow.lean`): its three Stone hypotheses — the
group law (`modUnitary_add`), `Δ^0 = 1` (`modUnitary_zero`), and inner-product preservation (derived here from
`modUnitary_adjoint`) — are all in hand. So the **modular generator** `modularGen := stoneGen (modUnitary S) =
−i d/dt Δ^{it}` (the modular Hamiltonian, `Δ^{it} = e^{it·modularGen}`) is a genuine *symmetric* unbounded
operator (`LinearPMap`) with the Cayley estimates, hence `modularGen ± i` injective.

This is the **third** of the three C₀ groups the wall-campaign instantiates (the clock energy `X = A_edge`,
`QIQTH/CrossedProductGenerator.lean`; the momentum `P`, `QIQTH/Spectral/MomentumGenerator.lean`; the modular
`Δ^{it}` here). `modularGen` is the `K` of the JLMS modular Hamiltonian `K̃ = A_edge·(1/4ℓ_P²) + K_bulk`.
Unlike the clock/momentum groups (on heavy `Lp` types), `modUnitary` lives on the abstract one-particle space,
so the instantiation needs no `Lp`-elaboration workaround.

**Essential self-adjointness IS now proved** (the Gårding-density / deficiency-index route was closed in
`QIQTH/Spectral/Garding.lean`): `modularGen_isSelfAdjoint` below gives `IsSelfAdjoint (modularGen S)` in the
genuine `LinearPMap` sense `K = K†`, via `stoneGen_isSelfAdjoint` (symmetry `K ⊆ K†` + the hard surjectivity
`Range(K + i) = H` from `stoneGen_add_I_surjective`, Gårding density + `ker(K† + i) = 0`).  So `K = modularGen`
is a genuine self-adjoint unbounded operator and `Δ^{it} = e^{itK}` is available via the spectral theorem —
the continuum modular Hamiltonian, not a carried frontier.  (Earlier revisions of this header labelled it
unclaimed; that is stale.)  Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import QIQTH.StandardSubspaceModularFlow
import QIQTH.Spectral.Stone
import QIQTH.Spectral.Garding

namespace QIQTH.StandardSubspaceModular

open QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The modular group law in `∘L` form: `Δ^{i(s+t)} = Δ^{is} ∘L Δ^{it}` (the Stone `hgrp` hypothesis), from
    `modUnitary_add` (stated with `*`, which on `H →L[ℂ] H` is composition). -/
theorem modUnitary_compL (S : StandardSubspace H) (s t : ℝ) :
    modUnitary S (s + t) = modUnitary S s ∘L modUnitary S t := by
  rw [modUnitary_add]; rfl

/-- Inner-product preservation `⟪Δ^{it} a, Δ^{it} b⟫ = ⟪a, b⟫` (the Stone `hUinner` hypothesis): `Δ^{it}` is
    unitary, `(Δ^{it})† Δ^{it} = Δ^{-it} Δ^{it} = Δ^0 = 1` (from `modUnitary_adjoint`/`_add`/`_zero`). -/
theorem inner_modUnitary_self (S : StandardSubspace H) (t : ℝ) (a b : H) :
    (inner ℂ (modUnitary S t a) (modUnitary S t b) : ℂ) = inner ℂ a b := by
  rw [← ContinuousLinearMap.adjoint_inner_right (modUnitary S t) a (modUnitary S t b),
    ← ContinuousLinearMap.mul_apply, modUnitary_adjoint, ← modUnitary_add, neg_add_cancel,
    modUnitary_zero, ContinuousLinearMap.one_apply]

/-- **★ The modular Hamiltonian `K`** = the (densely-definable) generator `−i d/dt Δ^{it}` of the modular
    flow, as a `LinearPMap` on the one-particle space `H`. This is the `K` of JLMS `K̃ = A_edge·(1/4ℓ_P²) + K_bulk`. -/
noncomputable def modularGen (S : StandardSubspace H) : H →ₗ.[ℂ] H :=
  stoneGen (modUnitary S)

/-- **★ The modular Hamiltonian is symmetric** — `K` is a formal adjoint of itself in Mathlib's `LinearPMap`
    framework (`K ⊆ K†` once its domain is dense). -/
theorem modularGen_isFormalAdjoint_self (S : StandardSubspace H) :
    (stoneGen (modUnitary S)).IsFormalAdjoint (stoneGen (modUnitary S)) :=
  stoneGen_isFormalAdjoint_self (modUnitary S) (modUnitary_compL S) (modUnitary_zero S)
    (inner_modUnitary_self S)

/-- **★ The Cayley estimate for the modular Hamiltonian** — `‖(K + i) x‖² = ‖K x‖² + ‖x‖²`. -/
theorem modularGen_norm_add_smul_I_sq (S : StandardSubspace H) (x : (stoneGen (modUnitary S)).domain) :
    ‖stoneGen (modUnitary S) x + Complex.I • (x : H)‖ ^ 2
      = ‖stoneGen (modUnitary S) x‖ ^ 2 + ‖(x : H)‖ ^ 2 :=
  stoneGen_norm_add_smul_I_sq (modUnitary S) (modUnitary_compL S) (modUnitary_zero S)
    (inner_modUnitary_self S) x

/-- **★ `K + i` is bounded below** — `‖x‖ ≤ ‖(K + i) x‖`, so `K + i` is injective on the smooth domain (half
    the deficiency-index data; essential self-adjointness needs `Range(K ± i)` dense, the carried frontier). -/
theorem modularGen_norm_le_norm_add_smul_I (S : StandardSubspace H) (x : (stoneGen (modUnitary S)).domain) :
    ‖(x : H)‖ ≤ ‖stoneGen (modUnitary S) x + Complex.I • (x : H)‖ :=
  stoneGen_norm_le_norm_add_smul_I (modUnitary S) (modUnitary_compL S) (modUnitary_zero S)
    (inner_modUnitary_self S) x

/-- **★★★ The modular Hamiltonian `K` is self-adjoint:** `IsSelfAdjoint (stoneGen (modUnitary S))`. The generic
    `stoneGen_isSelfAdjoint` instantiated for the modular flow `Δ^{it} = modUnitary S t` (group law, `Δ^0 = 1`,
    unitarity `inner_modUnitary_self`, the contraction `modUnitary_norm`, strong continuity). So `K` is a genuine
    self-adjoint unbounded operator — the spectral theorem's hypothesis for the JLMS modular Hamiltonian. -/
theorem modularGen_isSelfAdjoint (S : StandardSubspace H) :
    IsSelfAdjoint (stoneGen (modUnitary S)) :=
  stoneGen_isSelfAdjoint (modUnitary S) (modUnitary_compL S) (modUnitary_zero S)
    (inner_modUnitary_self S) (fun t y => le_of_eq (modUnitary_norm S t y))
    (modUnitary_stronglyContinuous S)

end QIQTH.StandardSubspaceModular
