/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# ELECTRON_FIELD_PLAN E1 — local first-order operators preserve (closed) support

The genuine analytic core behind the electron's microcausality `S_D = (iγ·∂ + m)Δ_m`: the **Dirac causal
kernel `S_D` is a first-order *local* differential operator applied to the scalar Pauli–Jordan kernel
`Δ_m`**, so it cannot *enlarge* the support.  Since the scalar kernel vanishes for spacelike separations
(`QIQTH/Fock/PauliJordan.lean`, `pauliJordan_spacelike_tendsto_zero`), the Dirac kernel inherits the
spacelike vanishing — *microcausality of the electron field reduces to the (proved) scalar Pauli–Jordan
spacelike wall*, with no new analytic input.

This module proves the abstract, Mathlib-style backbone (NOT yet wired to the concrete `Δ_m`, which needs
the scalar kernel packaged as *exact* vanishing on the open spacelike region rather than a regularized
limit): **a first-order local operator `(A·f + B·∂f)` applied to a function `f` that vanishes on an open
set `s` vanishes on `s`**, because `f ≡ 0` near a point forces `fderiv f = 0` there; hence its support is
contained in `closure(support f)`, and in any closed set containing `support f`.  Specialized to the light
cone: if `Δ_m` is supported in the (closed) causal/light cone, so is `S_D = (iγ·∂+m)Δ_m`.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Dirac.
-/
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace QIQTH.Fock.Dirac.LocalDifferential

open Set Filter
open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **If `f` vanishes on an open set, it has zero derivative there.**  (`f ≡ 0` near `x` ⟹ `f'(x) = 0`.) -/
theorem hasFDerivAt_zero_of_eqOn_open {s : Set E} (hs : IsOpen s) {f : E → F} {x : E}
    (hx : x ∈ s) (hf : ∀ y ∈ s, f y = 0) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  have hloc : f =ᶠ[𝓝 x] fun _ : E => (0 : F) :=
    Filter.eventually_of_mem (hs.mem_nhds hx) (fun y hy => hf y hy)
  exact (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq hloc

theorem fderiv_eq_zero_of_eqOn_open {s : Set E} (hs : IsOpen s) {f : E → F} {x : E}
    (hx : x ∈ s) (hf : ∀ y ∈ s, f y = 0) :
    fderiv 𝕜 f x = (0 : E →L[𝕜] F) :=
  (hasFDerivAt_zero_of_eqOn_open (𝕜 := 𝕜) hs hx hf).fderiv

/-- A **first-order local operator** with (possibly point-dependent) coefficients: `(L f)(x) = A(x)·f(x) +
B(x)·∂f(x)`.  The Dirac operator `iγ·∂ + m` is of this form (`A = m`, `B = iγ·`). -/
noncomputable def FirstOrderOp (A : E → F →L[𝕜] G) (B : E → (E →L[𝕜] F) →L[𝕜] G) (f : E → F) (x : E) :
    G :=
  A x (f x) + B x (fderiv 𝕜 f x)

/-- **A first-order local operator vanishes wherever its input vanishes on an open neighbourhood.** -/
theorem firstOrderOp_eq_zero_of_eqOn_open (A : E → F →L[𝕜] G) (B : E → (E →L[𝕜] F) →L[𝕜] G)
    {s : Set E} (hs : IsOpen s) {f : E → F} {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, f y = 0) :
    FirstOrderOp (𝕜 := 𝕜) A B f x = 0 := by
  rw [FirstOrderOp, hf x hx, fderiv_eq_zero_of_eqOn_open (𝕜 := 𝕜) hs hx hf]
  simp

/-- **A first-order local operator does not enlarge support: `support(L f) ⊆ closure(support f)`.**  The
operator-theoretic statement of locality — `L f` can only be nonzero where `f` is (up to closure). -/
theorem support_firstOrderOp_subset_closure (A : E → F →L[𝕜] G) (B : E → (E →L[𝕜] F) →L[𝕜] G)
    (f : E → F) :
    Function.support (fun x => FirstOrderOp (𝕜 := 𝕜) A B f x) ⊆ closure (Function.support f) := by
  intro x hx
  by_contra hxcl
  have hs : IsOpen (closure (Function.support f))ᶜ := isClosed_closure.isOpen_compl
  have hfzero : ∀ y ∈ (closure (Function.support f))ᶜ, f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (subset_closure (by simpa [Function.mem_support] using hne))
  exact hx (firstOrderOp_eq_zero_of_eqOn_open (𝕜 := 𝕜) A B hs hxcl hfzero)

/-- **A first-order local operator preserves any closed support bound.**  If `support f ⊆ C` for a closed
`C` (e.g. the closed causal / light cone), then `support(L f) ⊆ C`.  Applied to the Dirac kernel
`S_D = (iγ·∂+m)Δ_m` with `Δ_m` supported in the closed light cone (the scalar Pauli–Jordan spacelike wall):
`S_D` is supported in the light cone too — **the electron field's microcausality inherits from the scalar
Pauli–Jordan spacelike vanishing**, with no new analytic input. -/
theorem support_firstOrderOp_subset_of_closed (A : E → F →L[𝕜] G) (B : E → (E →L[𝕜] F) →L[𝕜] G)
    (f : E → F) {C : Set E} (hC : IsClosed C) (hfC : Function.support f ⊆ C) :
    Function.support (fun x => FirstOrderOp (𝕜 := 𝕜) A B f x) ⊆ C :=
  (support_firstOrderOp_subset_closure (𝕜 := 𝕜) A B f).trans (closure_minimal hfC hC)

end QIQTH.Fock.Dirac.LocalDifferential
