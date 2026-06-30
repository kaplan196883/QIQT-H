/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# I5 — a NON-VACUOUS `Phase5Master` instance from a finite trace (T1 of the crossed-product scope)

`QIQTH/FQBoundCGP.lean` reduced P4's holographic area floor to a single, non-vacuous, minimal interface — the
`Phase5Master` certificate, proved (both directions) equivalent to the JLMS master inequality
`S_vN + cgpEntropy S ξ ≤ areaTerm`. The genuine continuum dual-weight Type II_∞ trace that *supplies* that
inequality is a multi-month frontier (`CROSSED_PRODUCT_TYPE_II_SCOPE.md` §4). This file delivers T1 (ibid. §3):
a **concrete finite trace model** in which the certificate is discharged **non-vacuously** — i.e. NOT by
`Phase5Master.of_le` fed an assumed inequality, but with `SvN`, `areaTerm`, and the `remainder` all the model's
genuine quantities and the balance proved from a real theorem.

The finite (Type I / II₁ shadow) trace model: a finite density matrix `ρ : Matrix n n ℂ` (the finite trace is
`Matrix.trace`, `ρ.trace = 1`); the model entropy is the von Neumann entropy `S_vN(ρ) = −tr(ρ log ρ)`; the
independent **capacity / finite "area"** is `log|n| = log(dim 𝓗_R)` (the trace's renormalization scale); and the
**vacuum vector `ξ = 0`** makes the CGP relative entropy vanish (`cgpEntropy_zero`). The JLMS balance
`S_vN + cgpEntropy + remainder = areaTerm` then holds with `remainder = log|n| − S_vN(ρ)` the **genuine entropy
deficit**, proved `≥ 0` by the axiom-free Jensen/Gibbs max-entropy bound `vonNeumannEntropy_le_log_card`.

**Why this is non-vacuous (the soundness point).** `Phase5Master.of_le` would take the inequality
`SvN + cgpEntropy ≤ areaTerm` as *input*. Here `areaTerm` is **derived** (`= log|n|`, fixed by the model's
dimension), and the inequality is the **output** of a proved theorem; the `remainder` is the model's actual
entropy deficit (`> 0` off saturation, `= 0` exactly at the maximally-mixed record). So the interface to which
P4's floor was reduced is genuinely instantiable. This is a *finite Type I/II₁ shadow*, not the continuum
Type II_∞ trace — the `e^{−s}` dual-action scaling and the unbounded clock stay the §4 frontier. The
identification `log|n| = A/4ℓ_P²` carries the **value of `G`** (≡ `ℓ_P²`) as the UV datum, never asserted; the
`1/4` *ratio* itself is separately derived (`SakharovRatio.lean`, circularity-clean Sakharov).
Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import QIQTH.FQBoundCGP
import QIQTH.FQBoundMicro

namespace QIQTH.QG

open QuantumEntropy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **★ I5 — the non-vacuous `Phase5Master` instance from a finite trace.** For any standard subspace `S` and any
finite density matrix `ρ` (the finite trace model), the certificate `Phase5Master S 0 (S_vN ρ) (log|n|)` holds
with `remainder = log|n| − S_vN(ρ)` the genuine entropy deficit (`≥ 0` by `vonNeumannEntropy_le_log_card`) and the
JLMS balance an equality (`cgpEntropy S 0 = 0`). `areaTerm = log|n|` is derived, the inequality is output — NOT
`Phase5Master.of_le` on an assumed bound. -/
noncomputable def phase5_of_finite_trace (S : StandardSubspace H) {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (h : IsDensity ρ) :
    Phase5Master S (0 : H) (vonNeumannEntropy h) (Real.log (Fintype.card n)) where
  remainder := Real.log (Fintype.card n) - vonNeumannEntropy h
  remainder_nonneg := by have := vonNeumannEntropy_le_log_card h; linarith
  jlms_balance := by rw [cgpEntropy_zero]; ring

/-- **P4's holographic floor obtained THROUGH the discharged interface.** Using the non-vacuous instance and
`phase5_master_ineq`, the von Neumann entropy of the finite trace model obeys `S_vN(ρ) ≤ log|n|` — the
holographic area floor, here derived *via* the `Phase5Master` certificate (demonstrating the interface yields the
floor, not merely that the bound exists). -/
theorem finiteTrace_area_floor (S : StandardSubspace H) {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ Real.log (Fintype.card n) := by
  haveI : Phase5Master S (0 : H) (vonNeumannEntropy h) (Real.log (Fintype.card n)) :=
    phase5_of_finite_trace S h
  have hineq := phase5_master_ineq (S := S) (ξ := (0 : H))
    (SvN := vonNeumannEntropy h) (areaTerm := Real.log (Fintype.card n))
  rwa [cgpEntropy_zero, add_zero] at hineq

end QIQTH.QG
