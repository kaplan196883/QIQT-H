/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# D3 — bounded entropy does NOT bound cardinality (Fork A capacity is entropy, not a state count)

Phase of `FINITE_MATTER_OR_ENTROPY_PLAN.md` (D3). D1 found QIQT-H is committed to **Fork A** (a finite
*renormalized-entropy* bound `S_τ ≤ Q_D` over covariant matter), and D2 proved **Fork B** (literal finite matter)
untenable for exact Lorentz. This file pins what Fork A's capacity *is*: a **bounded entropy is NOT a bounded
cardinality** — the trace→cardinality counterexample (`TRACE_CARDINALITY_SCOPE.md` K1), machine-checked.

A weighted record center with `N` atoms of trace weight `tᵢ = e^Q/N`, in the uniform label state `qᵢ = 1/N`, has
**trace-entropy exactly `Q`, independent of `N`** — because `H(\text{uniform}) = \log N` exactly cancels
`∑ qᵢ \log tᵢ = \log(e^Q/N) = Q - \log N`. So `S_τ ≤ Q` is satisfied by record families of *arbitrarily large
cardinality*, and `S_τ ≤ Q_D ⇏ \mathrm{card} ≤ e^{Q_D}`. Fork A's holographic bound is genuinely an **entropy**
bound (Lorentz-safe, over a covariant Type III₁ algebra), not a literal state count; a cardinality bound would
need an extra (minimal-cell / Holevo) hypothesis. Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace QIQTH.QG

open Finset

/-- The weighted (trace) entropy of a probability vector `q` against trace weights `t`:
`S_τ(q) = ∑ᵢ qᵢ · (−log(qᵢ/tᵢ)) = H(q) + ∑ᵢ qᵢ log tᵢ`. For unit weights `tᵢ = 1` it is the ordinary Shannon
entropy; the trace weights are what let bounded entropy coexist with unbounded cardinality. -/
noncomputable def traceEntropy {N : ℕ} (q t : Fin N → ℝ) : ℝ :=
  ∑ i, q i * (- Real.log (q i / t i))

/-- **The weighted counterexample value.** The uniform label state `qᵢ = 1/N` on `N` atoms with trace weights
`tᵢ = e^Q/N` has trace-entropy **exactly `Q`, independent of `N`**. -/
theorem traceEntropy_uniform_weighted {N : ℕ} (hN : 0 < N) (Q : ℝ) :
    traceEntropy (fun _ : Fin N => (1 : ℝ) / N) (fun _ : Fin N => Real.exp Q / N) = Q := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNr : (N : ℝ) ≠ 0 := hNpos.ne'
  have h1N : (1 : ℝ) / (N : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hEN : Real.exp Q / (N : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hlog : - Real.log (((1 : ℝ) / N) / (Real.exp Q / N)) = Q := by
    rw [Real.log_div h1N hEN, Real.log_div one_ne_zero hNr,
        Real.log_div (Real.exp_ne_zero Q) hNr, Real.log_exp, Real.log_one]
    ring
  unfold traceEntropy
  trans (∑ _i : Fin N, (1 : ℝ) / N * Q)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    show (1 : ℝ) / N * (- Real.log ((1 : ℝ) / N / (Real.exp Q / N))) = (1 : ℝ) / N * Q
    rw [hlog]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, mul_one_div, div_self hNr, one_mul]

/-- **★ D3 — bounded entropy does NOT bound cardinality.** For every `Q` and every `N ≥ 1` there is an `N`-atom
weighted record family that is a probability distribution (`∑ qᵢ = 1`) with trace-entropy **exactly `Q`** (hence
`≤ Q`). The cardinality `N` is therefore **unbounded at fixed entropy `Q`**: a finite renormalized-entropy bound
`S_τ ≤ Q_D` (Fork A) is genuinely an ENTROPY bound, **not** a literal state COUNT `card ≤ e^{Q_D}`. The
trace→cardinality counterexample, machine-checked. -/
theorem entropy_bound_not_cardinality_bound (Q : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ q t : Fin N → ℝ, (∑ i, q i = 1) ∧ traceEntropy q t = Q := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNr : (N : ℝ) ≠ 0 := hNpos.ne'
  refine ⟨fun _ => 1 / N, fun _ => Real.exp Q / N, ?_, traceEntropy_uniform_weighted hN Q⟩
  show ∑ _i : Fin N, (1 : ℝ) / N = 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end QIQTH.QG
