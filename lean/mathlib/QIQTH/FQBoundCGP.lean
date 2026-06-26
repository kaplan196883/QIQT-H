/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Grounding the conditional FQ bound in the proved one-particle relative entropy

`QIQTH/FQBoundConditional.lean` proves P4's holographic area floor `S(ρ_R) ≤ A/4ℓ_P²` as a *conditional* algebraic
theorem `fq_bound_of_slack`: from a nonnegative `slack` and the master inequality `S + slack ≤ areaTerm`.  This
file discharges the `0 ≤ slack` hypothesis with a **proved** positivity: the one-particle CGP modular relative
entropy `cgpEntropy S ξ`, which is already shown `≥ 0` axiom-free (`cgpEntropy_nonneg`, the JLMS Stage-2 / Klein
positivity engine).  So the only remaining hypothesis of the grounded FQ bound is the **master inequality**
`S_vN + cgpEntropy S ξ ≤ areaTerm` — exactly the output the Phase-5 dual-weight trace + JLMS identity must supply.

HONEST.  `areaTerm` (`= ⟨A_edge⟩/4ℓ_P²` once the trace exists) and the master inequality are theorem hypotheses,
not axioms; the value of `G` / the edge normalization is the carried UV datum and is never claimed.  Free scalar.
-/
import QIQTH.ModularRelativeEntropy
import QIQTH.FQBoundConditional

namespace QIQTH

open MeasureTheory QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The FQ bound grounded in the proved one-particle relative entropy.**  For a separating/cyclic standard
    subspace `S`, a vector `ξ` in the real subspace (`projK S ξ = ξ`) whose modular spectrum avoids the endpoints
    (`hspec`), the CGP relative entropy `cgpEntropy S ξ` is a *proved* nonnegative slack (`cgpEntropy_nonneg`).
    Hence whenever the JLMS master inequality `S_vN + cgpEntropy S ξ ≤ areaTerm` holds (the Phase-5 trace's output,
    with `areaTerm = ⟨A_edge⟩/4ℓ_P²`), the entropy obeys the **FQ bound** `S_vN ≤ areaTerm`.  The slack positivity is
    no longer hypothesized — it is the machine-checked `cgpEntropy_nonneg`; only the master inequality (the trace)
    remains as input. -/
theorem fq_bound_cgp (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a)
    {SvN areaTerm : ℝ} (hmaster : SvN + cgpEntropy S ξ ≤ areaTerm) :
    SvN ≤ areaTerm :=
  QIQTH.FQBound.fq_bound_of_slack (cgpEntropy_nonneg S hξ ha ha1 hspec) hmaster

end QIQTH
