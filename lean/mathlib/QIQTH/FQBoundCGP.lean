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

/-- **The Phase-5 certificate** (the named obligation the dual-weight trace / JLMS analysis must discharge).
    For a standard subspace `S`, a one-particle vector `ξ`, the von Neumann entropy `SvN` and the area term
    `areaTerm` (`= ⟨A_edge⟩/4ℓ_P²`), this bundles the **JLMS balance** as a single equation with an explicitly
    **nonnegative remainder**:  `SvN + cgpEntropy S ξ + remainder = areaTerm`.  This is the Lean analogue of the
    `DonaldSystem` typeclass that made the finite QIQT-H core axiom-free: P4's bound becomes an *unconditional*
    theorem relative to this certificate, and the certificate is a precise, **non-vacuous** physics interface (the
    remainder is the relative-entropy / bulk-modular / trace gap, which the Phase-5 dual-weight trace must produce
    `≥ 0` with the balance holding) — not an axiom.  Per GPT-5.5-pro's strategy audit (2026-06-27). -/
class Phase5Master (S : StandardSubspace H) (ξ : H) (SvN areaTerm : ℝ) where
  /-- The JLMS / trace remainder (relative entropy + bulk-modular + trace gap). -/
  remainder : ℝ
  /-- The remainder is nonnegative — the JLMS positivity content the trace must supply. -/
  remainder_nonneg : 0 ≤ remainder
  /-- The JLMS balance: entropy + CGP relative entropy + remainder = area term. -/
  jlms_balance : SvN + cgpEntropy S ξ + remainder = areaTerm

/-- **The JLMS master inequality, derived from the Phase-5 certificate:**
    `SvN + cgpEntropy S ξ ≤ areaTerm`.  Immediate from the balance with the nonnegative remainder. -/
theorem phase5_master_ineq {S : StandardSubspace H} {ξ : H} {SvN areaTerm : ℝ}
    [h : Phase5Master S ξ SvN areaTerm] : SvN + cgpEntropy S ξ ≤ areaTerm := by
  have hr := h.remainder_nonneg
  have hb := h.jlms_balance
  linarith

/-- **The Phase-5 certificate is EXACTLY the JLMS master inequality** (the converse of `phase5_master_ineq`):
    the certificate is constructible iff `SvN + cgpEntropy S ξ ≤ areaTerm`.  The witnessing remainder is the *gap*
    `areaTerm − SvN − cgpEntropy S ξ ≥ 0`.  Combined with `phase5_master_ineq`, this proves `Phase5Master` carries
    **neither more nor less** than the single inequality `SvN + cgpEntropy S ξ ≤ areaTerm` — confirming the interface
    is **non-vacuous** (it cannot be instanced for arbitrary `SvN`, `areaTerm`) and **minimal** (the dual-weight
    trace's *only* obligation is to supply that one inequality, via the JLMS area first law).  Axiom-free. -/
noncomputable def Phase5Master.of_le {S : StandardSubspace H} {ξ : H} {SvN areaTerm : ℝ}
    (h : SvN + cgpEntropy S ξ ≤ areaTerm) : Phase5Master S ξ SvN areaTerm where
  remainder := areaTerm - SvN - cgpEntropy S ξ
  remainder_nonneg := by linarith
  jlms_balance := by ring

/-- **★★★ P4's FQ bound, unconditional relative to the Phase-5 certificate:**
    `SvN ≤ areaTerm`.  Given the `Phase5Master` certificate (the JLMS balance with nonnegative remainder) and the
    standard CGP positivity hypotheses, the von Neumann entropy is at most the area term `⟨A_edge⟩/4ℓ_P²`.  This is
    the holographic area floor as a *theorem* — axiom-free, modulo the named Phase-5 physics interface
    (`Phase5Master`), which the dual-weight trace will instance.  The slack positivity is the proved
    `cgpEntropy_nonneg`; only the certificate (= the trace) remains.  The coefficient in `areaTerm` is the carried
    UV datum, never assigned. -/
theorem fq_bound_of_phase5 (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a)
    {SvN areaTerm : ℝ} [Phase5Master S ξ SvN areaTerm] : SvN ≤ areaTerm :=
  fq_bound_cgp S hξ ha ha1 hspec phase5_master_ineq

/-- **★★★ The holographic area floor in manifest form `S ≤ A/4ℓ_P²`, relative to the Phase-5 certificate.**
    Specializing `fq_bound_of_phase5` to `areaTerm = edgeArea / (4·ℓ_P²)` exhibits P4's bound in its physical shape:
    the entropy `SvN` is at most the **area over `4ℓ_P²`**.  Here `edgeArea` (`= ⟨A_edge⟩ = A(∂R)`, the **carried UV
    datum** whose value is *never* asserted) and `ellP` (the Planck length, physically `> 0`) are explicit; the
    coefficient `1/4ℓ_P²` is now manifest in the statement rather than hidden in `areaTerm`.  Axiom-free, relative
    only to the named `Phase5Master` certificate (the dual-weight trace's obligation).  The `1/4` *ratio* is derived
    separately (`SakharovRatio`); free scalar. -/
theorem holographic_area_floor (S : StandardSubspace H) {ξ : H} (hξ : projK S ξ = ξ)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S), a ≤ (ω : ℝ) ∧ (ω : ℝ) ≤ 2 - a)
    {SvN edgeArea ellP : ℝ} [Phase5Master S ξ SvN (edgeArea / (4 * ellP ^ 2))] :
    SvN ≤ edgeArea / (4 * ellP ^ 2) :=
  fq_bound_of_phase5 S hξ ha ha1 hspec

end QIQTH
