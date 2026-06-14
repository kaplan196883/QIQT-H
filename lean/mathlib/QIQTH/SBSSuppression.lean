/-
SBSSuppression.lean — redundancy drives STRONG decoherence: the Quantum-Darwinism limit (2026-06-15)

`WeylBitStrongDecoherence` showed the multi-bit-differing residual vanishes *exactly* for ORTHOGONAL
record modes, and `bitOp_vac_expVec_cross_eq` gave the exact overlap correction for NON-orthogonal modes
(`∝ Re⟪u,v⟫`), with `strong_decoherence_needs_orthogonality` witnessing that a single overlapping record is
genuinely not strongly decoherent.  This file supplies the missing physical mechanism that restores strong
decoherence in that general case: **redundancy** (spectrum-broadcast structure / Quantum Darwinism).

The picture: a macroscopic pointer value is redundantly imprinted on `N` environment fragments.  Each
fragment distinguishes the two branches only *partially* — a per-fragment off-diagonal overlap `z k` of
modulus `≤ r < 1` (for orthogonal records `r = 0` and one fragment already suffices, cf.
`vacuum_bit_strong_decoherence`; the interesting case is `0 < r < 1`).  For independent fragments the joint
off-diagonal decoherence functional FACTORS as the product `∏ z k`, so it is suppressed as `rᴺ` and → 0 as
the redundancy `N → ∞`.  This is exactly how decoherence becomes effectively strong (`D ≈ 0`) for
macroscopic records even when no single fragment fully resolves them.

- `offdiagonal_norm_le` — the exponential bound `‖∏ z k‖ ≤ rᴺ`.
- `offdiagonal_tendsto_zero` — the joint off-diagonal → 0 as `N → ∞` (full/strong decoherence in the limit).

HONEST SCOPE: this is the abstract suppression law (the product of per-fragment overlaps decays), the
quantitative core of the SBS / Quantum-Darwinism objectivity argument (`SBSBoolean` supplies the exact
`r = 0` Boolean-record limit).  The *physical input* — that macroscopic records ARE redundantly broadcast
with bounded per-fragment overlap `r < 1` — is the (well-established) cited assumption, not derived here.
Axiom-free.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic

namespace QIQTH.SBSSuppression

open Filter Topology

/-- **Exponential suppression bound.**  With `N` redundant fragments, each contributing a per-fragment
off-diagonal overlap `z k` of modulus `≤ r`, the joint off-diagonal (the product) has modulus `≤ rᴺ`. -/
theorem offdiagonal_norm_le (r : ℝ) (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ r) (N : ℕ) :
    ‖∏ k ∈ Finset.range N, z k‖ ≤ r ^ N := by
  rw [norm_prod]
  calc ∏ k ∈ Finset.range N, ‖z k‖
      ≤ ∏ _k ∈ Finset.range N, r :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hz i)
    _ = r ^ N := by rw [Finset.prod_const, Finset.card_range]

/-- **SBS / Quantum-Darwinism suppression — redundancy ⇒ strong decoherence in the limit.**  If each of
infinitely many redundant fragments distinguishes the pointer with per-fragment overlap of modulus `≤ r < 1`,
the joint off-diagonal decoherence functional `∏ z k` → 0 as the redundancy `N → ∞`.  So even records that
are only partially resolved per fragment become *fully* (strongly) decohered once broadcast macroscopically:
`D → 0`.  This is the quantitative heart of objectivity/Quantum Darwinism. -/
theorem offdiagonal_tendsto_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (z : ℕ → ℂ) (hz : ∀ k, ‖z k‖ ≤ r) :
    Tendsto (fun N => ∏ k ∈ Finset.range N, z k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => offdiagonal_norm_le r z hz N) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

end QIQTH.SBSSuppression
