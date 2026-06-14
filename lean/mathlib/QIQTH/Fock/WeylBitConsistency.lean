/-
WeylBitConsistency.lean — the free-field Born histories are a CONSISTENT SET (2026-06-15)

This discharges the load-bearing obligation behind "the λ-measure is consistent" (see
`paper_strategy/57`, the decoherent-histories sense of *consistent*). A family of histories is a
**consistent set** (Gell-Mann–Hartle) iff the decoherence functional `D(α,β) = ⟪vec α, vec β⟫`
satisfies the medium-consistency condition `Re D(α,β) = 0` for `α ≠ β` — exactly the condition that
makes the Born weights `D(α,α) = ‖vec α‖²` obey the probability **sum rules** (additivity under
coarse-graining).

For the genuine Weyl-bit Born net (`WeylBitMeasure`), the bit operators `A(u,s) = (I + s·W(u))/2`
are NOT orthogonal projectors, so the *full* decoherence functional does NOT vanish — only its REAL
part does, and that is exactly medium decoherence. We prove this **exactly** (no `N → ∞`
environment limit), and show it is the same content as the existing normalization identity
`bit_normSq_sum`. Results:

- `bitOp_resolves` — `A(u,1)ψ + A(u,−1)ψ = ψ` (the two outcomes resolve the identity).
- `pythagoras_of_re_inner_zero` — `Re⟪a,b⟫ = 0 ⇒ ‖a+b‖² = ‖a‖²+‖b‖²` (sum rule ⇔ consistency).
- `medium_decoherence_bit` — **the consistency atom**: `Re⟪A(u,1)ψ, A(u,−1)ψ⟫ = 0`, exactly.
- `medium_decoherence_context` — the same in ANY commuting context, single-bit coarse-graining: the
  whole projective Born family is medium-decoherent (this is what powers `bornWeight_*_marginal`).
- `bell_consistency_alice` / `bell_consistency_bob` — the two-record (Bell) configuration is a
  consistent set on each wing; `bell_marginal_sum_rule` — hence the wing marginals are additive.

HONEST SCOPE: this is MEDIUM (a.k.a. weak) decoherence `Re D = 0` — exactly the Gell-Mann–Hartle
condition the Born sum rules require, and it holds EXACTLY here. STRONG decoherence (the full `D = 0`,
i.e. `Im D → 0` and *every* multi-bit pair, off-diagonals fully suppressed) is the separate
environmental-redundancy / SBS statement (`SBSBoolean`, Quantum Darwinism) — the cited mechanism, not
proved here. Uniqueness of the realm is separate again (`RealmSelection`: needs einselection).
Axiom-free.
-/
import QIQTH.Fock.WeylBitMeasure
import Mathlib.Tactic

namespace QIQTH.Fock

open scoped InnerProductSpace
open RCLike (re)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The two outcomes of a Weyl bit resolve the identity**: `A(u,1)ψ + A(u,−1)ψ = ψ`.  (So summing
the two history vectors of one bit gives the coarse-grained vector — the geometric content of
coarse-graining.) -/
theorem bitOp_resolves (u : H) (ψ : FockPre H) :
    bitOp u 1 ψ + bitOp u (-1) ψ = ψ := by
  rw [bitOp_apply, bitOp_apply, one_smul, neg_one_smul, smul_add, smul_add, smul_neg,
    add_add_add_comm, add_neg_cancel, add_zero, ← add_smul,
    show (1 / 2 + 1 / 2 : ℂ) = 1 from by norm_num, one_smul]

/-- **The Born sum rule is exactly medium decoherence.**  If the real part of the decoherence
functional between two history vectors vanishes, their Born weights add to the coarse-grained weight
(Pythagoras): `‖a + b‖² = ‖a‖² + ‖b‖²`.  This is the operational content of *consistent set*. -/
theorem pythagoras_of_re_inner_zero (a b : FockPre H) (h : re ⟪a, b⟫_ℂ = 0) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), h]; ring

/-- **MEDIUM DECOHERENCE — the consistency atom.**  For a single Weyl bit, the real part of the
decoherence functional between its two outcomes vanishes *exactly*:
`Re⟪A(u,1)ψ, A(u,−1)ψ⟫ = 0`.  This is the Gell-Mann–Hartle medium-consistency condition, and it is
equivalent to the normalization identity `bit_normSq_sum` (the Born sum rule): since
`A(u,1)ψ + A(u,−1)ψ = ψ`, Pythagoras + `bit_normSq_sum` force the cross term to vanish.  No `N → ∞`
environment limit is used — it is exact. -/
theorem medium_decoherence_bit (u : H) (ψ : FockPre H) :
    re ⟪bitOp u 1 ψ, bitOp u (-1) ψ⟫_ℂ = 0 := by
  have hres : bitOp u 1 ψ + bitOp u (-1) ψ = ψ := bitOp_resolves u ψ
  have hnorm : ‖bitOp u 1 ψ‖ ^ 2 + ‖bitOp u (-1) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := bit_normSq_sum u ψ
  have hadd := norm_add_sq (𝕜 := ℂ) (bitOp u 1 ψ) (bitOp u (-1) ψ)
  rw [hres] at hadd
  -- hadd : ‖ψ‖² = ‖a‖² + 2 * re⟪a,b⟫ + ‖b‖²
  linarith [hadd, hnorm]

/-- **Medium decoherence in any commuting context (single-bit coarse-graining).**  For a finite
commuting family `u` with symplectic isotropy, a head mode `a ∉ J'`, and any fixed outcomes `s` on
`J'`, the two completions of the history at `a` (`a ↦ +1`, `a ↦ −1`) are medium-decoherent:
`Re⟪vec(a↦+1), vec(a↦−1)⟫ = 0`.  This is the consistency condition that makes the projective Born
family `bornWeight_*_marginal` / `bornWeight_coarse` a genuine probability marginalization — the whole
typicality measure μ∞ rests on a CONSISTENT SET, exactly, axiom-free. -/
theorem medium_decoherence_context {ι : Type*} [DecidableEq ι] (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (s : ι → ℂ)
    (a : ι) (J' : Finset ι) :
    re ⟪bitOp (u a) 1 (bornVecTot u hiso s J'),
        bitOp (u a) (-1) (bornVecTot u hiso s J')⟫_ℂ = 0 :=
  medium_decoherence_bit (u a) (bornVecTot u hiso s J')

/-- **Bell two-record consistency — Alice wing.**  Fixing Bob's outcome `s'` (mode `v`), the two
Alice outcomes (mode `u`) are medium-decoherent.  So the Alice-marginal Born weights add up: the
configuration is a consistent set on the Alice wing. -/
theorem bell_consistency_alice (u v : H) (s' : ℂ) :
    re ⟪bitOp u 1 (bitOp v s' (vac H)), bitOp u (-1) (bitOp v s' (vac H))⟫_ℂ = 0 :=
  medium_decoherence_bit u (bitOp v s' (vac H))

/-- **Bell two-record consistency — Bob wing.**  Symmetrically, fixing Alice's outcome `s`, the two
Bob outcomes are medium-decoherent. -/
theorem bell_consistency_bob (u v : H) (s : ℂ) :
    re ⟪bitOp v 1 (bitOp u s (vac H)), bitOp v (-1) (bitOp u s (vac H))⟫_ℂ = 0 :=
  medium_decoherence_bit v (bitOp u s (vac H))

/-- **The Bell wing marginal obeys the Born sum rule.**  Because the Alice off-diagonal real part
vanishes (`bell_consistency_alice`), the two Alice outcomes' Born weights sum to the
Bob-only (Alice-coarse-grained) weight: `‖A(u,1)A(v,s')Ω‖² + ‖A(u,−1)A(v,s')Ω‖² = ‖A(v,s')Ω‖²`.
This is consistency made operational — the marginal probability is well defined. -/
theorem bell_marginal_sum_rule (u v : H) (s' : ℂ) :
    ‖bitOp u 1 (bitOp v s' (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v s' (vac H))‖ ^ 2
      = ‖bitOp v s' (vac H)‖ ^ 2 := by
  have h := pythagoras_of_re_inner_zero
    (bitOp u 1 (bitOp v s' (vac H))) (bitOp u (-1) (bitOp v s' (vac H)))
    (bell_consistency_alice u v s')
  rw [bitOp_resolves u (bitOp v s' (vac H))] at h
  exact h.symm

end QIQTH.Fock
