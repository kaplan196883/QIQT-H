/-
BornEquiprobable.lean — closing audit candidate (ii): symmetric equiprobability ⇒ Born (2026-06-15)

`BornTypicality.audit_summary` reduced Born-from-typicality to ONE question — *which* measure on the
microstate space is canonical — with three candidate principles. Candidate (ii) is **symmetric
equiprobability on a natural decomposition of the IC space**. The honest gap (`SelectionDynamics`,
`Relaxation`): the symmetric/uniform measure reproduces Born only if the decomposition has `count = M·w_k`
sub-records per outcome — and that multiplicity was *posited*, the circularity crux. (`RankCountNoGo` shows
no amplitude-INDEPENDENT count works, so the count must track the amplitudes.)

This file discharges candidate (ii). The decomposition is an **equal-amplitude orthonormal fine-graining**
`f : I → H` (each branch a unit vector, all equal amplitude — the Born-free notion of "equiprobable",
justified by `Envariance`) with a sector readout `sec : I → K`. The Zurek **amplitude→count bridge**:
by orthonormality alone, the squared-norm (Born) weight of a sector equals its branch-count fraction,

  `(‖∑_{sec i = k} fᵢ‖ / ‖∑ᵢ fᵢ‖)²  =  #{i : sec i = k} / |I|`.

So the *uniform* (symmetric) measure on `I` has outcome-marginal exactly the Born weight — the `count = M·w_k`
premise is no longer assumed, it is forced. We package this as a `CanonicalIcMeasure` whose `born_marginal`
field is PROVED, and feed it to `qiqth_born_typicality_conditional`: symmetric equiprobability over an
equal-amplitude orthonormal decomposition yields Born empirical frequencies.

HONEST RESIDUAL (sharpened after a 2026-06-15 GPT-5.5-pro review). The IDENTITY `‖ψ_k‖²/‖ψ‖² = count/|I|` is
non-circular linear algebra (Pythagoras + equal norms). But "orthonormality FORCES `count = M·w_k`" is only
true for an **equal-NORM** fine-graining with fixed sectors — arbitrary (unequal-norm) refinements restore the
`RankCountNoGo` freedom. So the load-bearing premise is the CANONICITY of the equal-norm decomposition (that λ
is uniform over the equal-norm atoms); the Lean structure being NAMED `CanonicalIcMeasure` does not prove it.
Remaining premises, none eliminated here, all needed for Born: (i) ENVARIANCE (equal-amplitude ⇒ equiprobable;
`EnvarianceJustification`); (ii) the equal-norm fine-graining is canonical (= refinement/coarse-graining
ADDITIVITY, `RefinementBorn` ⇔ Born — what excludes the α-family `w_k^q`); (iii) EXISTENCE of the
fine-graining (exact for rational `|c_k|²`, irrational needs continuity); (iv) PRODUCT independence for the
LLN. What this file genuinely does: replace the *naked posited* `count = M·w_k` with the orthonormality
identity, given an equal-norm decomposition — not derive Born from nothing. Axiom-free.
-/
import QIQTH.BornTypicality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

namespace QIQTH.BornEquiprobable

open scoped InnerProductSpace BigOperators
open QIQTH.BornTypicality QIQTH.NoBornFromNothing

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {I K : Type*} [Fintype I] [DecidableEq I] [DecidableEq K]

/-- **Orthonormal counting identity.**  The squared norm of a sum of an orthonormal family over a finite
set equals its cardinality: `‖∑_{i∈s} fᵢ‖² = |s|`.  (Cross terms vanish; the diagonal contributes 1 each.)
This is the Hilbert-space bookkeeping that ties amplitude to count. -/
theorem norm_sum_orthonormal_sq {f : I → H} (hf : Orthonormal ℂ f) (s : Finset I) :
    ‖∑ i ∈ s, f i‖ ^ 2 = (s.card : ℝ) := by
  have hortho : ∀ i j : I, ⟪f i, f j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    fun i j => orthonormal_iff_ite.mp hf i j
  have hinner : ∀ i ∈ s, ⟪f i, ∑ j ∈ s, f j⟫_ℂ = 1 := by
    intro i hi
    simp_rw [inner_sum, hortho]
    rw [Finset.sum_ite_eq s i (fun _ => (1 : ℂ))]
    simp [hi]
  have hcplx : (∑ i ∈ s, ⟪f i, ∑ j ∈ s, f j⟫_ℂ) = (s.card : ℂ) := by
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, hcplx]
  simp

/-- The Born amplitude of outcome `k` for the equal-amplitude state `ψ = ∑ fᵢ`: the norm of its sector
component, normalised by `‖ψ‖`. Its square is the Born weight. -/
noncomputable def sectorAmp (f : I → H) (sec : I → K) (k : K) : ℝ :=
  ‖∑ i ∈ Finset.univ.filter (fun i => sec i = k), f i‖ / ‖∑ i, f i‖

/-- **The Zurek amplitude→count bridge.**  The uniform (symmetric) measure's outcome-marginal equals the
Born squared-amplitude weight: `outcomeMarginal sec (1/|I|) k = (sectorAmp k)²`. Both sides equal the
branch-count fraction `#{sec i = k}/|I|` — the left by counting, the right by orthonormality. So the
`count = M·w_k` premise is forced, not assumed. -/
theorem uniform_marginal_eq_sectorAmp_sq [Nonempty I] {f : I → H} (hf : Orthonormal ℂ f)
    (sec : I → K) (k : K) :
    outcomeMarginal sec (fun _ => 1 / (Fintype.card I : ℝ)) k = (sectorAmp f sec k) ^ 2 := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hLHS : outcomeMarginal sec (fun _ => 1 / (Fintype.card I : ℝ)) k
      = ((Finset.univ.filter (fun i => sec i = k)).card : ℝ) / (Fintype.card I : ℝ) := by
    simp only [outcomeMarginal, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hRHS : (sectorAmp f sec k) ^ 2
      = ((Finset.univ.filter (fun i => sec i = k)).card : ℝ) / (Fintype.card I : ℝ) := by
    unfold sectorAmp
    rw [div_pow, norm_sum_orthonormal_sq hf,
      show (∑ i, f i) = ∑ i ∈ (Finset.univ : Finset I), f i from rfl,
      norm_sum_orthonormal_sq hf, Finset.card_univ]
  rw [hLHS, hRHS]

/-- **Candidate (ii) realised: a canonical (symmetric / equiprobable) IC measure pushing forward to Born.**
The uniform measure on an equal-amplitude orthonormal fine-graining is a `CanonicalIcMeasure` for the Born
weights `(sectorAmp k)² = |c_k|²` — with the `born_marginal` field PROVED from orthonormality
(`uniform_marginal_eq_sectorAmp_sq`), not posited. This is the symmetric-equiprobability answer to the
"which measure is canonical" question, with the counting residual discharged. -/
noncomputable def equiAmplitudeMeasure [Nonempty I] {f : I → H} (hf : Orthonormal ℂ f) (sec : I → K) :
    CanonicalIcMeasure I K sec (sectorAmp f sec) where
  μ := fun _ => 1 / (Fintype.card I : ℝ)
  nn := fun _ => by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
      div_self (by exact_mod_cast Fintype.card_ne_zero)]
  born_marginal := fun k => uniform_marginal_eq_sectorAmp_sq hf sec k

/-- **Born from symmetric equiprobability — the capstone.**  Over an equal-amplitude orthonormal
fine-graining, the symmetric (uniform) IC measure yields Born empirical frequencies: the expected per-run
frequency of every outcome `k` equals its squared amplitude `(sectorAmp k)²`. Combines the amplitude→count
bridge (orthonormality) with the existing conditional typicality theorem. The remaining inputs are the
envariance symmetry (`Envariance`) and the existence of the fine-graining — not a counting rule and not
the Born rule itself. -/
theorem born_from_equiprobability [Nonempty I] [Fintype K] {f : I → H} (hf : Orthonormal ℂ f)
    (sec : I → K) (k : K) :
    expectedIndicator sec (equiAmplitudeMeasure hf sec).μ k = (sectorAmp f sec k) ^ 2 :=
  qiqth_born_typicality_conditional sec (sectorAmp f sec) (equiAmplitudeMeasure hf sec) k

end QIQTH.BornEquiprobable
