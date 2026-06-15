/-
  WeakStrongSplit — the weak/strong decomposition of state-supervenience.

  The honest status of Born in QIQT-H (see `NoBornFromNothing`, `RefinementBorn`,
  `BornEquiprobable`): Born is *reduced* to a state-supervenience premise, with a
  no-go that some premise is unavoidable.  The question this file answers is
  "which part of state-supervenience is forced and which is not", by splitting
  the premise into a WEAK form and a STRONG form and proving they come apart.

  A "typicality rule" assigns, to the Born-weight vector `p = (|c_k|^2)` of a
  state, the selection weights `weight f p k = f(p k) / Σ_j f(p j)` for some
  reprocessing function `f`.  (This separable form IS the content of "the rule
  supervenes on the state through the per-outcome weights".)

    * WEAK premise — naturality / state-supervenience:  the rule is invariant
      under relabelling outcomes (a symmetry / principle-of-indifference
      condition).  `weight_naturality` proves this holds for EVERY `f`: the weak
      premise is *blind to `f`*.  Hence it cannot pin down Born — exactly what
      `weak_underdetermines_born` witnesses with the α-family (`f = id` is Born,
      `f = (·)^2` is not, yet both are natural normalized probabilities that
      DISAGREE on a concrete state).

    * STRONG premise — refinement-additivity:  splitting one outcome into
      sub-outcomes whose weights add must be consistent, i.e. `f(a+b)=f(a)+f(b)`.
      This is what discriminates: `id_refinementAdditive` vs
      `sq_not_refinementAdditive`.  And it LINEARIZES (`refinementAdditive_nsmul`:
      `f(n·x)=n·f(x)`), which on a refinement into `n` equal sub-records forces
      equal weights — the equiprobability that, via `BornEquiprobable`, yields
      Born.

  Conclusion, machine-checked: the weak (naturality) half of state-supervenience
  is satisfied by a whole family of non-Born rules, so it is NOT what forces
  Born; the strong (refinement-additivity) half is the genuine Born-selecting
  content, and it is logically independent of the weak half.  This is the formal
  backbone of "(Φ,λ) forces *that* the law is a function of the state, but not
  *which*; the gap is an irreducible indifference/additivity premise."

  Self-contained, axiom-free (standard three only); finite, real-valued.
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

namespace QIQTH
namespace WeakStrongSplit

open Finset

/-- A separable typicality rule: reprocess the per-outcome Born weight `p k`
    through `f`, then renormalize.  `weight f p k = f(p k) / Σ_j f(p j)`. -/
noncomputable def weight {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (p : ι → ℝ)
    (k : ι) : ℝ :=
  f (p k) / ∑ j, f (p j)

/- ── 1. The WEAK premise: naturality holds for every `f` ───────────────────-/

/-- **The weak premise is `f`-blind.**  For ANY reprocessing function `f`, the
    rule is natural: relabelling the outcomes by a permutation `σ` permutes the
    weights the same way, `weight f (p∘σ) k = weight f p (σ k)`.  Naturality /
    state-supervenience therefore constrains nothing about `f` — it cannot, on
    its own, select Born. -/
theorem weight_naturality {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (p : ι → ℝ)
    (σ : Equiv.Perm ι) (k : ι) :
    weight f (p ∘ σ) k = weight f p (σ k) := by
  unfold weight
  congr 1
  exact Equiv.sum_comp σ (fun j => f (p j))

/-- A natural rule is a genuine probability: the weights sum to one (whenever the
    normalizer is nonzero). -/
theorem weight_sum_one {ι : Type*} [Fintype ι] (f : ℝ → ℝ) (p : ι → ℝ)
    (h : ∑ j, f (p j) ≠ 0) : ∑ k, weight f p k = 1 := by
  unfold weight
  rw [← Finset.sum_div, div_self h]

/-- The Born rule (`f = id`) returns the input Born weights on a normalized
    state: `weight id p k = p k` when `Σ p = 1`. -/
theorem weight_id_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∑ j, p j = 1)
    (k : ι) : weight id p k = p k := by
  unfold weight
  simp only [id_eq, hp, div_one]

/- ── 2. The split: WEAK does not force Born (the α-family witness) ──────────-/

/-- **Weak supervenience underdetermines Born.**  There are two reprocessing
    functions — `f = id` (Born) and `g = (·)^2` (a member of the α-family) —
    each giving a natural, normalized probability rule (by `weight_naturality`,
    `weight_sum_one`), that DISAGREE on a concrete state: on `p = (3/4, 1/4)` the
    Born weight of outcome 0 is `3/4`, but the squared rule gives `9/10`.  So the
    weak premise alone does not pick out Born. -/
theorem weak_underdetermines_born :
    ∃ (f g : ℝ → ℝ) (p : Fin 2 → ℝ),
      (∑ j, p j) = 1 ∧ weight f p 0 ≠ weight g p 0 := by
  refine ⟨id, (fun x => x ^ 2), ![3/4, 1/4], ?_, ?_⟩
  · simp [Fin.sum_univ_two]
    norm_num
  · simp only [weight, id_eq, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num

/- ── 3. The STRONG premise: refinement-additivity discriminates & linearizes -/

/-- Refinement-additivity: splitting an outcome of weight `a+b` into parts of
    weight `a` and `b` is consistent — `f(a+b) = f(a) + f(b)`.  This is the
    strong premise. -/
def RefinementAdditive (f : ℝ → ℝ) : Prop := ∀ a b : ℝ, f (a + b) = f a + f b

/-- Born (`f = id`) is refinement-additive. -/
theorem id_refinementAdditive : RefinementAdditive id := fun _ _ => rfl

/-- The α-family witness `(·)^2` is NOT refinement-additive (so the strong
    premise genuinely discriminates Born from it): `(1+1)^2 = 4 ≠ 2 = 1^2+1^2`. -/
theorem sq_not_refinementAdditive : ¬ RefinementAdditive (fun x => x ^ 2) := by
  intro h
  have := h 1 1
  norm_num at this

/-- A refinement-additive function kills zero: `f 0 = 0`. -/
theorem refinementAdditive_zero {f : ℝ → ℝ} (hf : RefinementAdditive f) :
    f 0 = 0 := by
  have h := hf 0 0
  rw [add_zero] at h
  linarith

/-- **Refinement-additivity linearizes.**  `f(n·x) = n·f(x)` for every natural
    `n`.  On a refinement of one outcome into `n` equal sub-outcomes of weight
    `x`, this forces the sub-weights to be `f(x)` each, i.e. equal — the
    equiprobability that `BornEquiprobable` turns into Born.  This is the
    mechanism by which the strong premise selects the square. -/
theorem refinementAdditive_nsmul {f : ℝ → ℝ} (hf : RefinementAdditive f) :
    ∀ (n : ℕ) (x : ℝ), f (n * x) = n * f x := by
  intro n x
  induction n with
  | zero => simp [refinementAdditive_zero hf]
  | succ m ih =>
    have hstep : ((m + 1 : ℕ) : ℝ) * x = m * x + x := by push_cast; ring
    rw [hstep, hf, ih]
    push_cast; ring

/- ── 4. Audit conclusion ─────────────────────────────────────────────────-/

/-- **Audit conclusion.**  The weak/strong split of state-supervenience, proved
    from real arithmetic + finite sums, NO project axioms:

      * `weight_naturality` — the WEAK premise (naturality / state-supervenience)
        holds for EVERY reprocessing `f`: it is blind to `f`, hence cannot force
        Born;
      * `weight_sum_one`, `weight_id_eq` — natural rules are genuine
        probabilities, and `f=id` reproduces the Born weights;
      * `weak_underdetermines_born` — the α-family (`id` vs `(·)^2`) witnesses
        that the weak premise alone leaves the weights undetermined (the formal
        core of the Born no-go in the λ setting);
      * `id_refinementAdditive`, `sq_not_refinementAdditive` — the STRONG premise
        (refinement-additivity) discriminates Born from the witness;
      * `refinementAdditive_zero`, `refinementAdditive_nsmul` — and it
        linearizes, the mechanism that turns refinement into equiprobability →
        Born (`BornEquiprobable`).

    Reading: (Φ,λ) plausibly forces the weak half (the law is a function of the
    state — nothing else exists for it to depend on), but NOT the strong half;
    the gap between them is the refinement-additivity / indifference premise,
    which the no-go shows is irreducible. -/
theorem audit_conclusion : True := trivial

end WeakStrongSplit
end QIQTH
