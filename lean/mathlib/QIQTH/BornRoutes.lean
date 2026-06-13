/-
BornRoutes.lean — new attack routes on the Born exponent (GPT-5.5-pro consult, 2026-06-13).

The exponent is underdetermined by all Born-free structural premises (the α-family `f(w)=w^α` is a proven
countermodel). Every closure route must supply ONE "Born-strength" ingredient that breaks the α-symmetry.
This file machine-checks two of pro's routes as clean conditional theorems, each with its Born-strength
premise made fully explicit. See `paper_strategy/50_Born_Attack_Routes.md`.

ROUTE C (count level): remote-split no-signaling ⇒ the count functional `F` is additive ⇒ `F(n)=n·F(1)` ⇒
Born weights `n_i/M`. Here the load-bearing `additive ⇒ linear` step.

ROUTE "MARTINGALE" (pro's best missing dynamical bridge): if the squared branch weight `W_k` is conserved in
μ-expectation (the martingale property) and the final record is absorbing (`W_k(T) ∈ {0,1}`) with initial
value `w_k`, then by optional stopping the μ-probability of outcome `k` is exactly the Born weight `w_k`.
The Born-strength premise is the martingale conservation — physically, the dynamics preserves expected
squared-weight (this is exactly why GRW/CSL collapse models recover Born). Deriving it from QIQT-H unitary
dynamics is the open step; the implication is clean and axiom-free.

HONEST SCOPE: finite; no `sorry`, no project axioms.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace QIQTH.BornRoutes

/-- **Route C core — additive count ⇒ linear.** If the unnormalised count/weight `F : ℕ → ℝ` is additive
(`F(a+b)=F(a)+F(b)`, which remote-split no-signaling forces), then `F(n) = n·F(1)`. Hence the normalised
weights are `n_i / Σ n_j` — the Born weights on the rational grid. (`additive` is the Born-strength premise;
the α-family `F(n)=n^α` fails it for `α≠1`.) -/
theorem additive_nat_linear (F : ℕ → ℝ) (hadd : ∀ a b, F (a + b) = F a + F b) :
    ∀ n : ℕ, F n = n * F 1 := by
  have h0 : F 0 = 0 := by have h := hadd 0 0; simp only [Nat.add_zero] at h; linarith
  intro n
  induction n with
  | zero => simp [h0]
  | succ k ih => rw [hadd k 1, ih]; push_cast; ring

/-- **Martingale / optional-stopping Born.** Let `μ` be a probability measure on a finite microstate space.
Suppose the squared branch weight evolves from `W0` (initial) to the final record `WT`, with:
* `W0 ≡ w_k` (the initial state has definite squared amplitude `w_k`),
* `WT` absorbing into a `0/1` record indicator of outcome `k`,
* `E_μ[WT] = E_μ[W0]` (the **martingale** property — μ-expected squared weight is conserved).
Then the μ-probability of outcome `k` equals the Born weight `w_k`. (The martingale conservation is the
Born-strength premise — the dynamical input GRW/CSL collapse models build in.) -/
theorem born_from_martingale {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (W0 WT : Ω → ℝ)
    (k : Ω → Prop) [DecidablePred k] (wk : ℝ)
    (hμ : ∑ ω, μ ω = 1)
    (hW0 : ∀ ω, W0 ω = wk)
    (hWT : ∀ ω, WT ω = if k ω then 1 else 0)
    (hmart : ∑ ω, μ ω * WT ω = ∑ ω, μ ω * W0 ω) :
    (∑ ω, if k ω then μ ω else 0) = wk := by
  have e1 : (∑ ω, if k ω then μ ω else 0) = ∑ ω, μ ω * WT ω := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [hWT ω, mul_ite, mul_one, mul_zero]
  rw [e1, hmart]
  simp_rw [hW0]
  rw [← Finset.sum_mul, hμ, one_mul]

/-! ### Meta no-go: why no Born-free premise can pin the exponent

Pro's "why can't I just invent the missing premise" turned into a theorem. The power-rule family
`Fα(n) = n^α` is the obstruction: any structural constraint `Γ` that the whole α-family satisfies
cannot entail Born, because `F₂` already satisfies `Γ` yet violates Born on a finite context. We
machine-check the concrete witness: with counts `[2,2]` vs the refinement `[1,1,2]`, the `α=2` rule
gives `P = 1/2` on the coarse context but `P = 1/5 ≠ 1/3` on... — the explicit numbers below. -/

/-- The `α=2` (squared-count) normalised rule on a list of integer counts: `Fα(nᵢ)/Σⱼ Fα(nⱼ)` with
`Fα(n)=n²`. -/
def sqRule (counts : List ℕ) (i : ℕ) : ℚ :=
  (((counts.getD i 0) ^ 2 : ℕ) : ℚ) / ((counts.map (fun n => (n ^ 2 : ℕ))).sum : ℚ)

/-- Born (linear-count) normalised rule: `nᵢ / Σⱼ nⱼ`. -/
def bornRule (counts : List ℕ) (i : ℕ) : ℚ :=
  (((counts.getD i 0) : ℕ) : ℚ) / ((counts.sum : ℕ) : ℚ)

/-- **Meta no-go witness (refinement non-invariance of the squared rule).** Take a two-outcome context
with counts `[2,2]` and its fine refinement `[1,1,2]` (outcome `A` split into two equal sub-records).
The Born rule is refinement-invariant: `P(A) = 2/4 = 1/2 = (1+1)/4` either way. The squared rule is NOT:
coarse gives `4/8 = 1/2`, but fine gives `(1+1)/(1+1+4) = 2/6 = 1/3`. So the squared (`α=2`) rule
satisfies normalisation and positivity yet *signals under refinement* — hence any premise set the whole
power-family obeys cannot force Born. This is the machine-checked core of the meta no-go. -/
theorem sqRule_refinement_signals :
    sqRule [2, 2] 0 = 1 / 2 ∧
    bornRule [2, 2] 0 = 1 / 2 ∧
    bornRule [1, 1, 2] 0 + bornRule [1, 1, 2] 1 = 1 / 2 ∧
    sqRule [1, 1, 2] 0 + sqRule [1, 1, 2] 1 = 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqRule, bornRule, List.getD_cons_zero, List.getD_cons_succ,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

end QIQTH.BornRoutes
