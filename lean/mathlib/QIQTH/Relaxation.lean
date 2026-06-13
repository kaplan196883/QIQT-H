/-
Relaxation.lean — the swing at the physics: derive measure-preservation from REVERSIBILITY, not assume it.

GPT-5.5-pro consult (2026-06-13). The Born residual is "the selection dynamics preserves a Born-agnostic
measure μ". Trying to get this from a relaxation / H-theorem story forces an honest reckoning:

  NO-GO (A): for ANY full-support `ν`, the reset kernel `K_ν(x,y) = ν y` is row-stochastic, strictly
  positive (primitive), and sends every measure to `ν` in one step — so "Markov + positive + relaxes to a
  unique equilibrium" does NOT single out the uniform/Born measure. Relaxation alone is Born-agnostic; the
  missing ingredient is exactly what rules out these non-uniform primitive kernels.

  ADVANCE (B): a REVERSIBLE closed update `F : S × E ≃ S × E` over a UNIFORM bath `E` induces a selector
  kernel `T_F(s,s') = #{e : fst (F (s,e)) = s'} / |E|` that is **bistochastic** — and column-stochasticity
  is *derived* from `F` being a bijection (the finite shadow of unitarity / Liouville), NOT assumed. Hence
  the uniform measure is STATIONARY for `T_F`. Pushed through the envariance fine-graining (where uniform
  count = Born weight, `SelectionDynamics.born_from_uniform`), the Born measure is the equilibrium.

This genuinely sharpens the irreducible input: from "assume μ is |Ψ|²-equivariant" to "assume the closed
dynamics is reversible and the inaccessible bath is uniform in counting measure" (finite Liouville +
molecular chaos). HONEST RESIDUAL (pro): stationarity ≠ relaxation — attraction needs a primitivity/mixing
premise (identity and permutations are bistochastic and do not mix); and the uniform-bath premise is itself
a typicality postulate, not pure logic. So Born is here the FIXED POINT forced by reversibility; that it is
the ATTRACTING one needs the separate mixing input. No `sorry`, no project axioms.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace QIQTH.Relaxation

/-- One step of a kernel `T` (entries `T x y`) acting on a measure `μ` on the left:
`(push μ T) y = ∑ₓ μ x · T x y`. -/
def push {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (T : Ω → Ω → ℝ) : Ω → ℝ :=
  fun y => ∑ x, μ x * T x y

/-! ### No-go A — relaxation to a unique equilibrium does NOT select Born -/

/-- The reset kernel ignores its input and jumps to `ν`: `K_ν(x,y) = ν y`. -/
def resetKernel {Ω : Type*} (ν : Ω → ℝ) : Ω → Ω → ℝ := fun _ y => ν y

variable {Ω : Type*} [Fintype Ω]

/-- The reset kernel is row-stochastic for any probability `ν`. -/
theorem resetKernel_row (ν : Ω → ℝ) (hν : ∑ y, ν y = 1) (x : Ω) :
    ∑ y, resetKernel ν x y = 1 := hν

omit [Fintype Ω] in
/-- The reset kernel is strictly positive (primitive) when `ν` has full support. -/
theorem resetKernel_pos (ν : Ω → ℝ) (hν : ∀ y, 0 < ν y) (x y : Ω) :
    0 < resetKernel ν x y := hν y

/-- **No-go.** One step of the reset kernel sends *every* probability measure to `ν`. So for ANY
full-support `ν` the dynamics has `ν` as its unique attracting equilibrium — relaxation to a unique,
strictly-positive fixed point is Born-agnostic and does not select the uniform/Born measure. -/
theorem resetKernel_reaches (ν : Ω → ℝ) (μ : Ω → ℝ) (hμ : ∑ x, μ x = 1) (y : Ω) :
    push μ (resetKernel ν) y = ν y := by
  simp only [push, resetKernel]
  rw [← Finset.sum_mul, hμ, one_mul]

/-- The reset kernel is bistochastic **iff** `ν` is uniform: its column sum is `|Ω|·ν y`. So the
non-uniform `ν` of the no-go are exactly the non-bistochastic kernels — bistochasticity is precisely the
extra input that relaxation lacks. -/
theorem resetKernel_colSum (ν : Ω → ℝ) (y : Ω) :
    ∑ x, resetKernel ν x y = (Fintype.card Ω : ℝ) * ν y := by
  simp only [resetKernel, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Advance B — reversibility over a uniform bath FORCES bistochasticity -/

variable {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]

/-- Selector kernel induced by a reversible closed update `F : S × E ≃ S × E` over a uniform bath `E`:
`T_F(s,s')` = fraction of bath states `e` for which the closed update sends record `s` to record `s'`. -/
noncomputable def inducedKernel (F : (S × E) ≃ (S × E)) (s s' : S) : ℝ :=
  ((Finset.univ.filter (fun e : E => (F (s, e)).1 = s')).card : ℝ) / (Fintype.card E)

/-- `T_F` is row-stochastic: each record `s` goes *somewhere* for every bath state. -/
theorem inducedKernel_row [Nonempty E] (F : (S × E) ≃ (S × E)) (s : S) :
    ∑ s', inducedKernel F s s' = 1 := by
  have hcard : Fintype.card E
      = ∑ s', (Finset.univ.filter (fun e : E => (F (s, e)).1 = s')).card := by
    rw [← Finset.card_univ (α := E)]
    exact Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ _)
  simp only [inducedKernel, ← Finset.sum_div, ← Nat.cast_sum]
  rw [← hcard]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- **The advance: `T_F` is column-stochastic — derived from reversibility.** Because `F` is a *bijection*
of `S × E`, the bath states landing on record `s'` (summed over all source records `s`) are exactly the
preimage of the fiber `{s'} × E`, which has `|E|` elements. So `∑ₛ T_F(s,s') = 1`. This is where finite
reversibility (the shadow of unitarity / Liouville's theorem) does the work that would otherwise be the
assumed `|Ψ|²`-equivariance. -/
theorem inducedKernel_col [Nonempty E] (F : (S × E) ≃ (S × E)) (s' : S) :
    ∑ s, inducedKernel F s s' = 1 := by
  have step1 : (∑ s, (Finset.univ.filter (fun e : E => (F (s, e)).1 = s')).card)
      = (Finset.univ.filter (fun p : S × E => (F p).1 = s')).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
  have step2 : (Finset.univ.filter (fun p : S × E => (F p).1 = s')).card
      = (Finset.univ.filter (fun q : S × E => q.1 = s')).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Equiv.sum_comp F (fun q => if q.1 = s' then 1 else 0)
  have step3 : (Finset.univ.filter (fun q : S × E => q.1 = s')).card = Fintype.card E := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hrow : ∀ s : S, (∑ _e : E, (if s = s' then (1 : ℕ) else 0))
        = (if s = s' then 1 else 0) * Fintype.card E := fun s => by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl (fun s _ => hrow s), ← Finset.sum_mul,
      (Finset.sum_ite_eq' Finset.univ s' (fun _ => (1 : ℕ))).trans (if_pos (Finset.mem_univ s')),
      one_mul]
  have hcard : (∑ s, (Finset.univ.filter (fun e : E => (F (s, e)).1 = s')).card)
      = Fintype.card E := by rw [step1, step2, step3]
  simp only [inducedKernel, ← Finset.sum_div, ← Nat.cast_sum]
  rw [hcard]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-! ### Bistochastic ⇒ the uniform (Born-counting) measure is stationary -/

/-- A column-stochastic kernel fixes the uniform measure: `π T = π` for `π ≡ 1/|Ω|`. With the envariance
fine-graining (`SelectionDynamics.born_from_uniform`, where uniform count = Born weight) this is the Born
measure as the stationary state. Applied to `inducedKernel` (`inducedKernel_col`), the Born measure is the
equilibrium forced by reversibility over a uniform bath. -/
theorem uniform_stationary_of_colStochastic (T : Ω → Ω → ℝ) (hcol : ∀ y, ∑ x, T x y = 1) (y : Ω) :
    push (fun _ => (1 : ℝ) / Fintype.card Ω) T y = 1 / Fintype.card Ω := by
  simp only [push]
  rw [← Finset.mul_sum, hcol y, mul_one]

end QIQTH.Relaxation
