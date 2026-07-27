/-
  ParallelTransport — the PARALLEL-TRANSPORT ISOMETRY (Phase M2b-1).

  MATRIX_JACOBI_PLAN.md, off-radial matrix-Jacobi campaign.  Parallel transport preserves the
  metric inner product: for two vector fields `e(τ), f(τ)` that are PARALLEL along a curve `γ(τ)`
  (their covariant derivative vanishes, `e'ᵢ = −∑_{jk} Γ^i_{jk}(γτ)·γ'ⱼ·eₖ`), the metric pairing

      `⟨e,f⟩_g(τ) := ∑_{ab} g_{ab}(γ τ)·eₐ(τ)·f_b(τ)`

  is (locally) constant: `d/dτ⟨e,f⟩_g = 0`.  Hence parallel transport is an ISOMETRY and an
  orthonormal frame stays orthonormal along the curve.

  Proof.  Product rule gives three groups —
    `∑_{ab}[(∑_l ∂_l g_{ab}·γ'_l) eₐ f_b] + ∑_{ab} g_{ab} e'ₐ f_b + ∑_{ab} g_{ab} eₐ f'_b`.
  Substitute metric compatibility `∂_l g_{ab} = ∑σ Γ^σ_{la} g_{σb} + ∑σ Γ^σ_{lb} g_{aσ}`
  (`QIQTH.Curvature.metric_compat`, via `covDeriv02 = 0`) and the parallel condition for `e'`,`f'`;
  the connection terms cancel PAIRWISE after a finite reindexing of the summation order
  (`sum4_swap14`, `sum4_swap24`, built from `Finset.sum_comm`).  Everything is ordinary
  differentiation (`hasDerivAt_comp_curve`, `HasDerivAt.mul`, `HasDerivAt.fun_sum`) plus Finset
  algebra — no curvature identification, no ODE solving.

  This is the FOUNDATION of the parallel-FRAME route to the clean matrix Jacobi equation
  `Ỹ'' = −R̃ Ỹ` (M2b): in a parallel orthonormal frame the covariant derivative is the ordinary
  derivative, so the covariant Jacobi equation trivialises to a matrix ODE.

  WHAT IS **NOT** HERE (honest scope):
    • no parallel-transport EXISTENCE — the frame ODE `e' = −Γ(γ)(γ',e)` is not solved (M2b-2);
      parallel `e,f` are carried as hypotheses `hep`/`hfp`, not constructed.
    • no expression of a Jacobi field IN the parallel frame (M2b-3).
    • no `Ỹ'' = −R̃ Ỹ` and no `tr R̃ = Ric` (M2b-3 / M2b-4).
    • no heat-kernel `a₁ = R/6` (M6).
  Only the isometry identity `d/dτ⟨e,f⟩_g = 0` lands here.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.CovariantJacobi

namespace QIQTH.ParallelTransport

open QIQTH.Curvature QIQTH.ExpMap Finset

variable {n : ℕ}

/-! ### Finite reindexing helpers (pure `Finset.sum_comm` bookkeeping) -/

/-- Reverse the outer/inner pair of a triple nested sum: `(a,b,c) ↦ (c,b,a)`. -/
private theorem sum3_swap13 (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [show (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c from
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_comm)

/-- Swap the outermost and innermost index of a 4-nested sum, keeping the middle two:
    `(a,b,c,d) ↦ (d,b,c,a)`. -/
private theorem sum4_swap14 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ b, ∑ c, ∑ a, f a b c d := by
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))]
  rw [show (∑ a, ∑ b, ∑ d, ∑ c, f a b c d) = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d from
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [show (∑ a, ∑ d, ∑ b, ∑ c, f a b c d) = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d from
        Finset.sum_comm]
  rw [show (∑ d, ∑ a, ∑ b, ∑ c, f a b c d) = ∑ d, ∑ b, ∑ a, ∑ c, f a b c d from
        Finset.sum_congr rfl (fun d _ => Finset.sum_comm)]
  exact Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun b _ => Finset.sum_comm))

/-- Swap the 2nd and 4th index of a 4-nested sum, keeping the 1st and 3rd:
    `(a,b,c,d) ↦ (a,d,c,b)`. -/
private theorem sum4_swap24 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ d, ∑ c, ∑ b, f a b c d :=
  Finset.sum_congr rfl (fun a _ => sum3_swap13 (fun b c d => f a b c d))

/-! ### The parallel-transport isometry -/

/-- **Parallel transport preserves the metric inner product.**  If `e,f` are parallel vector fields
    along `γ` (covariant derivative zero, `hep`/`hfp`) for a symmetric, invertible, `C¹` metric `g`,
    then `s ↦ ∑_{ab} g_{ab}(γ s)·eₐ(s)·f_b(s)` has derivative `0` at every `τ` — the pairing is
    locally constant.  The connection terms from `∂g` (metric compatibility) cancel pairwise against
    the connection terms from `e'`,`f'` (the parallel condition). -/
theorem parallel_metricInner_const
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (γ γ' e e' f f' : ℝ → Point n)
    (hinv : ∀ τ a b, (∑ σ, g (γ τ) a σ * gi (γ τ) σ b) = if a = b then 1 else 0)
    (hγ : ∀ τ, HasDerivAt γ (γ' τ) τ)
    (he : ∀ τ i, HasDerivAt (fun s => e s i) (e' τ i) τ)
    (hf : ∀ τ i, HasDerivAt (fun s => f s i) (f' τ i) τ)
    (hep : ∀ τ i, e' τ i = -∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * e τ k)
    (hfp : ∀ τ i, f' τ i = -∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * f τ k)
    (τ : ℝ) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * e s a * f s b) 0 τ := by
  -- Metric compatibility, written as the `∂g` identity `∂_l g_{ab} = ∑σ Γ^σ_{la}g_{σb}+∑σ Γ^σ_{lb}g_{aσ}`.
  have hpd : ∀ l a b, pd (fun y => g y a b) l (γ τ)
      = (∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b)
        + (∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ) := by
    intro l a b
    have h := metric_compat g gi hsymm (γ τ) (hinv τ) l a b
    simp only [covDeriv02] at h
    linarith
  -- Per-term derivative (chain rule along the curve + Leibniz).
  have hterm : ∀ a b, HasDerivAt (fun s => g (γ s) a b * e s a * f s b)
      (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b) τ := by
    intro a b
    have hG := hasDerivAt_comp_curve (fun y => g y a b) γ (γ' τ) τ (hg a b) (hγ τ)
    exact (hG.mul (he τ a)).mul (hf τ b)
  have hmain : HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * e s a * f s b)
      (∑ a, ∑ b, (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b)) τ := by
    apply HasDerivAt.fun_sum; intro a _
    apply HasDerivAt.fun_sum; intro b _
    exact hterm a b
  -- The assembled derivative is zero.
  have hzero : (∑ a, ∑ b, (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b)) = 0 := by
    -- Per-`(a,b)` distribution of the substituted derivative into four grouped double sums.
    have hper : ∀ a b, ((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
          + g (γ τ) a b * e τ a * f' τ b
        = (∑ l, ∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)
          + (∑ l, ∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b)
          - (∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b)
          - (∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k) := by
      intro a b
      simp only [hpd, hep, hfp]
      -- three pieces
      have hpart1 : (∑ l, ((∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b)
              + (∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ)) * γ' τ l) * e τ a * f τ b
          = (∑ l, ∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)
            + (∑ l, ∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        rw [add_mul, add_mul, add_mul]
        congr 1
        · rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        · rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      have hpart2 : g (γ τ) a b * (-∑ j, ∑ k, christoffel g gi a j k (γ τ) * γ' τ j * e τ k) * f τ b
          = -∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b := by
        rw [mul_neg, neg_mul]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k _; ring
      have hpart3 : g (γ τ) a b * e τ a * (-∑ j, ∑ k, christoffel g gi b j k (γ τ) * γ' τ j * f τ k)
          = -∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k := by
        rw [mul_neg]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [add_mul, hpart1, hpart2, hpart3]; ring
    -- rewrite the summand, split the outer sums, cancel via reindexing.
    have hrw : (∑ a, ∑ b, (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
          + g (γ τ) a b * e τ a * f' τ b))
        = ∑ a, ∑ b, ((∑ l, ∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)
            + (∑ l, ∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b)
            - (∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b)
            - (∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k)) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hper a b))
    rw [hrw]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- A = C
    have hAC : (∑ a, ∑ b, ∑ l, ∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)
        = (∑ a, ∑ b, ∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b) := by
      rw [sum4_swap14 (fun a b l σ =>
            christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)]
      refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))))
      ring
    -- B = D
    have hBD : (∑ a, ∑ b, ∑ l, ∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b)
        = (∑ a, ∑ b, ∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k) := by
      rw [sum4_swap24 (fun a b l σ =>
            christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b)]
      refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun x _ =>
        Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))))
      ring
    rw [hAC, hBD]; ring
  rwa [hzero] at hmain

end QIQTH.ParallelTransport
