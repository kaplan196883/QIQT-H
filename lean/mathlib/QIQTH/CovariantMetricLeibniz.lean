/-
  CovariantMetricLeibniz — the GENERAL covariant Leibniz rule for the metric pairing along a curve
  (Jacobi / first-variation Gauss-lemma infrastructure, sub-campaign start).

  `QIQTH.ParallelTransport.parallel_metricInner_const_at` proves that when TWO vector fields `e,f`
  along `γ` are PARALLEL (`∇_t e = ∇_t f = 0`), the metric pairing `⟨e,f⟩_g` is locally constant.
  This file GENERALIZES it to arbitrary covariant derivatives: writing the raw component derivatives
  as `e'ᵢ = Eᵢ − ∑ⱼₖ Γⁱⱼₖ(γτ)·γ'ⱼ·eₖ` and `f'ᵢ = Fᵢ − ∑ⱼₖ Γⁱⱼₖ(γτ)·γ'ⱼ·fₖ` (so `E = ∇_t e`,
  `F = ∇_t f` are the covariant derivatives), we prove the METRIC LEIBNIZ RULE

      `d/dτ ⟨e,f⟩_g = ⟨∇_t e, f⟩_g + ⟨e, ∇_t f⟩_g`,

  i.e. `d/dτ ∑_{ab} g_{ab}(γs) eₐ(s) f_b(s) = ∑_{ab} g_{ab}(γτ) Eₐ f_b + ∑_{ab} g_{ab}(γτ) eₐ F_b`.

  The proof is a controlled generalization of the parallel case: the connection terms hidden inside
  `∂g` (metric compatibility) cancel PAIRWISE (`sum4_swap14`/`sum4_swap24`) against the connection
  terms of `e'`,`f'` EXACTLY as in the parallel proof — these cancellations involve `e,f` only, not
  `E,F` — so the only surviving pieces are the two covariant-derivative pairings.  With `E = F = 0`
  this recovers `parallel_metricInner_const_at`.

  This is the metric-compatibility ENGINE for the abstract Jacobi / first-variation computation
  (per gpt-5.6-sol high scope assessment, 2026-08-22): it lets one differentiate `⟨γ', J⟩` along a
  geodesic using only the carried ODE hypotheses, WITHOUT any C¹-in-initial-condition information
  about the opaque Skolemized flow chart.  The corollary `metricPair_velocity_field_leibniz_at`
  specializes to a geodesic velocity `e = γ'` (`∇_t γ' = 0`), giving the first step of the Gauss
  lemma: `d/dτ ⟨γ', J⟩_g = ⟨γ', ∇_t J⟩_g`.

  HONEST SCOPE (what is NOT here): no Jacobi field EXISTS here (the field `J` and its covariant
  derivative `A = ∇_t J` are CARRIED as hypotheses, mirroring how `parallel_metricInner_const_at`
  carries the parallel fields as hypotheses rather than constructing them); no identification of `J`
  with `d(exp)` of a variation (that IS the C¹-in-IC wall this campaign is blocked on — the Jacobi
  approach RELOCATES rather than removes it); no Jacobi equation (`∇²_t J = −R(J,γ')γ'`); no Gauss
  lemma; no `a₁ = R/6`.  Only the metric Leibniz identity lands here.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.CovariantJacobi

namespace QIQTH.CovariantLeibniz

open QIQTH.Curvature QIQTH.ExpMap Finset

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### Finite reindexing helpers (pure `Finset.sum_comm` bookkeeping)

Re-declared here because the originals in `QIQTH.ParallelTransport` are `private`. -/

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

/-! ### The general covariant Leibniz rule -/

/-- **General covariant Leibniz rule for the metric pairing (pointwise at-`τ` form).**  Let `g` be a
    symmetric, invertible, `C¹` metric and `e,f` vector fields along `γ` whose raw component
    derivatives are `e'ᵢ = Eᵢ − ∑ⱼₖ Γⁱⱼₖ(γτ)γ'ⱼeₖ`, `f'ᵢ = Fᵢ − ∑ⱼₖ Γⁱⱼₖ(γτ)γ'ⱼfₖ` — so that
    `E = ∇_t e` and `F = ∇_t f` are the COVARIANT derivatives along `γ`.  Then the metric pairing
    `s ↦ ∑_{ab} g_{ab}(γ s)·eₐ(s)·f_b(s)` has derivative `⟨∇_t e, f⟩_g + ⟨e, ∇_t f⟩_g` at `τ`.

    Specializing `E = F = 0` recovers the parallel-transport isometry
    `parallel_metricInner_const_at`.  Every hypothesis is required only at the single base point `τ`,
    so this applies pointwise along a LOCALLY-existing curve/transport. -/
theorem metricPair_covariant_leibniz_at
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (γ γ' e e' f f' E F : ℝ → Point n) {τ : ℝ}
    (hinv : ∀ a b, (∑ σ, g (γ τ) a σ * gi (γ τ) σ b) = if a = b then 1 else 0)
    (hγ : HasDerivAt γ (γ' τ) τ)
    (he : ∀ i, HasDerivAt (fun s => e s i) (e' τ i) τ)
    (hf : ∀ i, HasDerivAt (fun s => f s i) (f' τ i) τ)
    (hE : ∀ i, e' τ i = E τ i - ∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * e τ k)
    (hF : ∀ i, f' τ i = F τ i - ∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * f τ k) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * e s a * f s b)
      ((∑ a, ∑ b, g (γ τ) a b * E τ a * f τ b)
        + (∑ a, ∑ b, g (γ τ) a b * e τ a * F τ b)) τ := by
  -- Metric compatibility, written as the `∂g` identity.
  have hpd : ∀ l a b, pd (fun y => g y a b) l (γ τ)
      = (∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b)
        + (∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ) := by
    intro l a b
    have h := metric_compat g gi hsymm (γ τ) hinv l a b
    simp only [covDeriv02] at h
    linarith
  -- Per-term derivative (chain rule along the curve + Leibniz).
  have hterm : ∀ a b, HasDerivAt (fun s => g (γ s) a b * e s a * f s b)
      (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b) τ := by
    intro a b
    have hG := hasDerivAt_comp_curve (fun y => g y a b) γ (γ' τ) τ (hg a b) hγ
    exact (hG.mul (he a)).mul (hf b)
  have hmain : HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * e s a * f s b)
      (∑ a, ∑ b, (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b)) τ := by
    apply HasDerivAt.fun_sum; intro a _
    apply HasDerivAt.fun_sum; intro b _
    exact hterm a b
  -- The assembled derivative equals the covariant-Leibniz value.
  have hval : (∑ a, ∑ b, (((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
        + g (γ τ) a b * e τ a * f' τ b))
      = ((∑ a, ∑ b, g (γ τ) a b * E τ a * f τ b)
          + (∑ a, ∑ b, g (γ τ) a b * e τ a * F τ b)) := by
    -- Per-`(a,b)` distribution of the substituted derivative.
    have hper : ∀ a b, ((∑ l, pd (fun y => g y a b) l (γ τ) * γ' τ l) * e τ a + g (γ τ) a b * e' τ a) * f τ b
          + g (γ τ) a b * e τ a * f' τ b
        = (∑ l, ∑ σ, christoffel g gi σ l a (γ τ) * g (γ τ) σ b * γ' τ l * e τ a * f τ b)
          + (∑ l, ∑ σ, christoffel g gi σ l b (γ τ) * g (γ τ) a σ * γ' τ l * e τ a * f τ b)
          + (g (γ τ) a b * E τ a * f τ b)
          + (g (γ τ) a b * e τ a * F τ b)
          - (∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b)
          - (∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k) := by
      intro a b
      simp only [hpd, hE, hF]
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
      have hpart2 : g (γ τ) a b * (E τ a - ∑ j, ∑ k, christoffel g gi a j k (γ τ) * γ' τ j * e τ k) * f τ b
          = g (γ τ) a b * E τ a * f τ b
            - ∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b := by
        rw [mul_sub, sub_mul]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro k _; ring
      have hpart3 : g (γ τ) a b * e τ a * (F τ b - ∑ j, ∑ k, christoffel g gi b j k (γ τ) * γ' τ j * f τ k)
          = g (γ τ) a b * e τ a * F τ b
            - ∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k := by
        rw [mul_sub]
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
            + (g (γ τ) a b * E τ a * f τ b)
            + (g (γ τ) a b * e τ a * F τ b)
            - (∑ j, ∑ k, g (γ τ) a b * christoffel g gi a j k (γ τ) * γ' τ j * e τ k * f τ b)
            - (∑ j, ∑ k, g (γ τ) a b * e τ a * christoffel g gi b j k (γ τ) * γ' τ j * f τ k)) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hper a b))
    rw [hrw]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- A = C (connection terms, involving `e,f` only — identical to the parallel proof)
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
  rwa [hval] at hmain

/-! ### Geodesic-velocity specialization — the first step of the Gauss-lemma computation -/

/-- **Metric Leibniz along a geodesic velocity.**  If `γ` is a geodesic (`γ''ᵢ = −∑ⱼₖ Γⁱⱼₖ(γτ)γ'ⱼγ'ₖ`,
    i.e. `∇_t γ' = 0`) and `J` is any vector field along `γ` with covariant derivative `A = ∇_t J`
    (`J'ᵢ = Aᵢ − ∑ⱼₖ Γⁱⱼₖ(γτ)γ'ⱼJₖ`), then

      `d/dτ ⟨γ', J⟩_g = ⟨γ', ∇_t J⟩_g`,

    i.e. `d/dτ ∑_{ab} g_{ab}(γ s) γ'ₐ(s) J_b(s) = ∑_{ab} g_{ab}(γτ) γ'ₐ A_b`.

    This is the FIRST step of the standard first-variation Gauss-lemma computation (the radial vector
    is the geodesic velocity `γ'`; the connection term for `e = γ'` drops out because `γ` is a
    geodesic). -/
theorem metricPair_velocity_field_leibniz_at
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (γ γ' γ'' J J' A : ℝ → Point n) {τ : ℝ}
    (hinv : ∀ a b, (∑ σ, g (γ τ) a σ * gi (γ τ) σ b) = if a = b then 1 else 0)
    (hγ : HasDerivAt γ (γ' τ) τ)
    (hv : ∀ i, HasDerivAt (fun s => γ' s i) (γ'' τ i) τ)
    (hJ : ∀ i, HasDerivAt (fun s => J s i) (J' τ i) τ)
    (hgeo : ∀ i, γ'' τ i = -∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * γ' τ k)
    (hJcov : ∀ i, J' τ i = A τ i - ∑ j, ∑ k, christoffel g gi i j k (γ τ) * γ' τ j * J τ k) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (γ s) a b * γ' s a * J s b)
      (∑ a, ∑ b, g (γ τ) a b * γ' τ a * A τ b) τ := by
  have h := metricPair_covariant_leibniz_at g gi hg hsymm γ γ' γ' γ'' J J'
      (fun _ => (0 : Point n)) A hinv hγ hv hJ
      (fun i => by simpa using hgeo i) hJcov
  simpa using h

end QIQTH.CovariantLeibniz
