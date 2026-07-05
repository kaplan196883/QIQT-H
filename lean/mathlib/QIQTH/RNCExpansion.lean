/-
  RNCExpansion — the `√det g` atom of the Riemann-normal-coordinate second-order expansion.

  RNC1 of THE_RNC_EXPANSION_PLAN.md.  Component-level, in a fixed coordinate chart
  `Point n = Fin n → ℝ`, on the `pd` calculus of `QIQTH/Curvature.lean`.

  RESULT (this file): at the origin, with `g_{ab}(0)=δ_{ab}` (`hg0`), `∂g(0)=0` (`hdg0`), and the
  CARRIED metric-Hessian-trace datum `tr ∂∂g(0) = −⅔ Ric` (`htr`), the second derivative of `√det g`
  is `∂_c∂_d √det g (0) = −⅓ Ric_{cd}`, equivalently the Taylor COEFFICIENT (half the second
  derivative) is `−⅙ Ric_{cd}`, i.e. `√det g = 1 − ⅙ R_{cd} x^c x^d`.  The `⅙` is the source of the
  `κ = 1/6` conformal factor.

  HONEST CAPTION (binding): this is CONDITIONAL on the carried `htr : tr ∂∂g(0) = −⅔ Ric` (a genuine
  equation on `pd (pd g)`, load-bearing — remove it and the `−⅙R` conclusion is false).  RNC3 later
  discharges `htr` from the radial/normal gauge.  It does NOT give the numerical value of G (species
  count N, granularity scale Λ_s, the E/ξ heat-kernel term remain), and does NOT build a curved heat
  kernel.  The `⅙` normalization only.
-/
import Mathlib
import QIQTH.Curvature

namespace QIQTH.RNCExpansion

open QIQTH.Curvature
open Finset Matrix

variable {n : ℕ}

/-! ### Infrastructure: `pd` congruence, product `ContDiff`, finite-product Leibniz -/

/-- **Local congruence for `pd`.** Two fields agreeing on a neighborhood of `x` have equal partial
    derivatives there — `pd` sees only the germ (via `deriv` of the coordinate restriction). -/
theorem pd_congr {f h : Point n → ℝ} (i : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) : pd f i x = pd h i x := by
  simp only [pd]
  apply Filter.EventuallyEq.deriv_eq
  have htend : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
    have hc := (hasDerivAt_update x i (x i)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact htend.eventually hfh

/-- A finite product of `C^∞` fields is `C^∞`. -/
theorem contDiff_prod {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ)
    (hF : ∀ i ∈ s, ContDiff ℝ ⊤ (fun y => F i y)) :
    ContDiff ℝ ⊤ (fun y => ∏ i ∈ s, F i y) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact contDiff_const
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- **Finite-product Leibniz for `pd`** — `∂_c ∏_{i∈s} F i = ∑_{i∈s} (∂_c F i) · ∏_{j∈s\{i}} F j`.
    (`C^∞` factors give all the differentiability side-conditions.) -/
theorem pd_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → Point n → ℝ)
    (c : Fin n) (x : Point n)
    (hF : ∀ i ∈ s, ContDiff ℝ ⊤ (fun y => F i y)) :
    pd (fun y => ∏ i ∈ s, F i y) c x
      = ∑ i ∈ s, pd (F i) c x * ∏ j ∈ s.erase i, F j x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact pd_const 1 c x
  | insert a s ha ih =>
      have hFa : PdiffAt (F a) c x :=
        PdiffAt_of_contDiff _ (hF a (Finset.mem_insert_self a s)) c x
      have hFs : ∀ i ∈ s, ContDiff ℝ ⊤ (fun y => F i y) :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hprod : PdiffAt (fun y => ∏ i ∈ s, F i y) c x :=
        PdiffAt_of_contDiff _ (contDiff_prod s F hFs) c x
      simp only [Finset.prod_insert ha]
      rw [pd_mul (F a) (fun y => ∏ i ∈ s, F i y) c x hFa hprod, ih hFs,
          Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      -- the i=a product terms are syntactically equal; match the i∈s terms
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert (by
            simp only [Finset.mem_erase]; exact fun h => ha h.2)]
      ring

/-! ### The `√` chain rule at a critical point -/

/-- First-order chain rule for `√ ∘ F` where `F ≠ 0`: `∂_i √F = (∂_i F)/(2√F)`. -/
theorem pd_comp_sqrt (F : Point n → ℝ) (i : Fin n) (x : Point n)
    (hF : PdiffAt F i x) (hne : F x ≠ 0) :
    pd (fun y => Real.sqrt (F y)) i x = (1 / (2 * Real.sqrt (F x))) * pd F i x := by
  simp only [pd]
  have hval : F (Function.update x i (x i)) = F x := by rw [Function.update_eq_self]
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (F x)))
      (F (Function.update x i (x i))) := by rw [hval]; exact Real.hasDerivAt_sqrt hne
  have hcomp := hsqrt.comp (x i) hF.hasDerivAt
  exact hcomp.deriv

/-- **Second derivative of `√ ∘ F` at a critical point** where `F = 1` and `∂F = 0`:
    `∂_c∂_d √F = ½ ∂_c∂_d F`.  (The cross term `(∂F)²·…` drops because `∂F(x)=0`; the `½` is
    `1/(2√F(x)) = 1/2`.) -/
theorem sqrt_pd_pd (F : Point n → ℝ) (c d : Fin n) (x : Point n)
    (hF : ContDiff ℝ ⊤ F) (hval : F x = 1) (hcrit : ∀ e, pd F e x = 0) :
    pd (fun y => pd (fun w => Real.sqrt (F w)) d y) c x
      = (1 / 2) * pd (fun y => pd F d y) c x := by
  have hne : F x ≠ 0 := by rw [hval]; norm_num
  have hcont : Continuous F := hF.continuous
  have hnhds : ∀ᶠ y in nhds x, F y ≠ 0 :=
    hcont.continuousAt.eventually_ne hne
  -- the chain rule holds eventually near x
  have hchain : (fun y => pd (fun w => Real.sqrt (F w)) d y)
      =ᶠ[nhds x] (fun y => (1 / (2 * Real.sqrt (F y))) * pd F d y) := by
    filter_upwards [hnhds] with y hy
    exact pd_comp_sqrt F d y (PdiffAt_of_contDiff F hF d y) hy
  rw [pd_congr c x hchain]
  -- differentiability of the two factors
  have hB : PdiffAt (fun y => pd F d y) c x := PdiffAt_pd F hF d c x
  have hγd : DifferentiableAt ℝ (fun t => F (Function.update x c t)) (x c) :=
    PdiffAt_of_contDiff F hF c x
  have hFxc : F (Function.update x c (x c)) = F x := by rw [Function.update_eq_self]
  have hsqrtd : DifferentiableAt ℝ Real.sqrt (F (Function.update x c (x c))) := by
    rw [hFxc]; exact (Real.hasDerivAt_sqrt hne).differentiableAt
  have hcompd : DifferentiableAt ℝ (fun t => Real.sqrt (F (Function.update x c t))) (x c) :=
    hsqrtd.comp (x c) hγd
  have hden : DifferentiableAt ℝ (fun t => 2 * Real.sqrt (F (Function.update x c t))) (x c) :=
    (differentiableAt_const 2).mul hcompd
  have hdenne : (2 : ℝ) * Real.sqrt (F (Function.update x c (x c))) ≠ 0 := by
    rw [hFxc, hval, Real.sqrt_one]; norm_num
  have hA : PdiffAt (fun y => 1 / (2 * Real.sqrt (F y))) c x := by
    show DifferentiableAt ℝ (fun t => 1 / (2 * Real.sqrt (F (Function.update x c t)))) (x c)
    simp only [one_div]
    exact hden.inv hdenne
  rw [pd_mul (fun y => 1 / (2 * Real.sqrt (F y))) (fun y => pd F d y) c x hA hB]
  have hBx : pd F d x = 0 := hcrit d
  have hAx : (1 : ℝ) / (2 * Real.sqrt (F x)) = 1 / 2 := by
    rw [hval, Real.sqrt_one]; norm_num
  rw [hBx, mul_zero, zero_add, hAx]

/-! ### The determinant atom -/

/-- `∂ᵢ(c·f) = c·∂ᵢf` at the level of partial differentiability closure. -/
theorem PdiffAt_const_mul (c : ℝ) (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) : PdiffAt (fun y => c * f y) i x :=
  (differentiableAt_const c).mul hf

/-- `F = det ∘ g` is `C^∞` when the metric components are. -/
theorem det_contDiff (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b)) :
    ContDiff ℝ ⊤ (fun y => Matrix.det (g y)) := by
  rw [show (fun y => Matrix.det (g y))
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g y (σ i) i)
      from funext (fun y => Matrix.det_apply' _)]
  apply ContDiff.sum
  intro σ _
  exact contDiff_const.mul (contDiff_prod _ (fun i y => g y (σ i) i) (fun i _ => hg (σ i) i))

/-- **First derivative of `det g`, permutation-sum + product-Leibniz form.** -/
theorem pd_det (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b)) (d : Fin n) (y : Point n) :
    pd (fun w => Matrix.det (g w)) d y
      = ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
          * ∑ k, pd (fun w => g w (σ k) k) d y * ∏ i ∈ univ.erase k, g y (σ i) i := by
  rw [show (fun w => Matrix.det (g w))
        = (fun w => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g w (σ i) i)
      from funext (fun w => Matrix.det_apply' _)]
  rw [pd_sum univ _ d y (fun σ _ => PdiffAt_const_mul _ _ d y
        (PdiffAt_of_contDiff _ (contDiff_prod _ (fun i w => g w (σ i) i)
          (fun i _ => hg (σ i) i)) d y))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pd_const_mul _ _ d y (PdiffAt_of_contDiff _
        (contDiff_prod _ (fun i w => g w (σ i) i) (fun i _ => hg (σ i) i)) d y),
      pd_prod univ (fun i w => g w (σ i) i) d y (fun i _ => hg (σ i) i)]

/-- **The first derivative of `det g` vanishes at the origin** where `∂g(0)=0`. -/
theorem det_pd_first (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (e : Fin n) :
    pd (fun w => Matrix.det (g w)) e 0 = 0 := by
  rw [pd_det g hg e 0]
  apply Finset.sum_eq_zero
  intro σ _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k _
  rw [hdg0 (σ k) k e, zero_mul]

/-- **Second derivative of `det g` at the origin, expanded** — the cross Leibniz terms drop because
    `∂g(0)=0`, leaving `∑_σ sgn σ ∑_k ∂_c∂_d g_{σk,k}(0) · ∏_{i≠k} g_{σi,i}(0)`. -/
theorem det_pd_pd_expand (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (c d : Fin n) :
    pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
          * ∑ k, pd (fun y => pd (fun w => g w (σ k) k) d y) c 0
              * ∏ i ∈ univ.erase k, g 0 (σ i) i := by
  rw [show (fun y => pd (fun w => Matrix.det (g w)) d y)
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
            * ∑ k, pd (fun w => g w (σ k) k) d y * ∏ i ∈ univ.erase k, g y (σ i) i)
      from funext (fun y => pd_det g hg d y)]
  rw [pd_sum univ _ c 0 (fun σ _ => PdiffAt_const_mul _ _ c 0
        (PdiffAt_sum univ _ c 0 (fun k _ =>
          (PdiffAt_pd (fun w => g w (σ k) k) (hg (σ k) k) d c 0).mul
          (PdiffAt_of_contDiff _ (contDiff_prod _ (fun i y => g y (σ i) i)
            (fun i _ => hg (σ i) i)) c 0))))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pd_const_mul _ _ c 0 (PdiffAt_sum univ _ c 0 (fun k _ =>
        (PdiffAt_pd (fun w => g w (σ k) k) (hg (σ k) k) d c 0).mul
        (PdiffAt_of_contDiff _ (contDiff_prod _ (fun i y => g y (σ i) i)
          (fun i _ => hg (σ i) i)) c 0)))]
  congr 1
  rw [pd_sum univ _ c 0 (fun k _ =>
        (PdiffAt_pd (fun w => g w (σ k) k) (hg (σ k) k) d c 0).mul
        (PdiffAt_of_contDiff _ (contDiff_prod _ (fun i y => g y (σ i) i)
          (fun i _ => hg (σ i) i)) c 0))]
  apply Finset.sum_congr rfl
  intro k _
  rw [pd_mul (fun y => pd (fun w => g w (σ k) k) d y)
        (fun y => ∏ i ∈ univ.erase k, g y (σ i) i) c 0
        (PdiffAt_pd (fun w => g w (σ k) k) (hg (σ k) k) d c 0)
        (PdiffAt_of_contDiff _ (contDiff_prod _ (fun i y => g y (σ i) i)
          (fun i _ => hg (σ i) i)) c 0)]
  simp only [hdg0 (σ k) k d, zero_mul, add_zero]

/-- For `σ ≠ 1`, some point `i ≠ k` is moved by `σ` — the fact that kills the off-diagonal
    permutation products at the identity metric. -/
theorem perm_moves_in_erase (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (k : Fin n) :
    ∃ i ∈ univ.erase k, σ i ≠ i := by
  have hex : ∃ x, σ x ≠ x := by
    by_contra hc
    exact hσ (Equiv.ext (fun x => not_not.mp (fun h => hc ⟨x, h⟩)))
  obtain ⟨x0, hx0⟩ := hex
  by_cases hxk : x0 = k
  · have hk : σ k ≠ k := hxk ▸ hx0
    have hinv : σ (σ⁻¹ k) = k := by simp
    have hik : σ⁻¹ k ≠ k := by
      intro h
      apply hk
      conv_lhs => rw [← h]
      exact hinv
    refine ⟨σ⁻¹ k, ?_, ?_⟩
    · rw [Finset.mem_erase]; exact ⟨hik, Finset.mem_univ _⟩
    · rw [hinv]; exact fun h => hik h.symm
  · exact ⟨x0, by rw [Finset.mem_erase]; exact ⟨hxk, Finset.mem_univ _⟩, hx0⟩

/-- **RNC1 — the `√det g` atom.**  At the origin, with `g_{ab}(0)=δ_{ab}` (`hg0`), `∂g(0)=0` (`hdg0`),
    and the CARRIED metric-Hessian-trace datum `∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}` (`htr`), the
    second partial derivative of `√det g` at the origin is `−⅓ Ric_{cd}`.  (The Taylor COEFFICIENT,
    i.e. half of this, is `−⅙ Ric_{cd}` — the source of `κ = 1/6`; see `sqrtdet_taylor_coeff`.)

    LOAD-BEARING: `htr` is a genuine equation on `pd (pd g)`; remove it and `−⅓ Ric` is false.
    RNC3 later discharges `htr` from the radial/normal gauge.  This is the `⅙` normalization ONLY —
    NOT numerical-G (N, Λ_s, E/ξ remain), NOT a curved heat kernel. -/
theorem sqrtdet_pd_pd (g : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (c d : Fin n) :
    pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0 = -(1 / 3) * Ric c d := by
  have hFcd : ContDiff ℝ ⊤ (fun y => Matrix.det (g y)) := det_contDiff g hg
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hF0 : (fun y => Matrix.det (g y)) 0 = 1 := by show Matrix.det (g 0) = 1; rw [hg0mat, Matrix.det_one]
  have hcrit : ∀ e, pd (fun y => Matrix.det (g y)) e 0 = 0 := fun e => det_pd_first g hg hdg0 e
  -- the second derivative of det collapses to the trace of the metric Hessian
  have hdet2 : pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
    rw [det_pd_pd_expand g hg hdg0 c d,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · -- σ = 1 term
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.prod_eq_one (fun i _ => by rw [hg0 i i]; exact Matrix.one_apply_eq i), mul_one]
    · -- σ ≠ 1 terms vanish
      intro σ _ hσ
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro k _
      apply mul_eq_zero_of_right
      obtain ⟨i0, hi0mem, hi0⟩ := perm_moves_in_erase σ hσ k
      exact Finset.prod_eq_zero hi0mem (by rw [hg0 (σ i0) i0]; exact Matrix.one_apply_ne hi0)
    · intro h; exact absurd (Finset.mem_univ _) h
  -- assemble with the √ Taylor factor and the carried htr
  have key := sqrt_pd_pd (fun y => Matrix.det (g y)) c d 0 hFcd hF0 hcrit
  rw [hdet2, htr c d] at key
  rw [show (1 : ℝ) / 2 * (-(2 / 3) * Ric c d) = -(1 / 3) * Ric c d from by ring] at key
  exact key

/-- **RNC1 corollary — the `⅙` Taylor coefficient.**  Half the second derivative is the quadratic
    Taylor coefficient of `√det g`: `½ ∂_c∂_d √det g (0) = −⅙ Ric_{cd}`, i.e.
    `√det g = 1 − ⅙ R_{cd} x^c x^d`.  This is where the `κ = 1/6` conformal factor comes from.
    CONDITIONAL on the carried `htr` (discharged by RNC3); NOT numerical-G, NOT a curved heat kernel. -/
theorem sqrtdet_taylor_coeff (g : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (c d : Fin n) :
    (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0 = -(1 / 6) * Ric c d := by
  rw [sqrtdet_pd_pd g Ric hg hg0 hdg0 htr c d]; ring

end QIQTH.RNCExpansion
