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
import QIQTH.HeatKernelA1

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

/-! ### RNC2 / RNC3 — the curvature ↔ metric-Hessian bridge and the normal-coordinate gauge

    RNC2 (`rnc_riemann_hessian`): the forward local-inertial formula
    `R_{ρσμν}(0) = ½(∂_μ∂_σ g_{ρν} − ∂_μ∂_ρ g_{νσ} − ∂_ν∂_σ g_{ρμ} + ∂_ν∂_ρ g_{μσ})(0)`,
    from `g(0)=δ`, `∂g(0)=0` (so `Γ(0)=0`).  RNC3 (`rnc_htr_of_gauge`): carrying the
    **normal-coordinate gauge** `∂_{(a}Γ^i_{bc)}(0)=0` (a falsifiable christoffel-symmetrization
    condition), the metric-Hessian trace is forced, `tr ∂∂g(0) = −⅔ Ric` — EXACTLY RNC1's carried
    `htr`, now DERIVED from the gauge.  Removing the gauge makes the `−⅔Ric` conclusion false (the
    symmetric part of `∂∂g` re-enters the trace); the gauge is genuinely load-bearing. -/

/-- **The Christoffel symbols vanish at the origin** where `∂g(0)=0`.  Immediate from the definition:
    every `∂g` entering `Γ` is zero at `0`. -/
theorem christoffel_zero_at_origin (g gi : Point n → Fin n → Fin n → ℝ)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (ρ μ σ : Fin n) :
    christoffel g gi ρ μ σ 0 = 0 := by
  simp only [christoffel]
  rw [Finset.sum_eq_zero (fun α _ => by rw [hdg0 α σ μ, hdg0 α μ σ, hdg0 μ σ α]; ring)]
  ring

/-- **The Riemann tensor at the origin drops its `ΓΓ` part** (`Γ(0)=0`), leaving the derivative part
    `R^ρ_{σμν}(0) = ∂_μ Γ^ρ_{νσ}(0) − ∂_ν Γ^ρ_{μσ}(0)`. -/
theorem riemann_at_origin (g gi : Point n → Fin n → Fin n → ℝ)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν 0
      = pd (fun y => christoffel g gi ρ ν σ y) μ 0
        - pd (fun y => christoffel g gi ρ μ σ y) ν 0 := by
  simp only [riemann]
  rw [Finset.sum_eq_zero (fun l _ => by
        rw [christoffel_zero_at_origin g gi hdg0 l ν σ,
            christoffel_zero_at_origin g gi hdg0 l μ σ]; ring), add_zero]

/-- **The Christoffel derivative at the origin in terms of the metric Hessian.**  With `g(0)=δ`
    (via `gi(0)=δ`) and `∂g(0)=0`, the `(∂gi)·(∂g)` term drops (the `∂g` bracket vanishes at `0`) and
    the inverse metric collapses to `δ`, giving
    `∂_a Γ^ν_{λμ}(0) = ½(∂_a∂_λ g_{νμ} + ∂_a∂_μ g_{νλ} − ∂_a∂_ν g_{λμ})(0)`. -/
theorem pd_christoffel_origin (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (ν lam mu a : Fin n) :
    pd (fun y => christoffel g gi ν lam mu y) a 0
      = (1 / 2) * (pd (fun y => pd (fun w => g w ν mu) lam y) a 0
                   + pd (fun y => pd (fun w => g w ν lam) mu y) a 0
                   - pd (fun y => pd (fun w => g w lam mu) ν y) a 0) := by
  have hBP : ∀ α, PdiffAt (fun y => pd (fun w => g w α mu) lam y
      + pd (fun w => g w α lam) mu y - pd (fun w => g w lam mu) α y) a 0 := fun α =>
    ((PdiffAt_pd (fun w => g w α mu) (hg α mu) lam a 0).add
      (PdiffAt_pd (fun w => g w α lam) (hg α lam) mu a 0)).sub
      (PdiffAt_pd (fun w => g w lam mu) (hg lam mu) α a 0)
  have hgiP : ∀ α, PdiffAt (fun y => gi y ν α) a 0 := fun α => PdiffAt_of_contDiff _ (hgi ν α) a 0
  have hsummand : ∀ α, pd (fun y => gi y ν α * (pd (fun w => g w α mu) lam y
        + pd (fun w => g w α lam) mu y - pd (fun w => g w lam mu) α y)) a 0
      = gi 0 ν α * (pd (fun y => pd (fun w => g w α mu) lam y) a 0
          + pd (fun y => pd (fun w => g w α lam) mu y) a 0
          - pd (fun y => pd (fun w => g w lam mu) α y) a 0) := by
    intro α
    rw [pd_mul (fun y => gi y ν α) _ a 0 (hgiP α) (hBP α),
        pd_sub _ _ a 0 ((PdiffAt_pd (fun w => g w α mu) (hg α mu) lam a 0).add
          (PdiffAt_pd (fun w => g w α lam) (hg α lam) mu a 0))
          (PdiffAt_pd (fun w => g w lam mu) (hg lam mu) α a 0),
        pd_add _ _ a 0 (PdiffAt_pd (fun w => g w α mu) (hg α mu) lam a 0)
          (PdiffAt_pd (fun w => g w α lam) (hg α lam) mu a 0)]
    simp only [hdg0 α mu lam, hdg0 α lam mu, hdg0 lam mu α]
    ring
  simp only [christoffel]
  rw [pd_const_mul _ _ a 0 (PdiffAt_sum univ _ a 0 (fun α _ => (hgiP α).mul (hBP α))),
      pd_sum univ _ a 0 (fun α _ => (hgiP α).mul (hBP α)),
      Finset.sum_congr rfl (fun α _ => hsummand α)]
  simp only [hgi0, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- **RNC2 — the forward local-inertial Riemann formula.**  At a normal-coordinate origin
    (`g(0)=δ`, `∂g(0)=0`), the Riemann tensor is the antisymmetrized metric Hessian:
    `R^ρ_{σμν}(0) = ½(∂_μ∂_σ g_{ρν} − ∂_μ∂_ρ g_{νσ} − ∂_ν∂_σ g_{ρμ} + ∂_ν∂_ρ g_{μσ})(0)`.
    (The symmetric `∂_μ∂_ν g_{ρσ}` piece cancels via Schwarz.)  Connects the curvature tower to the
    metric-Hessian bridge feeding RNC3. -/
theorem rnc_riemann_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν 0
      = (1 / 2) * (pd (fun y => pd (fun w => g w ρ ν) σ y) μ 0
                 - pd (fun y => pd (fun w => g w ν σ) ρ y) μ 0
                 - pd (fun y => pd (fun w => g w ρ μ) σ y) ν 0
                 + pd (fun y => pd (fun w => g w μ σ) ρ y) ν 0) := by
  rw [riemann_at_origin g gi hdg0 ρ σ μ ν,
      pd_christoffel_origin g gi hg hgi hgi0 hdg0 ρ ν σ μ,
      pd_christoffel_origin g gi hg hgi hgi0 hdg0 ρ μ σ ν,
      pd_comm (fun w => g w ρ σ) μ ν 0 (hg ρ σ)]
  ring

/-- **The trace of the Christoffel derivative equals half the metric-Hessian trace** (a pure-calculus
    identity, no gauge): `∑_ν ∂_c Γ^ν_{νd}(0) = ½ ∑_a ∂_c∂_d g_{aa}(0)`.  In `∂_c Γ^ν_{νd}` the two
    `∂∂g` terms carrying the contracted index cancel identically, leaving `½ ∂_c∂_d g_{νν}`. -/
theorem sum_pd_christoffel_trace (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (c d : Fin n) :
    (∑ ν, pd (fun y => christoffel g gi ν ν d y) c 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [pd_christoffel_origin g gi hg hgi hgi0 hdg0 ν ν d c]
  ring

/-- **The normal-coordinate inversion (the `−⅓`).**  Combining the origin Riemann formula
    `R^i_{jkl}(0) = ∂_kΓ^i_{lj} − ∂_lΓ^i_{kj}` with the carried normal-coordinate gauge
    `∂_{(a}Γ^i_{bc)}(0)=0`, the finite antisymmetrize-vs-symmetrize system solves to
    `∂_a Γ^i_{bc}(0) = ⅓(R^i_{bac}(0) + R^i_{cab}(0))`.  This is where the gauge becomes load-bearing —
    it fixes the totally-symmetric part of `∂Γ`. -/
theorem pd_christoffel_solve (g gi : Point n → Fin n → Fin n → ℝ)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (i a b c : Fin n) :
    pd (fun y => christoffel g gi i b c y) a 0
      = (1 / 3) * (riemann g gi i b a c 0 + riemann g gi i c a b 0) := by
  have ro1 := riemann_at_origin g gi hdg0 i b a c
  have ro2 := riemann_at_origin g gi hdg0 i c a b
  have gauge := hgauge i a b c
  have symcb : pd (fun y => christoffel g gi i c b y) a 0
      = pd (fun y => christoffel g gi i b c y) a 0 := by
    rw [show (fun y => christoffel g gi i c b y) = (fun y => christoffel g gi i b c y) from
      funext (fun y => christoffel_symm g gi hsymm i c b y)]
  have symac : pd (fun y => christoffel g gi i a c y) b 0
      = pd (fun y => christoffel g gi i c a y) b 0 := by
    rw [show (fun y => christoffel g gi i a c y) = (fun y => christoffel g gi i c a y) from
      funext (fun y => christoffel_symm g gi hsymm i a c y)]
  linarith [ro1, ro2, gauge, symcb, symac]

/-- **The first-pair contraction of the origin Riemann tensor vanishes** (antisymmetry, gauge-free):
    `∑_ν R^ν_{νcd}(0) = 0`.  Both `∂_cΓ^ν_{dν}` and `∂_dΓ^ν_{cν}` contract to `½ tr ∂∂g`, and the
    difference cancels (Schwarz). -/
theorem sum_riemann_ii_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (c d : Fin n) :
    (∑ ν, riemann g gi ν ν c d 0) = 0 := by
  have hL : (∑ ν, pd (fun y => christoffel g gi ν d ν y) c 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
    rw [show (∑ ν, pd (fun y => christoffel g gi ν d ν y) c 0)
          = ∑ ν, pd (fun y => christoffel g gi ν ν d y) c 0 from
        Finset.sum_congr rfl (fun ν _ => by
          rw [show (fun y => christoffel g gi ν d ν y) = (fun y => christoffel g gi ν ν d y) from
            funext (fun y => christoffel_symm g gi hsymm ν d ν y)])]
    exact sum_pd_christoffel_trace g gi hg hgi hgi0 hdg0 c d
  have hR : (∑ ν, pd (fun y => christoffel g gi ν c ν y) d 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0 := by
    rw [show (∑ ν, pd (fun y => christoffel g gi ν c ν y) d 0)
          = ∑ ν, pd (fun y => christoffel g gi ν ν c y) d 0 from
        Finset.sum_congr rfl (fun ν _ => by
          rw [show (fun y => christoffel g gi ν c ν y) = (fun y => christoffel g gi ν ν c y) from
            funext (fun y => christoffel_symm g gi hsymm ν c ν y)])]
    exact sum_pd_christoffel_trace g gi hg hgi hgi0 hdg0 d c
  have hswap : (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0)
      = (∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0) :=
    Finset.sum_congr rfl (fun a _ => pd_comm (fun w => g w a a) c d 0 (hg a a))
  rw [Finset.sum_congr rfl (fun ν _ => riemann_at_origin g gi hdg0 ν ν c d),
      Finset.sum_sub_distrib, hL, hR, hswap]
  ring

/-- **RNC3 — the normal-coordinate gauge discharges the metric-Hessian trace `htr`.**  Carrying the
    falsifiable NORMAL-COORDINATE GAUGE `hgauge : ∂_{(a}Γ^i_{bc)}(0)=0` (the totally-symmetrized
    Christoffel derivative vanishes at the origin), together with `g(0)=δ`/`gi(0)=δ`, `∂g(0)=0`, the
    metric-Hessian trace is FORCED to `tr ∂∂g(0) = −⅔ Ric` — EXACTLY the datum RNC1 carried as `htr`.

    LOAD-BEARING (sharp test): the gauge is a genuine christoffel-symmetrization equation, NOT a
    pre-contracted `∂∂g=−⅓(R+R)`.  Remove `hgauge` and `∑_ν ∂_cΓ^ν_{νd}` is no longer `−⅓Ric` (the
    symmetric/trace part of `∂∂g` is unconstrained), so the `−⅔Ric` conclusion becomes false.  Route:
    `∑_ν ∂_cΓ^ν_{νd}` equals BOTH `½ tr∂∂g` (calculus, `sum_pd_christoffel_trace`) AND `−⅓Ric` (gauge,
    `pd_christoffel_solve` + antisymmetry) — combining gives `tr∂∂g = −⅔Ric`.  Discharges RNC1's `htr`;
    still the `⅙` normalization ONLY — NOT numerical-G, NOT a curved heat kernel. -/
theorem rnc_htr_of_gauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * ricci g gi c d 0 := by
  have key : ∀ p q : Fin n,
      (∑ a, pd (fun y => pd (fun w => g w a a) q y) p 0) = -(2 / 3) * ricci g gi q p 0 := by
    intro p q
    have hc1 := sum_pd_christoffel_trace g gi hg hgi hgi0 hdg0 p q
    have hsolve : (∑ ν, pd (fun y => christoffel g gi ν ν q y) p 0)
        = (1 / 3) * ((∑ ν, riemann g gi ν ν p q 0) + (∑ ν, riemann g gi ν q p ν 0)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ν _ => by
        rw [pd_christoffel_solve g gi hdg0 hsymm hgauge ν p ν q]; ring)
    have h2a := sum_riemann_ii_zero g gi hg hgi hgi0 hdg0 hsymm p q
    have h2b : (∑ ν, riemann g gi ν q p ν 0) = - ricci g gi q p 0 := by
      rw [show (∑ ν, riemann g gi ν q p ν 0) = ∑ ν, (-1 : ℝ) * riemann g gi ν q ν p 0 from
            Finset.sum_congr rfl (fun ν _ => by rw [riemann_antisymm g gi ν q p ν 0]; ring),
          ← Finset.mul_sum]
      simp only [ricci]; ring
    rw [hc1] at hsolve
    rw [h2a, h2b] at hsolve
    linarith [hsolve]
  have hsw : (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0)
      = (∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0) :=
    Finset.sum_congr rfl (fun a _ => pd_comm (fun w => g w a a) c d 0 (hg a a))
  rw [hsw]
  exact key d c

/-- **RNC3 payoff — `√det g = 1 − ⅙ R_{cd} x^c x^d` holds GIVEN THE NORMAL-COORDINATE GAUGE.**  The
    Taylor coefficient `½ ∂_c∂_d √det g (0) = −⅙ Ric_{cd}` now follows with the metric-Hessian trace
    `htr` no longer a free hypothesis: it is DERIVED from `hgauge` (`rnc_htr_of_gauge`) and fed into
    `sqrtdet_taylor_coeff`.  The `⅙` (source of `κ = 1/6`) is thus gauge-derived, not carried.
    HONEST: still the `⅙` normalization ONLY — NOT the numerical value of G (N, Λ_s, E/ξ remain),
    NOT a curved heat kernel. -/
theorem sqrtdet_taylor_coeff_of_gauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (c d : Fin n) :
    (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0
      = -(1 / 6) * ricci g gi c d 0 :=
  sqrtdet_taylor_coeff g (fun a b => ricci g gi a b 0) hg hg0 hdg0
    (fun a b => rnc_htr_of_gauge g gi hg hgi hgi0 hdg0 hsymm hgauge a b) c d

/-! ### RNC4 — wiring the gauge-derived ⅙ into the heat-kernel `a₁` assembly -/

open QIQTH.HeatKernelA1 in
/-- **RNC4 — the `a₁` assembly with `κ = 1/6` GAUGE-DERIVED, not cited.**  This wires RNC3's
    gauge-derived `√det g` coefficient (`sqrtdet_taylor_coeff_of_gauge`) into `HeatKernelA1`'s
    conditional `a₁` assembly (`heat_a1_of_RNC_derived`), DISCHARGING the `κ = 1/6` citation that
    `heat_a1_of_RNC` carried.

    The conformal factor `κ` is DEFINED (via `hκgeo`) as the coefficient of the measure expansion
    `√det g = 1 − κ · R_{cd} x^c x^d` — i.e. `½ ∂_c∂_d √det g(0) = −κ · Ric_{cd}`.  This is the
    physical *definition* of `κ`, NOT a claim about its value.  Its VALUE is then FORCED to `1/6` by
    the falsifiable normal-coordinate gauge `hgauge`: `sqrtdet_taylor_coeff_of_gauge` gives
    `½ ∂_c∂_d √det g(0) = −(1/6) Ric_{cd}`, and comparing with `hκgeo` at a genuinely curved point
    (`hRic : ∃ c d, Ric_{cd}(0) ≠ 0`) cancels the Ricci factor to yield `κ = 1/6`.  That derived
    value discharges the `hκ : κ = 1/6` hypothesis of `heat_a1_of_RNC`, so the assembled `t¹`
    coefficient `(1/6 − ξ)R − m²` now carries the GAUGE as the source of its `1/6`, not a citation.

    SHARP TEST (passes): remove `hgauge` and `sqrtdet_taylor_coeff_of_gauge` is unavailable, so `κ`
    is no longer pinned to `1/6` (the trace/symmetric part of `∂∂g` is unconstrained) and the
    `(1/6 − ξ)R` conclusion fails.  The `1/6` genuinely flows from the falsifiable gauge.

    HONEST CAPTION (binding): this replaces the CITED `κ = 1/6` in the `a₁` accounting with the
    RNC3 gauge-DERIVED value — the conformal factor is no longer a free citation but follows from
    the normal-coordinate gauge.  It STILL does NOT give the numerical value of G (species count N,
    granularity scale Λ_s, and the E/`m²`/ξ potential term remain), and does NOT build a curved heat
    kernel.  The `⅙` normalization only. -/
theorem heat_a1_of_gauge (t : ℝ) (ht : 0 < t) (ξ m : ℝ)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (κ : ℝ)
    (hκgeo : ∀ c d, (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0
        = -κ * ricci g gi c d 0)
    (hRic : ∃ c d, ricci g gi c d 0 ≠ 0)
    (Rscl : ℝ) (hR : Rscl = ∑ i, ricci g gi i i 0) :
    (1 / (2 * t)) * (κ * ∑ i, ∑ j, ricci g gi i j 0 *
        (∫ x : (Fin n → ℝ), (∏ k, heatKernel1D t (x k)) * (x i * x j))) - ξ * Rscl - m ^ 2
      = (1 / 6 - ξ) * Rscl - m ^ 2 := by
  -- The gauge forces κ = 1/6 (discharging the citation), via RNC3's derived √det g coefficient.
  obtain ⟨c, d, hcd⟩ := hRic
  have hgc := sqrtdet_taylor_coeff_of_gauge g gi hg hgi hg0 hgi0 hdg0 hsymm hgauge c d
  have heq : -κ * ricci g gi c d 0 = -(1 / 6) * ricci g gi c d 0 := by
    rw [← hκgeo c d]; exact hgc
  have h0 : (1 / 6 - κ) * ricci g gi c d 0 = 0 := by
    have hrw : (1 / 6 - κ) * ricci g gi c d 0
        = -κ * ricci g gi c d 0 - (-(1 / 6) * ricci g gi c d 0) := by ring
    rw [hrw, heq, sub_self]
  have hκ : κ = 1 / 6 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hcd
  -- Feed the DERIVED κ = 1/6 into the (moment-matrix-derived) a₁ assembly.
  exact heat_a1_of_RNC_derived t ht ξ m (fun i j => ricci g gi i j 0) κ hκ Rscl hR

/-! ### FINITE-REGULARITY (`C²`) VARIANTS of the RNC → `a₁` chain

    The `⊤`-regularity theorems above (`heat_a1_of_gauge` and its callees) demand `g, gi ∈ C^∞`.
    Their proofs use only `≤ 2` derivatives of `g` and `≤ 1` derivative of `gi` at `0`, so they are
    weakenable to the FINITE regularity the pullback metric `g̃ = expPullbackMetric` actually
    satisfies: `g̃ ∈ ContDiffAt ℝ 2` at `0` (`contDiffAt2_expPullbackMetric_zero`) and its inverse
    is only `C¹`/differentiable at `0` (`expPullbackMetricInv_differentiableAt`).

    Below we add `_c2` variants with hypotheses `hg2 : ∀ a b, ContDiffAt ℝ 2 (g·· a b) 0` and
    `hgi1 : ∀ a b, ContDiffAt ℝ 1 (gi·· a b) 0`, proved by the SAME proof bodies with the analytic
    regularity primitives swapped for their local `ContDiffAt`/`DifferentiableAt` forms.  The
    `⊤` originals are UNTOUCHED.  This is independent of the pullback-gauge reindex work and does
    NOT itself give `κ = 1/6` (that needs `heat_a1_of_gauge_c2` instantiated at `g̃` with the
    unconditional gauge, separately blocked on the `g·Γ·Γ` reindex). -/

/-- Coordinate partial differentiability from Fréchet differentiability at a point (local form,
    not needing global `ContDiff`).  Self-contained copy of the technique used downstream in
    `QIQTH.PullbackMetric.pdiffAt_of_differentiableAt`. -/
theorem pdiffAt_of_differentiableAt (f : Point n → ℝ) (l : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f x) : PdiffAt f l x := by
  have hx : DifferentiableAt ℝ f ((Function.update x l) (x l)) := by
    rw [Function.update_eq_self]; exact hf
  exact hx.comp (x l) (hasDerivAt_update x l (x l)).differentiableAt

/-- `PdiffAt` congruence on a neighbourhood — if `f = h` near `x` then `PdiffAt f = PdiffAt h`. -/
theorem PdiffAt_congr_nhds {f h : Point n → ℝ} (l : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) (H : PdiffAt h l x) : PdiffAt f l x := by
  unfold PdiffAt at *
  have htend : Filter.Tendsto (fun t => Function.update x l t) (nhds (x l)) (nhds x) := by
    have hc := (hasDerivAt_update x l (x l)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact H.congr_of_eventuallyEq (htend.eventually hfh)

/-- `C²`-localised analogue of `Curvature.pd_pd_eq`: `∂_i∂_j f(0) = D²f(0)(e_i, e_j)`, needing only
    `ContDiffAt ℝ 2 f 0`. -/
theorem pd_pd_eq_of_contDiffAt2 (f : Point n → ℝ) (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) :
    pd (fun y => pd f j y) i 0
      = fderiv ℝ (fderiv ℝ f) 0 (Pi.single i 1) (Pi.single j 1) := by
  have hdf_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds (0 : Point n), ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have e1 : (fun y => pd f j y) =ᶠ[nhds (0 : Point n)] (fun y => (fderiv ℝ f y) (Pi.single j 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f j y hy
  rw [pd_congr i 0 e1,
      pd_eq_fderiv _ i 0 (hfd2.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hfd2 (differentiableAt_const _)]
  simp

/-- Second-order local partial differentiability at `0` from `ContDiffAt ℝ 2` — the `C²`-localised
    analogue of `Curvature.PdiffAt_pd`. -/
theorem PdiffAt_pd_zero_of_contDiffAt2 (f : Point n → ℝ) (m l : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) : PdiffAt (fun y => pd f m y) l 0 := by
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdf_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds (0 : Point n), ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds (0 : Point n)]
      (fun y => (fderiv ℝ f y) (Pi.single m 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact PdiffAt_congr_nhds l 0 e1
    (pdiffAt_of_differentiableAt _ l 0 (hfd2.clm_apply (differentiableAt_const _)))

/-- `C²`-localised **Schwarz** (`Curvature.pd_comm`): mixed partials commute at `0` from
    `ContDiffAt ℝ 2 f 0`. -/
theorem pd_comm_of_contDiffAt2 (f : Point n → ℝ) (i j : Fin n) (hf : ContDiffAt ℝ 2 f 0) :
    pd (fun y => pd f j y) i 0 = pd (fun y => pd f i y) j 0 := by
  rw [pd_pd_eq_of_contDiffAt2 f i j hf, pd_pd_eq_of_contDiffAt2 f j i hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq _ _

/-- `C²` variant of `pd_christoffel_origin`: needs only `g ∈ ContDiffAt ℝ 2` and `gi ∈ ContDiffAt ℝ 1`
    at `0`. -/
theorem pd_christoffel_origin_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (ν lam mu a : Fin n) :
    pd (fun y => christoffel g gi ν lam mu y) a 0
      = (1 / 2) * (pd (fun y => pd (fun w => g w ν mu) lam y) a 0
                   + pd (fun y => pd (fun w => g w ν lam) mu y) a 0
                   - pd (fun y => pd (fun w => g w lam mu) ν y) a 0) := by
  have hBP : ∀ α, PdiffAt (fun y => pd (fun w => g w α mu) lam y
      + pd (fun w => g w α lam) mu y - pd (fun w => g w lam mu) α y) a 0 := fun α =>
    ((PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α mu) lam a (hg2 α mu)).add
      (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α lam) mu a (hg2 α lam))).sub
      (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w lam mu) α a (hg2 lam mu))
  have hgiP : ∀ α, PdiffAt (fun y => gi y ν α) a 0 := fun α =>
    pdiffAt_of_differentiableAt _ a 0 ((hgi1 ν α).differentiableAt (by norm_num))
  have hsummand : ∀ α, pd (fun y => gi y ν α * (pd (fun w => g w α mu) lam y
        + pd (fun w => g w α lam) mu y - pd (fun w => g w lam mu) α y)) a 0
      = gi 0 ν α * (pd (fun y => pd (fun w => g w α mu) lam y) a 0
          + pd (fun y => pd (fun w => g w α lam) mu y) a 0
          - pd (fun y => pd (fun w => g w lam mu) α y) a 0) := by
    intro α
    rw [pd_mul (fun y => gi y ν α) _ a 0 (hgiP α) (hBP α),
        pd_sub _ _ a 0 ((PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α mu) lam a (hg2 α mu)).add
          (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α lam) mu a (hg2 α lam)))
          (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w lam mu) α a (hg2 lam mu)),
        pd_add _ _ a 0 (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α mu) lam a (hg2 α mu))
          (PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w α lam) mu a (hg2 α lam))]
    simp only [hdg0 α mu lam, hdg0 α lam mu, hdg0 lam mu α]
    ring
  simp only [christoffel]
  rw [pd_const_mul _ _ a 0 (PdiffAt_sum univ _ a 0 (fun α _ => (hgiP α).mul (hBP α))),
      pd_sum univ _ a 0 (fun α _ => (hgiP α).mul (hBP α)),
      Finset.sum_congr rfl (fun α _ => hsummand α)]
  simp only [hgi0, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- `C²` variant of `sum_pd_christoffel_trace`. -/
theorem sum_pd_christoffel_trace_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (c d : Fin n) :
    (∑ ν, pd (fun y => christoffel g gi ν ν d y) c 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [pd_christoffel_origin_c2 g gi hg2 hgi1 hgi0 hdg0 ν ν d c]
  ring

/-- `C²` variant of `sum_riemann_ii_zero`. -/
theorem sum_riemann_ii_zero_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (c d : Fin n) :
    (∑ ν, riemann g gi ν ν c d 0) = 0 := by
  have hL : (∑ ν, pd (fun y => christoffel g gi ν d ν y) c 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
    rw [show (∑ ν, pd (fun y => christoffel g gi ν d ν y) c 0)
          = ∑ ν, pd (fun y => christoffel g gi ν ν d y) c 0 from
        Finset.sum_congr rfl (fun ν _ => by
          rw [show (fun y => christoffel g gi ν d ν y) = (fun y => christoffel g gi ν ν d y) from
            funext (fun y => christoffel_symm g gi hsymm ν d ν y)])]
    exact sum_pd_christoffel_trace_c2 g gi hg2 hgi1 hgi0 hdg0 c d
  have hR : (∑ ν, pd (fun y => christoffel g gi ν c ν y) d 0)
      = (1 / 2) * ∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0 := by
    rw [show (∑ ν, pd (fun y => christoffel g gi ν c ν y) d 0)
          = ∑ ν, pd (fun y => christoffel g gi ν ν c y) d 0 from
        Finset.sum_congr rfl (fun ν _ => by
          rw [show (fun y => christoffel g gi ν c ν y) = (fun y => christoffel g gi ν ν c y) from
            funext (fun y => christoffel_symm g gi hsymm ν c ν y)])]
    exact sum_pd_christoffel_trace_c2 g gi hg2 hgi1 hgi0 hdg0 d c
  have hswap : (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0)
      = (∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0) :=
    Finset.sum_congr rfl (fun a _ => pd_comm_of_contDiffAt2 (fun w => g w a a) c d (hg2 a a))
  rw [Finset.sum_congr rfl (fun ν _ => riemann_at_origin g gi hdg0 ν ν c d),
      Finset.sum_sub_distrib, hL, hR, hswap]
  ring

/-- `C²` variant of `rnc_htr_of_gauge`. -/
theorem rnc_htr_of_gauge_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (c d : Fin n) :
    (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * ricci g gi c d 0 := by
  have key : ∀ p q : Fin n,
      (∑ a, pd (fun y => pd (fun w => g w a a) q y) p 0) = -(2 / 3) * ricci g gi q p 0 := by
    intro p q
    have hc1 := sum_pd_christoffel_trace_c2 g gi hg2 hgi1 hgi0 hdg0 p q
    have hsolve : (∑ ν, pd (fun y => christoffel g gi ν ν q y) p 0)
        = (1 / 3) * ((∑ ν, riemann g gi ν ν p q 0) + (∑ ν, riemann g gi ν q p ν 0)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ν _ => by
        rw [pd_christoffel_solve g gi hdg0 hsymm hgauge ν p ν q]; ring)
    have h2a := sum_riemann_ii_zero_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm p q
    have h2b : (∑ ν, riemann g gi ν q p ν 0) = - ricci g gi q p 0 := by
      rw [show (∑ ν, riemann g gi ν q p ν 0) = ∑ ν, (-1 : ℝ) * riemann g gi ν q ν p 0 from
            Finset.sum_congr rfl (fun ν _ => by rw [riemann_antisymm g gi ν q p ν 0]; ring),
          ← Finset.mul_sum]
      simp only [ricci]; ring
    rw [hc1] at hsolve
    rw [h2a, h2b] at hsolve
    linarith [hsolve]
  have hsw : (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0)
      = (∑ a, pd (fun y => pd (fun w => g w a a) c y) d 0) :=
    Finset.sum_congr rfl (fun a _ => pd_comm_of_contDiffAt2 (fun w => g w a a) c d (hg2 a a))
  rw [hsw]
  exact key d c

/-! #### `C²` det / √det atoms -/

/-- A finite product of `ContDiffAt ℝ 2`-at-`x` fields is `ContDiffAt ℝ 2` — local analogue of
    `contDiff_prod`. -/
theorem contDiffAt_prod {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (x : Point n)
    (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (fun y => F i y) x) :
    ContDiffAt ℝ 2 (fun y => ∏ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact contDiffAt_const
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- A finite product of `DifferentiableAt`-at-`x` fields is `DifferentiableAt` (fderiv finite-product
    rule, general domain). -/
theorem differentiableAt_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F : ι → Point n → ℝ) (x : Point n)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (fun y => F i y) x) :
    DifferentiableAt ℝ (fun y => ∏ i ∈ s, F i y) x :=
  (HasFDerivAt.finsetProd (fun i hi => (hF i hi).hasFDerivAt)).differentiableAt

/-- `C²` variant of `det_contDiff`: `det ∘ g` is `ContDiffAt ℝ 2` at `0` when the entries are. -/
theorem det_contDiffAt2 (g : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0) :
    ContDiffAt ℝ 2 (fun y => Matrix.det (g y)) 0 := by
  rw [show (fun y => Matrix.det (g y))
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g y (σ i) i)
      from funext (fun y => Matrix.det_apply' _)]
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul
    (contDiffAt_prod univ (fun i y => g y (σ i) i) 0 (fun i _ => hg2 (σ i) i))

/-- Local **finite-product Leibniz for `pd`** — the `DifferentiableAt`-at-`x` analogue of `pd_prod`. -/
theorem pd_prod_diff {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → Point n → ℝ)
    (c : Fin n) (x : Point n)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (fun y => F i y) x) :
    pd (fun y => ∏ i ∈ s, F i y) c x
      = ∑ i ∈ s, pd (F i) c x * ∏ j ∈ s.erase i, F j x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact pd_const 1 c x
  | insert a s ha ih =>
      have hFa : PdiffAt (F a) c x :=
        pdiffAt_of_differentiableAt _ c x (hF a (Finset.mem_insert_self a s))
      have hFs : ∀ i ∈ s, DifferentiableAt ℝ (fun y => F i y) x :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hprod : PdiffAt (fun y => ∏ i ∈ s, F i y) c x :=
        pdiffAt_of_differentiableAt _ c x (differentiableAt_finset_prod s F x hFs)
      simp only [Finset.prod_insert ha]
      rw [pd_mul (F a) (fun y => ∏ i ∈ s, F i y) c x hFa hprod, ih hFs,
          Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne (Ne.symm hia), Finset.prod_insert (by
            simp only [Finset.mem_erase]; exact fun h => ha h.2)]
      ring

/-- Local (pointwise) first derivative of `det g` — the `DifferentiableAt`-at-`y` analogue of
    `pd_det`. -/
theorem pd_det_diff (g : Point n → Fin n → Fin n → ℝ) (d : Fin n) (y : Point n)
    (hy : ∀ a b, DifferentiableAt ℝ (fun w => g w a b) y) :
    pd (fun w => Matrix.det (g w)) d y
      = ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
          * ∑ k, pd (fun w => g w (σ k) k) d y * ∏ i ∈ univ.erase k, g y (σ i) i := by
  rw [show (fun w => Matrix.det (g w))
        = (fun w => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g w (σ i) i)
      from funext (fun w => Matrix.det_apply' _)]
  rw [pd_sum univ _ d y (fun σ _ => PdiffAt_const_mul _ _ d y
        (pdiffAt_of_differentiableAt _ d y
          (differentiableAt_finset_prod univ (fun i w => g w (σ i) i) y
            (fun i _ => hy (σ i) i))))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pd_const_mul _ _ d y (pdiffAt_of_differentiableAt _ d y
        (differentiableAt_finset_prod univ (fun i w => g w (σ i) i) y (fun i _ => hy (σ i) i))),
      pd_prod_diff univ (fun i w => g w (σ i) i) d y (fun i _ => hy (σ i) i)]

/-- `C²` variant of `det_pd_first`. -/
theorem det_pd_first_c2 (g : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (e : Fin n) :
    pd (fun w => Matrix.det (g w)) e 0 = 0 := by
  rw [pd_det_diff g e 0 (fun a b => (hg2 a b).differentiableAt (by norm_num))]
  apply Finset.sum_eq_zero
  intro σ _
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k _
  rw [hdg0 (σ k) k e, zero_mul]

set_option maxHeartbeats 800000 in
/-- `C²` variant of `det_pd_pd_expand`.  The inner first-derivative identity `pd_det` is transported
    from a single point to a NEIGHBOURHOOD of `0` (where all entries are differentiable, from
    `ContDiffAt.eventually`) via `pd_congr`, then the outer `∂_c` distributes at `0` using the
    `C²`-localised second-order `PdiffAt` facts. -/
theorem det_pd_pd_expand_c2 (g : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0) (c d : Fin n) :
    pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
          * ∑ k, pd (fun y => pd (fun w => g w (σ k) k) d y) c 0
              * ∏ i ∈ univ.erase k, g 0 (σ i) i := by
  -- entries are differentiable on a neighbourhood of `0`.
  have hdiff_ev : ∀ᶠ y in nhds (0 : Point n),
      ∀ a b, DifferentiableAt ℝ (fun w => g w a b) y := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    filter_upwards [(hg2 a b).eventually (by norm_num)] with y hy
      using hy.differentiableAt (by norm_num)
  -- transport `pd_det` to the germ.
  have hEq : (fun y => pd (fun w => Matrix.det (g w)) d y) =ᶠ[nhds (0 : Point n)]
      (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ)
          * ∑ k, pd (fun w => g w (σ k) k) d y * ∏ i ∈ univ.erase k, g y (σ i) i) := by
    filter_upwards [hdiff_ev] with y hy using pd_det_diff g d y hy
  rw [pd_congr c 0 hEq]
  -- second-order `PdiffAt` facts at `0`.
  have hPd : ∀ (σ : Equiv.Perm (Fin n)) (k : Fin n),
      PdiffAt (fun y => pd (fun w => g w (σ k) k) d y) c 0 :=
    fun σ k => PdiffAt_pd_zero_of_contDiffAt2 (fun w => g w (σ k) k) d c (hg2 (σ k) k)
  have hPp : ∀ (σ : Equiv.Perm (Fin n)) (k : Fin n),
      PdiffAt (fun y => ∏ i ∈ univ.erase k, g y (σ i) i) c 0 :=
    fun σ k => pdiffAt_of_differentiableAt _ c 0
      (differentiableAt_finset_prod (univ.erase k) (fun i y => g y (σ i) i) 0
        (fun i _ => (hg2 (σ i) i).differentiableAt (by norm_num)))
  rw [pd_sum univ _ c 0 (fun σ _ => PdiffAt_const_mul _ _ c 0
        (PdiffAt_sum univ _ c 0 (fun k _ => (hPd σ k).mul (hPp σ k))))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pd_const_mul _ _ c 0 (PdiffAt_sum univ _ c 0 (fun k _ => (hPd σ k).mul (hPp σ k)))]
  congr 1
  rw [pd_sum univ _ c 0 (fun k _ => (hPd σ k).mul (hPp σ k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [pd_mul (fun y => pd (fun w => g w (σ k) k) d y)
        (fun y => ∏ i ∈ univ.erase k, g y (σ i) i) c 0 (hPd σ k) (hPp σ k)]
  simp only [hdg0 (σ k) k d, zero_mul, add_zero]

/-- `C²` variant of `sqrt_pd_pd`: `∂_c∂_d √F(0) = ½ ∂_c∂_d F(0)` at a critical point, needing only
    `ContDiffAt ℝ 2 F 0`. -/
theorem sqrt_pd_pd_c2 (F : Point n → ℝ) (c d : Fin n)
    (hF : ContDiffAt ℝ 2 F 0) (hval : F 0 = 1) (hcrit : ∀ e, pd F e 0 = 0) :
    pd (fun y => pd (fun w => Real.sqrt (F w)) d y) c 0
      = (1 / 2) * pd (fun y => pd F d y) c 0 := by
  have hne : F 0 ≠ 0 := by rw [hval]; norm_num
  have hnhds : ∀ᶠ y in nhds (0 : Point n), F y ≠ 0 :=
    hF.continuousAt.eventually_ne hne
  have hdiff_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ F y := by
    filter_upwards [hF.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hchain : (fun y => pd (fun w => Real.sqrt (F w)) d y)
      =ᶠ[nhds (0 : Point n)] (fun y => (1 / (2 * Real.sqrt (F y))) * pd F d y) := by
    filter_upwards [hnhds, hdiff_ev] with y hy hdy
    exact pd_comp_sqrt F d y (pdiffAt_of_differentiableAt F d y hdy) hy
  rw [pd_congr c 0 hchain]
  have hB : PdiffAt (fun y => pd F d y) c 0 := PdiffAt_pd_zero_of_contDiffAt2 F d c hF
  have hγd : DifferentiableAt ℝ (fun t => F (Function.update 0 c t)) ((0 : Point n) c) :=
    pdiffAt_of_differentiableAt F c 0 (hF.differentiableAt (by norm_num))
  have hFxc : F (Function.update (0 : Point n) c ((0 : Point n) c)) = F 0 := by
    rw [Function.update_eq_self]
  have hsqrtd : DifferentiableAt ℝ Real.sqrt (F (Function.update (0 : Point n) c ((0 : Point n) c))) := by
    rw [hFxc]; exact (Real.hasDerivAt_sqrt hne).differentiableAt
  have hcompd : DifferentiableAt ℝ (fun t => Real.sqrt (F (Function.update 0 c t))) ((0 : Point n) c) :=
    hsqrtd.comp ((0 : Point n) c) hγd
  have hden : DifferentiableAt ℝ (fun t => 2 * Real.sqrt (F (Function.update 0 c t))) ((0 : Point n) c) :=
    (differentiableAt_const 2).mul hcompd
  have hdenne : (2 : ℝ) * Real.sqrt (F (Function.update (0 : Point n) c ((0 : Point n) c))) ≠ 0 := by
    rw [hFxc, hval, Real.sqrt_one]; norm_num
  have hA : PdiffAt (fun y => 1 / (2 * Real.sqrt (F y))) c 0 := by
    show DifferentiableAt ℝ (fun t => 1 / (2 * Real.sqrt (F (Function.update 0 c t)))) ((0 : Point n) c)
    simp only [one_div]
    exact hden.inv hdenne
  rw [pd_mul (fun y => 1 / (2 * Real.sqrt (F y))) (fun y => pd F d y) c 0 hA hB]
  have hBx : pd F d 0 = 0 := hcrit d
  have hAx : (1 : ℝ) / (2 * Real.sqrt (F 0)) = 1 / 2 := by
    rw [hval, Real.sqrt_one]; norm_num
  rw [hBx, mul_zero, zero_add, hAx]

/-- `C²` variant of `sqrtdet_pd_pd`. -/
theorem sqrtdet_pd_pd_c2 (g : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (c d : Fin n) :
    pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0 = -(1 / 3) * Ric c d := by
  have hFcd : ContDiffAt ℝ 2 (fun y => Matrix.det (g y)) 0 := det_contDiffAt2 g hg2
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hF0 : (fun y => Matrix.det (g y)) 0 = 1 := by
    show Matrix.det (g 0) = 1; rw [hg0mat, Matrix.det_one]
  have hcrit : ∀ e, pd (fun y => Matrix.det (g y)) e 0 = 0 := fun e => det_pd_first_c2 g hg2 hdg0 e
  have hdet2 : pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = ∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0 := by
    rw [det_pd_pd_expand_c2 g hg2 hdg0 c d,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.prod_eq_one (fun i _ => by rw [hg0 i i]; exact Matrix.one_apply_eq i), mul_one]
    · intro σ _ hσ
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro k _
      apply mul_eq_zero_of_right
      obtain ⟨i0, hi0mem, hi0⟩ := perm_moves_in_erase σ hσ k
      exact Finset.prod_eq_zero hi0mem (by rw [hg0 (σ i0) i0]; exact Matrix.one_apply_ne hi0)
    · intro h; exact absurd (Finset.mem_univ _) h
  have key := sqrt_pd_pd_c2 (fun y => Matrix.det (g y)) c d hFcd hF0 hcrit
  rw [hdet2, htr c d] at key
  rw [show (1 : ℝ) / 2 * (-(2 / 3) * Ric c d) = -(1 / 3) * Ric c d from by ring] at key
  exact key

/-- `C²` variant of `sqrtdet_taylor_coeff`. -/
theorem sqrtdet_taylor_coeff_c2 (g : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (c d : Fin n) :
    (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0 = -(1 / 6) * Ric c d := by
  rw [sqrtdet_pd_pd_c2 g Ric hg2 hg0 hdg0 htr c d]; ring

/-- `C²` variant of `sqrtdet_taylor_coeff_of_gauge`. -/
theorem sqrtdet_taylor_coeff_of_gauge_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (c d : Fin n) :
    (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0
      = -(1 / 6) * ricci g gi c d 0 :=
  sqrtdet_taylor_coeff_c2 g (fun a b => ricci g gi a b 0) hg2 hg0 hdg0
    (fun a b => rnc_htr_of_gauge_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm hgauge a b) c d

open QIQTH.HeatKernelA1 in
/-- **`heat_a1_of_gauge_c2` — the FINITE-REGULARITY (`C²`) variant of `heat_a1_of_gauge`.**  Same
    statement/conclusion, with the `ContDiff ⊤` hypotheses on `g`/`gi` replaced by the WEAKEST
    regularity the proof uses: `g ∈ ContDiffAt ℝ 2` at `0` and `gi ∈ ContDiffAt ℝ 1` at `0` — exactly
    what the pullback metric `g̃ = expPullbackMetric` and its inverse satisfy.  The proof body is the
    same as `heat_a1_of_gauge`, calling the `_c2` chain (`sqrtdet_taylor_coeff_of_gauge_c2`). -/
theorem heat_a1_of_gauge_c2 (t : ℝ) (ht : 0 < t) (ξ m : ℝ)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (κ : ℝ)
    (hκgeo : ∀ c d, (1 / 2) * pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0
        = -κ * ricci g gi c d 0)
    (hRic : ∃ c d, ricci g gi c d 0 ≠ 0)
    (Rscl : ℝ) (hR : Rscl = ∑ i, ricci g gi i i 0) :
    (1 / (2 * t)) * (κ * ∑ i, ∑ j, ricci g gi i j 0 *
        (∫ x : (Fin n → ℝ), (∏ k, heatKernel1D t (x k)) * (x i * x j))) - ξ * Rscl - m ^ 2
      = (1 / 6 - ξ) * Rscl - m ^ 2 := by
  obtain ⟨c, d, hcd⟩ := hRic
  have hgc := sqrtdet_taylor_coeff_of_gauge_c2 g gi hg2 hgi1 hg0 hgi0 hdg0 hsymm hgauge c d
  have heq : -κ * ricci g gi c d 0 = -(1 / 6) * ricci g gi c d 0 := by
    rw [← hκgeo c d]; exact hgc
  have h0 : (1 / 6 - κ) * ricci g gi c d 0 = 0 := by
    have hrw : (1 / 6 - κ) * ricci g gi c d 0
        = -κ * ricci g gi c d 0 - (-(1 / 6) * ricci g gi c d 0) := by ring
    rw [hrw, heq, sub_self]
  have hκ : κ = 1 / 6 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hcd
  exact heat_a1_of_RNC_derived t ht ξ m (fun i j => ricci g gi i j 0) κ hκ Rscl hR

end QIQTH.RNCExpansion
