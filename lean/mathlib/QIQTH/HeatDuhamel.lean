/-
  HeatDuhamel — the ALGEBRAIC heart of the Levi/Duhamel parametrix correction.

  Decomposes the P2d wall.  The parametrix `H_N` (built elsewhere) satisfies `(∂_t − Δ_g)H_N = E`
  with a small residual `E` (`HeatParametrixError`/`HeatParametrixOrder`).  The TRUE heat kernel is
  the Levi/Duhamel Neumann series
      `K = H_N + H_N * E + H_N * E * E + …`,
  where `*` is the space-time (Duhamel) convolution
      `(A * B)(t,x,y) = ∫₀ᵗ ∫ A(t−s, x, z) · B(s, z, y) dz ds`
  and Duhamel's principle says `A * B` solves the inhomogeneous heat equation with source `B` when
  `A` is a fundamental solution of the (homogeneous) heat equation.

  This file separates the ALGEBRAIC core (reachable) from the ANALYTIC wall (checkpointed):

  LANDED (fully proven, axiom-clean):
    • `heatConv` — the space-time convolution (definition; `intervalIntegral` in `s`, Lebesgue
      `volume`-integral on `Point n = Fin n → ℝ` in `z`);
    • bilinearity / basic algebra: `heatConv_add_left`/`_right`, `heatConv_smul_left`/`_right`,
      `heatConv_zero_left`/`_right` — under the natural (non-vacuous) integrability hypotheses;
    • `heatConvFrozen` + `heatConvFrozen_diag` — the diagonal of the two-variable frozen convolution;
    • `heatConv_hasDerivAt_upper` / `heatConv_deriv_upper` — the FTC-1 (upper-limit) piece of
      Duhamel's principle: with the outer-`t`-inside-`A` FROZEN, `d/dt ∫₀ᵗ (…) ds = (…)|_{s=t}`;
    • `duhamel_principle` — the target Duhamel identity `(∂_t − Δ_{g,x})(A * B) = B` for `t>0`,
      REDUCED (by genuine algebra: Leibniz + heat-equation cancellation + Laplacian-under-integral +
      delta initial condition) to its four analytic ingredients, each carried as an EXPLICIT,
      non-vacuous hypothesis.

  CHECKPOINTED — the P2d analytic wall (deliberately NOT attempted here, carried as hypotheses):
    • the full diagonal Leibniz rule `heatConv_deriv_t` = `hLeibniz` (upper-limit FTC + differentiating
      the integrand's outer-`t` UNDER the `z`-integral via dominated convergence);
    • the heat-equation cancellation `hHeatEq` (`A` a fundamental solution ⟹ `∂_t = Δ_x` under `∫z`);
    • the Laplacian passing under the `s`-integral `hLapUnder`;
    • the delta initial condition `hDelta` (`A(0⁺,x,·) = δ_x`);
    • the Gaussian iterated-convolution CONVERGENCE of the Neumann series (the community-scale wall).

  This is NOT the true-kernel existence nor the general `a₁ = R/6` (both stay behind the convergence
  bound).  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.LaplaceBeltrami

open QIQTH.Curvature QIQTH.LaplaceBeltrami MeasureTheory
open scoped Interval

namespace QIQTH.HeatDuhamel

variable {n : ℕ}

/-! ### 1. The space-time (Duhamel) convolution -/

/-- **The space-time (Duhamel) convolution**
    `(A * B)(t,x,y) = ∫₀ᵗ ∫ A(t−s, x, z) · B(s, z, y) dz ds`,
    with the `s`-integral an `intervalIntegral` on `[0,t]` and the `z`-integral the Lebesgue
    (`volume`) integral on `Point n = Fin n → ℝ`.  This is the `*` of the Levi/Duhamel series. -/
noncomputable def heatConv (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) : ℝ :=
  ∫ s in (0)..t, (∫ z, A (t - s) x z * B s z y)

/-! ### 2. Bilinearity / basic algebra of the convolution -/

/-- **Left additivity** `(A₁+A₂) * B = A₁ * B + A₂ * B`, under integrability of each summand's
    `z`-integrand (for the inner split) and of each resulting `s`-integrand (for the outer split). -/
theorem heatConv_add_left (A₁ A₂ B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hA₁ : ∀ s, Integrable (fun z => A₁ (t - s) x z * B s z y))
    (hA₂ : ∀ s, Integrable (fun z => A₂ (t - s) x z * B s z y))
    (hI₁ : IntervalIntegrable (fun s => ∫ z, A₁ (t - s) x z * B s z y) volume 0 t)
    (hI₂ : IntervalIntegrable (fun s => ∫ z, A₂ (t - s) x z * B s z y) volume 0 t) :
    heatConv (fun τ p q => A₁ τ p q + A₂ τ p q) B t x y
      = heatConv A₁ B t x y + heatConv A₂ B t x y := by
  simp only [heatConv]
  have hstep : ∀ s, (∫ z, (A₁ (t - s) x z + A₂ (t - s) x z) * B s z y)
      = (∫ z, A₁ (t - s) x z * B s z y) + (∫ z, A₂ (t - s) x z * B s z y) := by
    intro s
    rw [← MeasureTheory.integral_add (hA₁ s) (hA₂ s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  simp only [hstep]
  exact intervalIntegral.integral_add hI₁ hI₂

/-- **Right additivity** `A * (B₁+B₂) = A * B₁ + A * B₂`. -/
theorem heatConv_add_right (A B₁ B₂ : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hB₁ : ∀ s, Integrable (fun z => A (t - s) x z * B₁ s z y))
    (hB₂ : ∀ s, Integrable (fun z => A (t - s) x z * B₂ s z y))
    (hI₁ : IntervalIntegrable (fun s => ∫ z, A (t - s) x z * B₁ s z y) volume 0 t)
    (hI₂ : IntervalIntegrable (fun s => ∫ z, A (t - s) x z * B₂ s z y) volume 0 t) :
    heatConv A (fun τ p q => B₁ τ p q + B₂ τ p q) t x y
      = heatConv A B₁ t x y + heatConv A B₂ t x y := by
  simp only [heatConv]
  have hstep : ∀ s, (∫ z, A (t - s) x z * (B₁ s z y + B₂ s z y))
      = (∫ z, A (t - s) x z * B₁ s z y) + (∫ z, A (t - s) x z * B₂ s z y) := by
    intro s
    rw [← MeasureTheory.integral_add (hB₁ s) (hB₂ s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  simp only [hstep]
  exact intervalIntegral.integral_add hI₁ hI₂

/-- **Left homogeneity** `(c·A) * B = c·(A * B)` (no integrability needed: pure scalar pull-out). -/
theorem heatConv_smul_left (c : ℝ) (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConv (fun τ p q => c * A τ p q) B t x y = c * heatConv A B t x y := by
  simp only [heatConv]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- **Right homogeneity** `A * (c·B) = c·(A * B)`. -/
theorem heatConv_smul_right (c : ℝ) (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConv A (fun τ p q => c * B τ p q) t x y = c * heatConv A B t x y := by
  simp only [heatConv]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- **Left annihilation** `0 * B = 0`. -/
theorem heatConv_zero_left (B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConv (fun _ _ _ => (0 : ℝ)) B t x y = 0 := by
  unfold heatConv
  simp only [zero_mul, MeasureTheory.integral_zero, intervalIntegral.integral_zero]

/-- **Right annihilation** `A * 0 = 0`. -/
theorem heatConv_zero_right (A : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConv A (fun _ _ _ => (0 : ℝ)) t x y = 0 := by
  unfold heatConv
  simp only [mul_zero, MeasureTheory.integral_zero, intervalIntegral.integral_zero]

/-! ### 3. The FTC (upper-limit) piece of Duhamel's principle -/

/-- **The frozen convolution**: the two-variable object whose diagonal is `heatConv`.  Here `τ₀` is
    the outer-`t` FROZEN inside `A`, while `t` is the free upper limit of the `s`-integral.  Isolating
    these two roles of `t` is the point: the FTC controls the upper-limit dependence, while the
    dependence through `A (τ₀ − s)` is the under-integral part (the analytic wall). -/
noncomputable def heatConvFrozen (A B : ℝ → Point n → Point n → ℝ) (τ₀ t : ℝ) (x y : Point n) : ℝ :=
  ∫ s in (0)..t, (∫ z, A (τ₀ - s) x z * B s z y)

/-- On the diagonal the frozen convolution is the genuine convolution. -/
theorem heatConvFrozen_diag (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatConvFrozen A B t t x y = heatConv A B t x y := rfl

/-- **FTC-1 (upper-limit) piece of Duhamel's principle.**  With the outer `t` inside `A` frozen at
    `τ₀`, the map `u ↦ ∫₀ᵘ (∫ z, A(τ₀−s) x z · B s z y) ds` has derivative equal to the integrand
    evaluated at the upper limit `s=t`, namely `∫ z, A(τ₀−t) x z · B t z y`.  This is exactly the
    boundary term of Duhamel's principle; the differentiation of the integrand's OWN outer-`t`
    (through `A(τ₀−s)` with `τ₀=t`) is the checkpointed under-integral part.  The (genuine,
    non-vacuous) hypothesis is continuity in `s` of the inner `z`-integral. -/
theorem heatConv_hasDerivAt_upper (A B : ℝ → Point n → Point n → ℝ) (τ₀ t : ℝ) (x y : Point n)
    (hcont : Continuous (fun s => ∫ z, A (τ₀ - s) x z * B s z y)) :
    HasDerivAt (fun u => ∫ s in (0)..u, (∫ z, A (τ₀ - s) x z * B s z y))
      (∫ z, A (τ₀ - t) x z * B t z y) t :=
  intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- The `deriv` form of the FTC upper-limit piece:
    `d/dt (heatConvFrozen A B τ₀ · x y) t = ∫ z, A(τ₀−t) x z · B t z y`. -/
theorem heatConv_deriv_upper (A B : ℝ → Point n → Point n → ℝ) (τ₀ t : ℝ) (x y : Point n)
    (hcont : Continuous (fun s => ∫ z, A (τ₀ - s) x z * B s z y)) :
    deriv (fun u => heatConvFrozen A B τ₀ u x y) t = ∫ z, A (τ₀ - t) x z * B t z y :=
  (heatConv_hasDerivAt_upper A B τ₀ t x y hcont).deriv

/-! ### 4. Duhamel's principle (target identity, carrying the analytic ingredients) -/

/-- **Duhamel's principle** — the target identity of the Levi/Duhamel correction:
    if `A` is a fundamental solution of the heat equation in its first slot, then `A * B` solves the
    inhomogeneous heat equation with source `B`, i.e. for `t > 0`
        `(∂_t − Δ_{g,x})(A * B)(t,x,y) = B(t,x,y)`.

    This theorem lands the STRUCTURE: it REDUCES the identity, by genuine algebra, to its four
    analytic ingredients — each carried as an EXPLICIT, non-vacuous hypothesis (they all hold for the
    true fundamental solution, none of them is the conclusion):

    * `hLeibniz` — the diagonal **Leibniz rule**: the `t`-derivative of the diagonal convolution
      splits into the upper-limit boundary term `∫ z, A 0 x z · B t z y` (proved directly in
      `heatConv_deriv_upper`) plus the under-integral term `∫₀ᵗ ∂_t(inner) ds`;
    * `hHeatEq` — `A` a **fundamental solution**: under the `z`-integral, `∂_t(inner) = Δ_{g,x}(inner)`
      pointwise in `s` (heat equation `∂_τ A = Δ_x A` transported through the convolution);
    * `hLapUnder` — the spatial **Laplacian passes under** the `s`-integral;
    * `hDelta` — the **delta initial condition** `A(0⁺, x, ·) = δ_x`, giving the boundary term `= B`.

    The `∂_t(inner)` and `Δ_x(inner)` terms CANCEL (via `hHeatEq`), leaving only the boundary term,
    which `hDelta` identifies with the source `B t x y`. -/
theorem duhamel_principle (g gi : Point n → Fin n → Fin n → ℝ)
    (A B : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hLeibniz : deriv (fun u => heatConv A B u x y) t
        = (∫ z, A 0 x z * B t z y)
          + (∫ s in (0)..t, deriv (fun u => ∫ z, A (u - s) x z * B s z y) t))
    (hHeatEq : ∀ s, deriv (fun u => ∫ z, A (u - s) x z * B s z y) t
        = laplaceBeltrami g gi (fun p => ∫ z, A (t - s) p z * B s z y) x)
    (hLapUnder : laplaceBeltrami g gi (fun p => heatConv A B t p y) x
        = ∫ s in (0)..t, laplaceBeltrami g gi (fun p => ∫ z, A (t - s) p z * B s z y) x)
    (hDelta : (∫ z, A 0 x z * B t z y) = B t x y) :
    deriv (fun u => heatConv A B u x y) t
        - laplaceBeltrami g gi (fun p => heatConv A B t p y) x
      = B t x y := by
  rw [hLeibniz, hLapUnder]
  have hcancel : (∫ s in (0)..t, deriv (fun u => ∫ z, A (u - s) x z * B s z y) t)
      = (∫ s in (0)..t, laplaceBeltrami g gi (fun p => ∫ z, A (t - s) p z * B s z y) x) :=
    intervalIntegral.integral_congr fun s _ => hHeatEq s
  rw [hcancel, add_sub_cancel_right, hDelta]

/-! ### 5. Associativity of the Duhamel convolution (Fubini algebra) -/

/-- **The convolution packaged as a kernel** `heatConvK A B : ℝ → Point n → Point n → ℝ`.  A
    `heatConv A B` is a scalar-per-`(t,x,y)` object; to iterate the Levi/Duhamel product
    `H_N * E * E * …` we must feed a convolution back in as a *kernel* argument of `heatConv`.  This
    repackaging is exactly that.  (`rfl`-transparent by `heatConvK_apply`.) -/
noncomputable def heatConvK (A B : ℝ → Point n → Point n → ℝ) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => heatConv A B τ p q

@[simp] theorem heatConvK_apply (A B : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p q : Point n) :
    heatConvK A B τ p q = heatConv A B τ p q := rfl

/-- **Spatial Fubini** — the reachable measure-theoretic core of associativity.  For a jointly
    integrable spatial integrand `F : Point n → Point n → ℝ`, the two orders of the iterated
    Lebesgue integral over `Point n = Fin n → ℝ` agree.  In the associativity computation this is
    exactly the swap of the `∫ z` and `∫ w` integrals carrying the two convolution kernels.  This is
    genuine (non-vacuous) measure theory: it FAILS without the joint-integrability hypothesis, whose
    shape (`Integrable (uncurry F) (volume.prod volume)`) is precisely what `integral_integral_swap`
    requires.  This is NOT any analytic/Gaussian-bound wall. -/
theorem heatConv_spatial_fubini (F : Point n → Point n → ℝ)
    (hF : Integrable (Function.uncurry F) (volume.prod volume)) :
    (∫ z, ∫ w, F z w) = ∫ w, ∫ z, F z w :=
  integral_integral_swap hF

set_option maxHeartbeats 1000000 in
/-- **Associativity of the Duhamel convolution** `(A * B) * C = A * (B * C)`.

    Writing both sides out over the space-time domain (`z, w` the two spatial integration variables
    threaded through the three kernels, `s, s'` the two time variables on the triangle
    `{0 ≤ s, 0 ≤ s', s + s' ≤ t}`):

      `((A*B)*C)(t,x,y) = ∫₀ᵗ ∫_z ∫₀^{t−s} ∫_w  A(t−s−s') x w · B s' w z · C s z y`
      `(A*(B*C))(t,x,y) = ∫₀ᵗ ∫_w ∫₀^{u}   ∫_z  A(t−u)   x w · B(u−u') w z · C u' z y`.

    Under the time change of variables `u = s + s'`, `u' = s` the two integrands coincide, so the
    identity is PURE Fubini/Tonelli algebra — NOT the analytic (Gaussian-bound) convergence wall.

    This theorem PROVES, with no side hypotheses, the two constant-pull-out steps (the scalar
    `C s z y` pulls through the inner `∫₀^{t−s} ∫_w` on the left; `A(t−u) x w` pulls into the inner
    `∫₀^{u} ∫_z` on the right — both by `intervalIntegral.integral_mul_const`/`integral_const_mul`,
    unconditional linearity).  It then REDUCES the identity to three explicit, non-vacuous carried
    Fubini facts (each a genuine equality of a *fixed* four-fold integrand under a permuted
    integration order — none is the conclusion, none is `True`, all hold whenever the joint integrand
    is integrable):

    * `hReorderL` — the spatial/temporal reordering on the LEFT: move the `∫_z` inward past
      `∫₀^{t−s}` and `∫_w` (the `∫_z`↔`∫_w` swap is exactly `heatConv_spatial_fubini`);
    * `hTri` — the **time-triangle Fubini** `∫₀ᵗ∫₀^{t−s} = ∫₀ᵗ∫₀^{u}` with the substitution
      `u = s+s', u' = s`.  Mathlib has NO direct triangular interval-integral Fubini lemma
      (only `regionBetween` volume formulae / group-translation `convolution_assoc`), so THIS is the
      reachable-in-principle-but-Mathlib-missing carry;
    * `hReorderR` — the mirror spatial/temporal reordering on the RIGHT (move `∫_w` inward past
      `∫₀^{u}` and `∫_z`).

    NB: this is genuine measure-theoretic algebra (Fubini), explicitly SEPARATED from the
    Neumann-series convergence wall and from `a₁ = R/6`. -/
theorem heatConv_assoc (A B C : ℝ → Point n → Point n → ℝ) (t : ℝ) (x y : Point n)
    (hReorderL :
      (∫ s in (0)..t, ∫ z, ∫ s' in (0)..(t - s), ∫ w,
          A (t - s - s') x w * B s' w z * C s z y)
        = ∫ s in (0)..t, ∫ s' in (0)..(t - s), ∫ w, ∫ z,
          A (t - s - s') x w * B s' w z * C s z y)
    (hTri :
      (∫ s in (0)..t, ∫ s' in (0)..(t - s), ∫ w, ∫ z,
          A (t - s - s') x w * B s' w z * C s z y)
        = ∫ u in (0)..t, ∫ u' in (0)..u, ∫ w, ∫ z,
          A (t - u) x w * B (u - u') w z * C u' z y)
    (hReorderR :
      (∫ u in (0)..t, ∫ w, ∫ u' in (0)..u, ∫ z,
          A (t - u) x w * B (u - u') w z * C u' z y)
        = ∫ u in (0)..t, ∫ u' in (0)..u, ∫ w, ∫ z,
          A (t - u) x w * B (u - u') w z * C u' z y) :
    heatConv (heatConvK A B) C t x y = heatConv A (heatConvK B C) t x y := by
  have hP1 : heatConv (heatConvK A B) C t x y
      = ∫ s in (0)..t, ∫ z, ∫ s' in (0)..(t - s), ∫ w,
          A (t - s - s') x w * B s' w z * C s z y := by
    simp only [heatConv, heatConvK]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr (fun s' _ => ?_)
    rw [← integral_mul_const]
  have hP2 : heatConv A (heatConvK B C) t x y
      = ∫ u in (0)..t, ∫ w, ∫ u' in (0)..u, ∫ z,
          A (t - u) x w * B (u - u') w z * C u' z y := by
    simp only [heatConv, heatConvK]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    dsimp only
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u' _ => ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    ring
  rw [hP1, hReorderL, hTri, ← hReorderR]
  exact hP2.symm

end QIQTH.HeatDuhamel
