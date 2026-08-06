/-
  GaussLemmaTransverse — the TRANSVERSE (Jacobi-field) conservation leg of the Gauss lemma
  for the geodesic exponential map, toward discharging `hGauss` (brick J4-342, the hGauss
  derivation campaign of the a₁ = R/6 heat-kernel tower).

  ⚠ HONESTY FIREWALL (binding).  This file is **NOT** a proof of `a₁ = R/6`.  The a₁ = R/6 milestone
  remains CONDITIONAL: `hGauss` is one of the four labelled inputs of `a1_R6_from_labelled`, and this
  campaign works toward discharging it for the exp-pullback normal-form metric.  This file delivers
  the TRANSVERSE LEG of that program (the metric-compatible transverse conservation `d/dt g(J,γ̇) =
  g(∇J,γ̇)` along a geodesic, and its two-step integration to linear growth).  Nothing here builds
  normal coordinates, moves numerical-G, or closes a₁ = R/6.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE MATH (classical Gauss-lemma transverse conservation, done honestly in the pd-calculus)
  ─────────────────────────────────────────────────────────────────────────────────────────────
  Notation.  `Point n = Fin n → ℝ`.  Metric `g`, inverse `gi`, `christoffel g gi μ ν ρ x = Γ^μ_{νρ}`,
  `pd f i x = ∂ᵢ f`.  A geodesic `γ` has velocity `u = γ̇`, acceleration `acc = γ̈ = −Γ(γ̇,γ̇)`.
  A Jacobi field `J` along `γ` has ordinary derivative `J'`; its covariant derivative along `γ` is
  `(∇J)^a = J'^a + ∑_{c,d} Γ^a_{cd} u^c J^d`.  The transverse pairing is
    `E_J(t) = ∑_{a,b} g_{ab}(γ t) · J(t)^a · γ̇(t)^b`.

  STEP T1 (the heart).  Differentiating `E_J` along the geodesic and substituting `acc = −Γ(γ̇,γ̇)`,
  metric compatibility `∂_c g_{ab} = ∑σ Γ^σ_{ca} g_{σb} + ∑σ Γ^σ_{cb} g_{aσ}` (`metric_compat`)
  collapses the ∂g-term against the acceleration term, leaving exactly the covariant pairing:
    `d/dt E_J = ∑_{a,b} g_{ab} (∇J)^a u^b`.
  This is PURE metric-compatibility algebra (no ODE, no smoothness): the raw derivative
  `∑[(∂_c g_{ab} u^c) J^a u^b + g_{ab} J'^a u^b + g_{ab} J^a acc^b]` equals the covariant pairing.
  (T1a = the algebra; T1b = the pointwise chain-rule `HasDerivAt`.)

  STEP T2.  Applying the SAME algebra to `∇J` in the first slot (the second-slot `∇γ̇ = 0` term
  drops by the geodesic equation) gives `d/dt[∑ g_{ab}(∇J)^a u^b] = ∑ g_{ab}(∇∇J)^a u^b`; the Jacobi
  equation `∇∇J = −R(J,γ̇)γ̇` and the curvature scalar `g(R(J,γ̇)γ̇, γ̇) = 0` make it vanish.
  The T1 algebra lemma is REUSED verbatim (it is stated for an arbitrary first-slot vector, not just
  a Jacobi field), so T2's differentiation step is `transverse_pairing_hasDerivAt` applied to `∇J`.

  CURVATURE-VANISHING VERDICT (honest).  The needed scalar `∑_a g_{ab}(R(J,γ̇)γ̇)^a γ̇^b` vanishes by
  the FIRST-pair antisymmetry of the lowered Riemann tensor contracted with `γ̇⊗γ̇`; that
  antisymmetry is a metric-compatibility consequence whose GENERAL-POINT coordinate derivation is a
  heavy separate brick.  Per the honest alternative, T2/T3 are proved CONDITIONAL on the named,
  satisfiable hypothesis that the second-covariant pairing vanishes (it IS true for Jacobi fields);
  discharging it is its own downstream brick.

  STEP T3.  `E_J' = W` (T1b) and `W' = 0` (T2) ⟹ `W` constant ⟹ `E_J(t) = E_J(0) + t·W(0)` (linear
  growth), integrated on the exp-tube.

  DELIVERED (fully derived, axiom-free, no `sorry`):
   • `transverse_pairing_deriv_eq_covariant` (T1a) — the algebraic heart: the raw derivative of the
     transverse pairing equals the covariant pairing (pure `metric_compat` algebra; no ODE).
   • `pairing_hasDerivAt_along_geodesic` — the pointwise chain-rule derivative of a general
     first-slot pairing along any integral curve of `geodesicField` (the G1b analog, reused twice).
   • `transverse_pairing_hasDerivAt` (T1b) — `HasDerivAt E_J (covariant pairing) t`.
   • `covariant_pairing_hasDerivAt_zero` (T2b) — `HasDerivAt W 0 t`, CONDITIONAL on the covariant
     second-derivative curve datum + the (satisfiable) curvature-vanishing hypothesis.
   • `gauss_transverse_linear` (T3) — the two-step integration to `E_J(t) = E_J(0) + t·W(0)`.

  ⚠ NOT a₁ = R/6; NOT unconditional (the curvature-vanishing is a labelled satisfiable carry).
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.Geodesic
import QIQTH.ExpMap
import QIQTH.GaussLemmaFirstVariation

namespace QIQTH.GaussLemmaTransverse

open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### Index-permutation helpers for the T1a triple/quadruple sum reindexings. -/

/-- Swap the 1st and 3rd summation variables of a triple sum. -/
private theorem sum3_swap13 (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ b, ∑ c, ∑ e, F b c e) = ∑ e, ∑ c, ∑ b, F b c e := by
  calc (∑ b, ∑ c, ∑ e, F b c e)
      = ∑ b, ∑ e, ∑ c, F b c e := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ e, ∑ b, ∑ c, F b c e := Finset.sum_comm
    _ = ∑ e, ∑ c, ∑ b, F b c e := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_comm

/-- Swap the 1st and 4th summation variables of a quadruple sum. -/
private theorem sum4_swap14 (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ e, F a b c e) = ∑ e, ∑ b, ∑ c, ∑ a, F a b c e := by
  calc (∑ a, ∑ b, ∑ c, ∑ e, F a b c e)
      = ∑ b, ∑ a, ∑ c, ∑ e, F a b c e := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ e, F a b c e := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ e, ∑ a, F a b c e := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ b, ∑ e, ∑ c, ∑ a, F a b c e := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ e, ∑ b, ∑ c, ∑ a, F a b c e := Finset.sum_comm

/-- Reindex the covariant-first term: `∑ (∑σ Γ^σ_{ca} g_{σb}) u^c J^a u^b = ∑ g_{ab} Γ^a_{cd} u^c J^d u^b`
    (`= R`, the covariant-derivative pairing term).  Pure 4-index permutation. -/
private theorem reindex_covariant_first (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (u J : Fin n → ℝ) :
    (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c a x * g x σ b) * u c) * J a * u b)
    = ∑ a, ∑ b, g x a b * (∑ c, ∑ d, christoffel g gi a c d x * u c * J d) * u b := by
  have hL : (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c a x * g x σ b) * u c) * J a * u b)
      = ∑ a, ∑ b, ∑ c, ∑ σ, christoffel g gi σ c a x * g x σ b * u c * J a * u b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.sum_mul]
  have hR : (∑ a, ∑ b, g x a b * (∑ c, ∑ d, christoffel g gi a c d x * u c * J d) * u b)
      = ∑ a, ∑ b, ∑ c, ∑ d, christoffel g gi a c d x * g x a b * u c * J d * u b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hL, hR]
  exact sum4_swap14 (fun a b c e => christoffel g gi e c a x * g x e b * u c * J a * u b)

/-- Reindex the acceleration term: `∑ (∑σ Γ^σ_{cb} g_{aσ}) u^c J^a u^b = ∑ Γ^b_{cd} g_{ab} u^c J^a u^d`.
    Pure permutation (swap of the inner triple under the outer `a`). -/
private theorem reindex_acceleration (g gi : Point n → Fin n → Fin n → ℝ)
    (x : Point n) (u J : Fin n → ℝ) :
    (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c b x * g x a σ) * u c) * J a * u b)
    = ∑ a, ∑ b, ∑ c, ∑ d, christoffel g gi b c d x * g x a b * u c * J a * u d := by
  have hL : (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c b x * g x a σ) * u c) * J a * u b)
      = ∑ a, ∑ b, ∑ c, ∑ σ, christoffel g gi σ c b x * g x a σ * u c * J a * u b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.sum_mul]
  rw [hL]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact sum3_swap13 (fun b c σ => christoffel g gi σ c b x * g x a σ * u c * J a * u b)

/-! ### T1a — the algebraic heart: the raw transverse-pairing derivative = the covariant pairing. -/

/-- **T1a — the transverse first-variation algebra.**  For a geodesic with velocity `u` and
    acceleration `acc = −Γ(u,u)` (`hacc`), and a Jacobi field with components `J` and ordinary
    derivative `Jp`, the raw total `t`-derivative of the transverse pairing
    `∑ g_{ab} J^a u^b` equals the covariant pairing `∑ g_{ab}(∇J)^a u^b`, where
    `(∇J)^a = Jp^a + ∑_{c,d} Γ^a_{cd} u^c J^d`.  Pure metric-compatibility algebra
    (`metric_compat`) — no ODE, no smoothness.  ⚠ NOT a₁ = R/6. -/
theorem transverse_pairing_deriv_eq_covariant
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n)
    (hinv : ∀ a b, (∑ σ, g x a σ * gi x σ b) = if a = b then 1 else 0)
    (u J Jp acc : Fin n → ℝ)
    (hacc : ∀ b, acc b = -∑ c, ∑ d, christoffel g gi b c d x * u c * u d) :
    (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c x * u c) * J a * u b
              + g x a b * Jp a * u b + g x a b * J a * acc b))
    = ∑ a, ∑ b, g x a b * (Jp a + ∑ c, ∑ d, christoffel g gi a c d x * u c * J d) * u b := by
  classical
  -- metric compatibility as the ∂g identity
  have hmc : ∀ a b c, pd (fun y => g y a b) c x
      = (∑ σ, christoffel g gi σ c a x * g x σ b)
        + (∑ σ, christoffel g gi σ c b x * g x a σ) := by
    intro a b c
    have h := metric_compat g gi hsymm x hinv c a b
    simp only [covDeriv02] at h
    linarith
  -- split the raw derivative's ∂g term via hmc into LAI + LAII.
  have hP : (∑ a, ∑ b, (∑ c, pd (fun y => g y a b) c x * u c) * J a * u b)
      = (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c a x * g x σ b) * u c) * J a * u b)
        + (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c b x * g x a σ) * u c) * J a * u b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (∑ c, pd (fun y => g y a b) c x * u c)
          = (∑ c, (∑ σ, christoffel g gi σ c a x * g x σ b) * u c)
            + (∑ c, (∑ σ, christoffel g gi σ c b x * g x a σ) * u c) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hmc a b c]; ring]
    ring
  -- the acceleration term cancels the covariant-first extra term (LAII).
  have hcancel :
      (∑ a, ∑ b, (∑ c, (∑ σ, christoffel g gi σ c b x * g x a σ) * u c) * J a * u b)
        + (∑ a, ∑ b, g x a b * J a * acc b) = 0 := by
    rw [reindex_acceleration, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hacc b, mul_neg,
        show g x a b * J a * (∑ c, ∑ d, christoffel g gi b c d x * u c * u d)
          = ∑ c, ∑ d, christoffel g gi b c d x * g x a b * u c * J a * u d from by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring]
    ring
  -- assemble
  have hsplit :
      (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c x * u c) * J a * u b
                + g x a b * Jp a * u b + g x a b * J a * acc b))
      = (∑ a, ∑ b, (∑ c, pd (fun y => g y a b) c x * u c) * J a * u b)
        + (∑ a, ∑ b, g x a b * Jp a * u b)
        + (∑ a, ∑ b, g x a b * J a * acc b) := by
    simp only [Finset.sum_add_distrib]
  have hRHS :
      (∑ a, ∑ b, g x a b * (Jp a + ∑ c, ∑ d, christoffel g gi a c d x * u c * J d) * u b)
      = (∑ a, ∑ b, g x a b * Jp a * u b)
        + (∑ a, ∑ b, g x a b * (∑ c, ∑ d, christoffel g gi a c d x * u c * J d) * u b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit, hP, hRHS, ← reindex_covariant_first g gi x u J]
  linarith [hcancel]

/-! ### The pointwise chain-rule derivative of a general first-slot pairing (G1b analog). -/

/-- **Pairing chain-rule (the G1b analog, reused for both `J` and `∇J`).**  For any `C¹` metric,
    any curve `Y` solving the geodesic ODE at `t`, and any vector-curve `K` (first slot) whose
    components are differentiable at `t` (derivative `K'`), the pairing
    `∑_{a,b} g_{ab}((Y s).1)·(K s)^a·(Y s).2^b` has the explicit product-rule derivative
    (radial ∂g-term + the two slots).  Pure chain/product rule; no metric-compatibility algebra. -/
theorem pairing_hasDerivAt_along_geodesic
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (Y : ℝ → Point n × Point n) (K : ℝ → Point n) (K' : Fin n → ℝ) {t : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y t)) t)
    (hK : ∀ a, HasDerivAt (fun s => K s a) (K' a) t) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (Y s).1 a b * K s a * (Y s).2 b)
      (∑ a, ∑ b, ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * K t a * (Y t).2 b
                + g (Y t).1 a b * K' a * (Y t).2 b
                + g (Y t).1 a b * K t a * (geodesicField g gi (Y t)).2 b)) t := by
  classical
  have hpos : HasDerivAt (fun s => (Y s).1) ((Y t).2) t := by
    simpa [geodesicField] using
      (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t hYd
  have hvel : HasDerivAt (fun s => (Y s).2) ((geodesicField g gi (Y t)).2) t := by
    simpa using
      (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t hYd
  have hu : ∀ b, HasDerivAt (fun s => (Y s).2 b) ((geodesicField g gi (Y t)).2 b) t := by
    intro b
    simpa using (ContinuousLinearMap.proj b).hasFDerivAt.comp_hasDerivAt t hvel
  have hgab : ∀ a b, HasDerivAt (fun s => g (Y s).1 a b)
      (∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) t := by
    intro a b
    have hcomp := ((hg a b).differentiableAt (x := (Y t).1)).hasFDerivAt.comp_hasDerivAt t hpos
    rwa [fderiv_apply_eq_sum_pd (fun y => g y a b) (Y t).1 ((Y t).2)
        ((hg a b).differentiableAt)] at hcomp
  have hsummand : ∀ a b, HasDerivAt (fun s => g (Y s).1 a b * K s a * (Y s).2 b)
      ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * K t a * (Y t).2 b
        + g (Y t).1 a b * K' a * (Y t).2 b
        + g (Y t).1 a b * K t a * (geodesicField g gi (Y t)).2 b) t := by
    intro a b
    have h := ((hgab a b).mul (hK a)).mul (hu b)
    rw [show (∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * K t a * (Y t).2 b
          + g (Y t).1 a b * K' a * (Y t).2 b
          + g (Y t).1 a b * K t a * (geodesicField g gi (Y t)).2 b
        = ((∑ c, pd (fun y => g y a b) c (Y t).1 * (Y t).2 c) * K t a
            + g (Y t).1 a b * K' a) * (Y t).2 b
          + g (Y t).1 a b * K t a * (geodesicField g gi (Y t)).2 b from by ring]
    exact h
  have h := HasDerivAt.sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
    HasDerivAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin n))) => hsummand a b))
  have hfun : (fun s => ∑ a, ∑ b, g (Y s).1 a b * K s a * (Y s).2 b)
      = (∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ,
          fun s => g (Y s).1 a b * K s a * (Y s).2 b) := by
    funext s; simp only [Finset.sum_apply]
  rw [hfun]; exact h

/-! ### T1b — the step-1 `HasDerivAt`: `d/dt E_J = ∑ g(∇J, γ̇)`. -/

/-- **T1b — the transverse pairing derivative equals the covariant pairing.**  Along a geodesic-ODE
    curve `Y` of a symmetric, invertible, `C¹` metric, with a Jacobi field `J` (components `J s a`,
    derivative `Jp`), the transverse pairing `E_J s = ∑ g_{ab} J^a γ̇^b` has derivative
    `∑ g_{ab}(∇J)^a γ̇^b` with `(∇J)^a = Jp^a + ∑ Γ^a_{cd} γ̇^c J^d` — the T1a algebra applied to the
    raw product-rule derivative.  ⚠ NOT a₁ = R/6. -/
theorem transverse_pairing_hasDerivAt
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (Y : ℝ → Point n × Point n) (J : ℝ → Point n) (Jp : Fin n → ℝ) {t : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y t)) t)
    (hJ : ∀ a, HasDerivAt (fun s => J s a) (Jp a) t) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (Y s).1 a b * J s a * (Y s).2 b)
      (∑ a, ∑ b, g (Y t).1 a b
        * (Jp a + ∑ c, ∑ d, christoffel g gi a c d (Y t).1 * (Y t).2 c * J t d)
        * (Y t).2 b) t := by
  have hbase := pairing_hasDerivAt_along_geodesic g gi hg Y J Jp hYd hJ
  have hacc : ∀ b, (geodesicField g gi (Y t)).2 b
      = -∑ c, ∑ d, christoffel g gi b c d (Y t).1 * (Y t).2 c * (Y t).2 d := fun b => by
    simp only [geodesicField]
  rwa [transverse_pairing_deriv_eq_covariant g gi hsymm (Y t).1 (hinv (Y t).1)
        ((Y t).2) (J t) Jp ((geodesicField g gi (Y t)).2) hacc] at hbase

/-! ### T2b — the step-2 `HasDerivAt`: `d/dt W = 0` (via Jacobi + curvature vanishing). -/

/-- **T2b — the covariant pairing has zero derivative.**  Let `cJ` be the covariant-derivative curve
    `∇J` along the geodesic (components `cJ s a`, derivative `cJp`).  Then `W s = ∑ g_{ab}(cJ)^a γ̇^b`
    (the covariant pairing) has derivative `0` at `t`, PROVIDED the second-covariant pairing
    `∑ g_{ab}(∇cJ)^a γ̇^b` vanishes (`hvanish`).

    ⚠ HONESTY (labelled carry).  `hvanish` is the Jacobi-equation + curvature-antisymmetry input:
    `∇cJ = ∇∇J = −R(J,γ̇)γ̇` and `g(R(J,γ̇)γ̇, γ̇) = 0` (first-pair antisymmetry of the lowered
    Riemann tensor contracted with `γ̇⊗γ̇`).  It IS true for Jacobi fields; its general-point
    coordinate derivation is a separate downstream brick.  This theorem discharges the DIFFERENTIATION
    step (the T1a algebra applied to `∇J`), reducing the transverse conservation to that one input. -/
theorem covariant_pairing_hasDerivAt_zero
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, Differentiable ℝ (fun y => g y a b))
    (Y : ℝ → Point n × Point n) (cJ : ℝ → Point n) (cJp : Fin n → ℝ) {t : ℝ}
    (hYd : HasDerivAt Y (geodesicField g gi (Y t)) t)
    (hcJ : ∀ a, HasDerivAt (fun s => cJ s a) (cJp a) t)
    (hvanish : (∑ a, ∑ b, g (Y t).1 a b
        * (cJp a + ∑ c, ∑ d, christoffel g gi a c d (Y t).1 * (Y t).2 c * cJ t d)
        * (Y t).2 b) = 0) :
    HasDerivAt (fun s => ∑ a, ∑ b, g (Y s).1 a b * cJ s a * (Y s).2 b) 0 t := by
  have h := transverse_pairing_hasDerivAt g gi hsymm hinv hg Y cJ cJp hYd hcJ
  rwa [hvanish] at h

/-! ### T3 — the two-step integration to linear growth. -/

/-- **T3 — transverse linear growth (the double-constancy integration).**  Given the two-step
    conservation as derivative families on `(-2,2)` — `E' = W` (T1b at each point) and `W' = 0`
    (T2b at each point) — the transverse pairing grows linearly:
      `E t = E 0 + t · W 0`   for `t ∈ [0,1]`.
    Integrates `W = W 0` (constancy of the covariant pairing) once more into `E`.
    ⚠ NOT a₁ = R/6; conditional on the T2b curvature-vanishing input. -/
theorem gauss_transverse_linear
    (E W : ℝ → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hE : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt E (W s) s)
    (hW : ∀ s ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt W 0 s) :
    E t = E 0 + t * W 0 := by
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- W is constant on [0,1]
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) 1) := fun x hx =>
    (hW x (hsub hx)).continuousAt.continuousWithinAt
  have hWderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt W 0 (Set.Ici x) x := fun x hx =>
    (hW x (hsub (Set.Ico_subset_Icc_self hx))).hasDerivWithinAt
  have hWconst : ∀ s ∈ Set.Icc (0 : ℝ) 1, W s = W 0 := fun s hs =>
    constant_of_has_deriv_right_zero hWcont hWderiv s hs
  -- h(s) = E s − s·W 0 has derivative 0 on [0,1]
  have hHcont : ContinuousOn (fun r => E r - r * W 0) (Set.Icc (0 : ℝ) 1) := fun x hx =>
    ((hE x (hsub hx)).sub ((hasDerivAt_id x).mul_const (W 0))).continuousAt.continuousWithinAt
  have hHderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun r => E r - r * W 0) 0 (Set.Ici x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
    have hd := (hE x (hsub hx')).sub ((hasDerivAt_id x).mul_const (W 0))
    rw [hWconst x hx', show W 0 - 1 * W 0 = 0 from by ring] at hd
    exact hd.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hHcont hHderiv t ht
  simp only [zero_mul, sub_zero] at hconst
  linarith [hconst]

end QIQTH.GaussLemmaTransverse
