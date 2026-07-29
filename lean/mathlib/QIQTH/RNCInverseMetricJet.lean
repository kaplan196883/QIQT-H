/-
  RNCInverseMetricJet — the RNC **inverse-metric** second-order jet.

  Upgrades the (c2) piece-(IV) isolation of the M5 cancellation
  (`VanVleckCancellation`, `HeatResidualBound.parametrixResidual_offdiag_absorbed`), whose residue is
  the metric-deviation cross-gradient `Σᵢⱼ (gⁱʲ − δⁱʲ)(∂ᵢG)(∂ⱼP)`, to the CLOSED curvature leading
  coefficient of the inverse-metric deviation.

  GOAL.  The Riemann-normal-coordinate inverse-metric 2-jet
      `gⁱʲ(v) − δⁱʲ = ⅓ · Σ_{α,β} R_{iαjβ}(0) · vᵃ · vᵝ + o(‖v‖²)`,
  i.e. at the level of the `pd` calculus of `QIQTH/Curvature.lean`, the inverse-metric Hessian
      `∂_a∂_b gⁱʲ(0) = +⅓ · (curvature combination)`.

  ─────────────────────────────────────────────────────────────────────────────────────────────────
  ASSESSMENT (recorded honestly; the deliverable's scope depends on it).

  • The full metric TENSOR 2-jet `∂_a∂_b g_{ij}(0) = −⅓(R_{iajb}+R_{ibja})` is **absent from Mathlib**
    (no `normalCoord`/`RiemannianMetric` Taylor expansion for the concrete `Point n → matrix` setup),
    and is **not a standalone lemma** anywhere in the repo either.  What the repo DID have is only the
    √det / trace-level version (`RNCExpansion.sqrtdet_pd_pd`, `rnc_htr_of_gauge`:
    `∑_a ∂_c∂_d g_{aa}(0) = −⅔ Ric_{cd}`) and the FORWARD local-inertial formula
    (`rnc_riemann_hessian`: Riemann *in terms of* the metric Hessian).

  • HOWEVER the metric tensor 2-jet is **reachable** from the existing Christoffel machinery — it is
    ONE brick, not a foundational wall.  From `pd_christoffel_origin` (gauge-free) applied to the two
    orderings `Γ^i_{bj}`, `Γ^j_{bi}` plus metric symmetry, one gets the pure-calculus identity
      `∂_a∂_b g_{ij}(0) = ∂_a Γ^i_{bj}(0) + ∂_a Γ^j_{bi}(0)`   (`pd_pd_metric_eq_sum_pd_christoffel`),
    and feeding the gauge-derived `pd_christoffel_solve`
      `∂_a Γ^i_{bc}(0) = ⅓(R^i_{bac} + R^i_{cab})`
    gives the closed metric tensor 2-jet (`rnc_metric_hessian`, gauge-conditional).  Its trace over
    `i=j` reproduces `−⅔ Ric` (via `sum_riemann_ii_zero` + Ricci antisymmetry), an exact cross-check
    against `rnc_htr_of_gauge`.

  ─────────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS FILE LANDS.

  (Core, UNCONDITIONAL — no gauge, no carried jet.)  The inverse-metric Hessian is minus the metric
  Hessian at an RNC centre: with `g(0)=δ`, `∂g(0)=0`, and `gi` the genuine (pointwise) inverse field
  `∑_σ gⁱˢ g_{σj} = δⁱ_j`,
      `∂_a∂_b gⁱʲ(0) = − ∂_a∂_b g_{ij}(0)`                          (`pd_pd_gInv_eq_neg_metric`),
  proved directly in the `pd` calculus by twice-differentiating the inverse relation (the `∂g(0)=0`
  and derived `∂gi(0)=0` cross terms drop).  This is the sign flip that turns the metric deviation
  `−⅓R` into the inverse-metric deviation `+⅓R`.

  (F1 — full, gauge-conditional.)  Combining the sign flip with the gauge-derived metric tensor 2-jet:
      `∂_a∂_b gⁱʲ(0) = −⅓ (R^i_{baj} + R^i_{jab} + R^j_{bai} + R^j_{iab})(0)`   (`rnc_gInv_hessian`),
  with `R = riemann g gi` and, at the RNC centre `g(0)=δ`, `R^i_{...} = R_{i...}` — the closed
  curvature leading coefficient of the inverse-metric deviation, i.e. exactly the
  `gⁱʲ(v) − δⁱʲ = ⅓ R_{iαjβ}vᵃvᵝ + o(r²)` jet in Hessian form.  The gauge here is the SAME
  load-bearing normal-coordinate gauge (`hgauge`, `∂_{(a}Γ^i_{bc)}(0)=0`) that the repo's √det chain
  already carries; removing it makes the closed `R`-value false.

  (F2 — abstract algebraic reduction.)  `rnc_gInv_twojet_of_metricJet`: for ANY carried metric-Hessian
  tensor `C` with `∂_a∂_b g_{ij}(0) = C a b i j`, the inverse jet is `∂_a∂_b gⁱʲ(0) = − C a b i j`.
  The inverse-from-metric-jet algebra is thus isolated from whatever supplies the metric jet.

  HONEST CAPTION (binding).  The UNCONDITIONAL content is the sign-flip `∂∂gⁱʲ = −∂∂g` from the genuine
  inverse relation.  The closed `R`-VALUE (`rnc_gInv_hessian`) is conditional on the normal-coordinate
  gauge — the same standard RNC input the √det chain carries, NOT a new axiom.  This is the inverse
  2-jet only; it does NOT give the numerical value of G, and does NOT close the M5 off-diagonal
  `O(1/t)` cancellation (that still needs the radial `∂_r log det g̃` Jacobi identity — see
  `VanVleckCancellation` checkpoint).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.RNCExpansion

set_option maxHeartbeats 1600000

namespace QIQTH.RNCExpansion

open QIQTH.Curvature
open Finset Matrix

variable {n : ℕ}

/-! ### The unconditional inverse-metric Hessian sign flip -/

/-- **First derivative of the inverse metric vanishes at an RNC centre.**  With `g(0)=δ`, `∂g(0)=0`,
    and `gi` the genuine (left) inverse field `∑_σ gⁱˢ g_{σj} = δⁱ_j`, once-differentiating the inverse
    relation gives `∂_e gⁱʲ(0) = 0`.  (The `gⁱ_σ ∂_e g_{σj}` term drops by `∂g(0)=0`.)  Unconditional
    — no gauge, no carried jet. -/
theorem pd_gInv_first_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (i j e : Fin n) :
    pd (fun y => gi y i j) e 0 = 0 := by
  -- the inverse product is a constant field, so its `∂_e` is `0`.
  have hzero : pd (fun y => ∑ σ, gi y i σ * g y σ j) e 0 = 0 := by
    rw [show (fun y => ∑ σ, gi y i σ * g y σ j) = (fun _ => (if i = j then (1 : ℝ) else 0))
          from funext (fun y => hinv y i j)]
    exact pd_const _ e 0
  -- expand by sum-Leibniz.
  have hexp : pd (fun y => ∑ σ, gi y i σ * g y σ j) e 0
      = ∑ σ, (pd (fun y => gi y i σ) e 0 * g 0 σ j + gi 0 i σ * pd (fun y => g y σ j) e 0) := by
    rw [pd_sum univ _ e 0 (fun σ _ => (PdiffAt_of_contDiff _ (hgi i σ) e 0).mul
          (PdiffAt_of_contDiff _ (hg σ j) e 0))]
    exact Finset.sum_congr rfl (fun σ _ => pd_mul _ _ e 0
      (PdiffAt_of_contDiff _ (hgi i σ) e 0) (PdiffAt_of_contDiff _ (hg σ j) e 0))
  rw [hexp] at hzero
  -- kill `∂g(0)=0` terms, collapse the `δ`-diagonal.
  simp only [hdg0, mul_zero, add_zero, hg0, Matrix.one_apply, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hzero
  exact hzero

/-- **The inverse-metric Hessian is minus the metric Hessian at an RNC centre.**  With `g(0)=δ`,
    `∂g(0)=0`, and `gi` the genuine inverse field, twice-differentiating the inverse relation
    `∑_σ gⁱˢ g_{σj} = δⁱ_j` and dropping the `∂g(0)=0` / `∂gi(0)=0` cross terms gives
      `∂_a∂_b gⁱʲ(0) = − ∂_a∂_b g_{ij}(0)`.
    This is the sign flip carrying the metric deviation `−⅓R` to the inverse-metric deviation `+⅓R`.
    UNCONDITIONAL: no gauge, no carried jet. -/
theorem pd_pd_gInv_eq_neg_metric (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => gi w i j) b y) a 0
      = - pd (fun y => pd (fun w => g w i j) b y) a 0 := by
  -- derived `gi(0)=δ` from the inverse relation at `0`.
  have hgi0 : ∀ p q, gi 0 p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q := by
    intro p q
    have h := hinv 0 p q
    rw [show (∑ σ, gi 0 p σ * g 0 σ q) = gi 0 p q from by
          rw [Finset.sum_eq_single q (fun σ _ hσ => by
                rw [hg0 σ q, Matrix.one_apply_ne hσ, mul_zero])
              (fun hq => absurd (Finset.mem_univ q) hq)]
          rw [hg0 q q, Matrix.one_apply_eq, mul_one]] at h
    rw [Matrix.one_apply]; exact h
  -- `∂gi(0)=0`.
  have hdgi0 : ∀ p q e, pd (fun y => gi y p q) e 0 = 0 := fun p q e =>
    pd_gInv_first_zero g gi hg hgi hg0 hdg0 hinv p q e
  -- the once-differentiated inverse product, expanded, as a field on all of the chart.
  have hΨeq : (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y)
      = (fun y => ∑ σ, (pd (fun w => gi w i σ) b y * g y σ j
                        + gi y i σ * pd (fun w => g w σ j) b y)) := by
    funext y
    rw [pd_sum univ _ b y (fun σ _ => (PdiffAt_of_contDiff _ (hgi i σ) b y).mul
          (PdiffAt_of_contDiff _ (hg σ j) b y))]
    exact Finset.sum_congr rfl (fun σ _ => pd_mul _ _ b y
      (PdiffAt_of_contDiff _ (hgi i σ) b y) (PdiffAt_of_contDiff _ (hg σ j) b y))
  -- LHS: `∂_a` of the constant `∂_b(inverse product)` is `0`.
  have hconst2 : pd (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y) a 0 = 0 := by
    rw [show (fun y => pd (fun w => ∑ σ, gi w i σ * g w σ j) b y) = (fun _ => (0 : ℝ)) from
          funext (fun y => by
            rw [show (fun w => ∑ σ, gi w i σ * g w σ j)
                  = (fun _ => (if i = j then (1 : ℝ) else 0)) from funext (fun w => hinv w i j)]
            exact pd_const _ b y)]
    exact pd_const 0 a 0
  rw [hΨeq] at hconst2
  -- per-`σ` outer Leibniz, with the vanishing `∂g(0)`, `∂gi(0)` factors removed.
  have hσ : ∀ σ : Fin n,
      pd (fun y => pd (fun w => gi w i σ) b y * g y σ j + gi y i σ * pd (fun w => g w σ j) b y) a 0
        = pd (fun y => pd (fun w => gi w i σ) b y) a 0 * g 0 σ j
          + gi 0 i σ * pd (fun y => pd (fun w => g w σ j) b y) a 0 := by
    intro σ
    rw [pd_add _ _ a 0
          ((PdiffAt_pd (fun w => gi w i σ) (hgi i σ) b a 0).mul (PdiffAt_of_contDiff _ (hg σ j) a 0))
          ((PdiffAt_of_contDiff _ (hgi i σ) a 0).mul (PdiffAt_pd (fun w => g w σ j) (hg σ j) b a 0)),
        pd_mul (fun y => pd (fun w => gi w i σ) b y) (fun y => g y σ j) a 0
          (PdiffAt_pd (fun w => gi w i σ) (hgi i σ) b a 0) (PdiffAt_of_contDiff _ (hg σ j) a 0),
        pd_mul (fun y => gi y i σ) (fun y => pd (fun w => g w σ j) b y) a 0
          (PdiffAt_of_contDiff _ (hgi i σ) a 0) (PdiffAt_pd (fun w => g w σ j) (hg σ j) b a 0),
        hdgi0 i σ b, hdgi0 i σ a, hdg0 σ j b]
    ring
  -- assemble: `∂_a` distributes over the `σ`-sum, then apply the per-`σ` identity.
  rw [pd_sum univ _ a 0 (fun σ _ =>
        ((PdiffAt_pd (fun w => gi w i σ) (hgi i σ) b a 0).mul (PdiffAt_of_contDiff _ (hg σ j) a 0)).add
        ((PdiffAt_of_contDiff _ (hgi i σ) a 0).mul (PdiffAt_pd (fun w => g w σ j) (hg σ j) b a 0))),
      Finset.sum_congr rfl (fun σ _ => hσ σ)] at hconst2
  -- collapse the `δ`-diagonals: LHS-sum = `∂∂gi_ij(0) + ∂∂g_ij(0) = 0`.
  simp only [hg0, hgi0, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    at hconst2
  linarith [hconst2]

/-! ### The gauge-derived metric tensor 2-jet (reachable from the Christoffel machinery) -/

/-- **The metric Hessian is the sum of the two Christoffel-derivative orderings** (gauge-free).  From
    `pd_christoffel_origin` applied to `Γ^i_{bj}` and `Γ^j_{bi}` plus metric symmetry, the mixed
    `∂∂g` cross terms cancel, leaving `∂_a∂_b g_{ij}(0) = ∂_a Γ^i_{bj}(0) + ∂_a Γ^j_{bi}(0)`.  Pure
    calculus at the RNC centre — no gauge. -/
theorem pd_pd_metric_eq_sum_pd_christoffel (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => g w i j) b y) a 0
      = pd (fun y => christoffel g gi i b j y) a 0 + pd (fun y => christoffel g gi j b i y) a 0 := by
  rw [pd_christoffel_origin g gi hg hgi hgi0 hdg0 i b j a,
      pd_christoffel_origin g gi hg hgi hgi0 hdg0 j b i a]
  -- symmetry of the metric ⇒ equality of the mixed second-derivative fields.
  have hAA : pd (fun y => pd (fun w => g w j i) b y) a 0 = pd (fun y => pd (fun w => g w i j) b y) a 0 := by
    rw [show (fun w => g w j i) = (fun w => g w i j) from funext (fun w => hsymm w j i)]
  have hBC : pd (fun y => pd (fun w => g w i b) j y) a 0 = pd (fun y => pd (fun w => g w b i) j y) a 0 := by
    rw [show (fun w => g w i b) = (fun w => g w b i) from funext (fun w => hsymm w i b)]
  have hCB : pd (fun y => pd (fun w => g w b j) i y) a 0 = pd (fun y => pd (fun w => g w j b) i y) a 0 := by
    rw [show (fun w => g w b j) = (fun w => g w j b) from funext (fun w => hsymm w b j)]
  linarith [hAA, hBC, hCB]

/-- **RNC metric tensor 2-jet (gauge-derived).**  Feeding the gauge-derived `pd_christoffel_solve`
    into `pd_pd_metric_eq_sum_pd_christoffel`, the metric Hessian at an RNC centre is the closed
    curvature combination
      `∂_a∂_b g_{ij}(0) = ⅓ (R^i_{baj} + R^i_{jab} + R^j_{bai} + R^j_{iab})(0)`,   `R = riemann g gi`.
    This is the metric TENSOR 2-jet (the closed leading curvature coefficient of `g_{ij}−δ_{ij}`),
    Mathlib-absent and not previously in the repo, now reachable from the Christoffel machinery.
    Its trace over `i=j` reproduces `−⅔ Ric` (cross-check against `rnc_htr_of_gauge`).

    LOAD-BEARING: `hgauge` (the normal-coordinate gauge) is genuine; without it the closed `R`-value
    is false (the symmetric part of `∂∂g` is unconstrained). -/
theorem rnc_metric_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => g w i j) b y) a 0
      = (1 / 3) * (riemann g gi i b a j 0 + riemann g gi i j a b 0
                 + riemann g gi j b a i 0 + riemann g gi j i a b 0) := by
  rw [pd_pd_metric_eq_sum_pd_christoffel g gi hg hgi hgi0 hdg0 hsymm a b i j,
      pd_christoffel_solve g gi hdg0 hsymm hgauge i a b j,
      pd_christoffel_solve g gi hdg0 hsymm hgauge j a b i]
  ring

/-! ### The RNC inverse-metric 2-jet -/

/-- ★ **RNC inverse-metric 2-jet (F1, gauge-conditional).**  The inverse-metric Hessian at an RNC
    centre is the closed curvature leading coefficient
      `∂_a∂_b gⁱʲ(0) = −⅓ (R^i_{baj} + R^i_{jab} + R^j_{bai} + R^j_{iab})(0)`,   `R = riemann g gi`,
    i.e. (at `g(0)=δ`, where `R^i_{...} = R_{i...}`) exactly the jet
      `gⁱʲ(v) − δⁱʲ = ⅓ R_{iαjβ}vᵃvᵝ + o(r²)`   in Hessian form,
    the CLOSED curvature coefficient upgrading the M5 piece-(IV) isolation
    `Σᵢⱼ (gⁱʲ − δⁱʲ)(∂ᵢG)(∂ⱼP)`.

    Route: the UNCONDITIONAL sign flip `pd_pd_gInv_eq_neg_metric` (`∂∂gⁱʲ = −∂∂g`, from the genuine
    inverse relation) composed with the gauge-derived metric tensor 2-jet `rnc_metric_hessian`.  The
    `+⅓` (vs the metric's `−⅓`) is the sign flip.  The gauge `hgauge` is the SAME load-bearing
    normal-coordinate gauge the repo's √det chain carries — not a new axiom; removing it makes the
    closed `R`-value false. -/
theorem rnc_gInv_hessian (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => gi w i j) b y) a 0
      = -(1 / 3) * (riemann g gi i b a j 0 + riemann g gi i j a b 0
                  + riemann g gi j b a i 0 + riemann g gi j i a b 0) := by
  -- derived `gi(0)=δ` from the inverse relation at `0`.
  have hgi0 : ∀ p q, gi 0 p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q := by
    intro p q
    have h := hinv 0 p q
    rw [show (∑ σ, gi 0 p σ * g 0 σ q) = gi 0 p q from by
          rw [Finset.sum_eq_single q (fun σ _ hσ => by
                rw [hg0 σ q, Matrix.one_apply_ne hσ, mul_zero])
              (fun hq => absurd (Finset.mem_univ q) hq)]
          rw [hg0 q q, Matrix.one_apply_eq, mul_one]] at h
    rw [Matrix.one_apply]; exact h
  rw [pd_pd_gInv_eq_neg_metric g gi hg hgi hg0 hdg0 hinv a b i j,
      rnc_metric_hessian g gi hg hgi hgi0 hdg0 hsymm hgauge a b i j]
  ring

/-- **RNC inverse-metric 2-jet (F2, abstract algebraic reduction).**  Isolates the
    inverse-from-metric-jet algebra from whatever supplies the metric jet: for ANY carried
    metric-Hessian tensor `C` with `∂_a∂_b g_{ij}(0) = C a b i j` at the RNC centre, the inverse jet
    is the sign flip `∂_a∂_b gⁱʲ(0) = − C a b i j`.  The carried `hgjet` is the genuine metric tensor
    2-jet (the Mathlib-absent RNC foundational datum, or — via `rnc_metric_hessian` — the gauge-derived
    closed curvature form).  Unconditional in `C`. -/
theorem rnc_gInv_twojet_of_metricJet (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (C : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hgjet : ∀ a b i j, pd (fun y => pd (fun w => g w i j) b y) a 0 = C a b i j)
    (a b i j : Fin n) :
    pd (fun y => pd (fun w => gi w i j) b y) a 0 = - C a b i j := by
  rw [pd_pd_gInv_eq_neg_metric g gi hg hgi hg0 hdg0 hinv a b i j, hgjet a b i j]

end QIQTH.RNCExpansion

