/-
  PullbackMetric — the pullback of the ambient metric through the geodesic exponential map,
  and its regularity ledger toward the `κ = 1/6` endgame (THE_PARAMETRIX_CRITICAL_PATH R3→κ).

  Setting.  `Point n = Fin n → ℝ`.  The ambient metric `g : Point n → Fin n → Fin n → ℝ` (component
  form: `g y a b` is the `(a,b)`-component of the metric at `y`).  The geodesic exponential map at `p`,
  `exp_p := expMap g gi hC p : Point n → Point n`, is `ContDiff³` on `ball 0 (expRho …)` (Rung 3,
  `expMap_contDiffOn_three`, unconditional).

  The pullback metric is `g̃(x)_{ij} = ∑_{a,b} g(exp_p x)_{ab} · (D exp_p x · e_i)_a · (D exp_p x · e_j)_b`,
  with `D exp_p x = fderiv ℝ exp_p x` and `e_i = Pi.single i 1`.  It is the metric that Riemann normal
  coordinates centred at `p` are built to satisfy the RNC gauge for.

  MAIN RESULT (this file).  From `exp_p ∈ C³` (Rung 3) and `g ∈ C^∞` (ambient smoothness), the pullback
  metric is `ContDiffOn ℝ 2` on the exp-ball.  This is SHARP for the composition budget:
  `g̃` involves `fderiv exp_p`, which drops one order from `exp_p`, so `C³ exp_p ⟹ C² (fderiv exp_p)`
  and hence `C² g̃`.  The regularity ledger for the `κ = 1/6` step is recorded at the end of the file.
-/
import Mathlib
import QIQTH.ExpMapContDiff3

namespace QIQTH.PullbackMetric

open QIQTH.Curvature QIQTH.ExpMap
open Finset

variable {n : ℕ}

/-- **The pullback metric** `g̃ = exp_p^* g`, in component form.

    `expPullbackMetric g gi hC p x i j = ∑_{a,b} g(exp_p x)_{ab} · (D exp_p x · e_i)_a · (D exp_p x · e_j)_b`

    where `exp_p := expMap g gi hC p`, `D exp_p x = fderiv ℝ exp_p x` is the Fréchet derivative
    (Jacobian) of the exponential map at `x`, and `e_i = Pi.single i 1` is the `i`-th coordinate basis
    vector.  This is the ordinary tensorial pullback of the ambient metric `g` by `exp_p`.

    Well-behaved only where `exp_p` is a differentiable diffeomorphism onto its image, i.e. on
    `ball 0 (expRho g gi hC p)` (where Rung 1–3 supply the regularity used below). -/
noncomputable def expPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, g (expMap g gi hC p x) a b
    * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
    * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b

/-- **The Jacobian of `exp_p` is `ContDiffOn ℝ 2` on the exp-ball.**  `fderiv` drops one differentiability
    order from the `ContDiff³` `exp_p` (Rung 3, `expMap_contDiffOn_three`), on the open ball. -/
theorem contDiffOn_fderiv_expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 2 (fun x => fderiv ℝ (expMap g gi hC p) x)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
  (expMap_contDiffOn_three g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)

/-- Each scalar component of the Jacobian, `x ↦ (D exp_p x · e_i)_a`, is `ContDiffOn ℝ 2` on the
    exp-ball: apply the `ContDiffOn ℝ 2` CLM-field `x ↦ D exp_p x` to the constant vector `e_i`
    (`ContDiffOn.clm_apply`) and read off the `a`-th coordinate (compose with the projection CLM). -/
theorem contDiffOn_fderiv_expMap_component (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a : Fin n) :
    ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  have hJv : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1))
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    (contDiffOn_fderiv_expMap g gi hC p).clm_apply contDiffOn_const
  exact hJv.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a)

/-- **REGULARITY OF THE PULLBACK METRIC (the deliverable):** each component `x ↦ g̃(x)_{ij}` of the
    pullback metric is `ContDiffOn ℝ 2` on the exp-ball, given `exp_p ∈ C³` (Rung 3) and the ambient
    metric `g ∈ C^∞`.

    Composition budget (why `m = 2` is the best provable, and is sharp for this construction):
    * `x ↦ g(exp_p x)_{ab}` is `ContDiffOn ℝ 3` (`C^∞` `g` composed with `C³` `exp_p`);
    * `x ↦ (D exp_p x · e_i)_a` is `ContDiffOn ℝ 2` (`fderiv exp_p` is one order below `exp_p`);
    * the triple product and the finite `∑_{a,b}` preserve the minimum order `2`. -/
theorem contDiffOn_expPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j : Fin n) :
    ContDiffOn ℝ 2 (fun x => expPullbackMetric g gi hC p x i j)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hs
  -- `exp_p ∈ C³` on `s`; downgrade to `C²` where needed.
  have hE : ContDiffOn ℝ 2 (expMap g gi hC p) s :=
    (expMap_contDiffOn_three g gi hC p).of_le (by norm_num)
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  -- `x ↦ g(exp_p x)_{ab}` : `C^∞` `g`-component composed with `C²` `exp_p`.
  have hgcomp : ContDiffOn ℝ 2 (fun x => g (expMap g gi hC p x) a b) s :=
    ((hg a b).of_le (le_top)).comp_contDiffOn hE
  -- the two Jacobian components.
  have hJa : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) s :=
    contDiffOn_fderiv_expMap_component g gi hC p i a
  have hJb : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) s :=
    contDiffOn_fderiv_expMap_component g gi hC p j b
  exact (hgcomp.mul hJa).mul hJb

/-!
### REGULARITY LEDGER (R3→κ) — recorded, not `sorry`

* **Proved here:** `g̃ ∈ ContDiffOn ℝ 2` on the exp-ball (`contDiffOn_expPullbackMetric`), from
  `exp_p ∈ C³` (Rung 3) `+` `g ∈ C^∞`.  This is sharp for the pullback construction: `fderiv exp_p`
  costs one order, so `C³ exp_p ⟹ C² g̃`; recovering `C³ g̃` would require `exp_p ∈ C⁴` (Rung 4).

* **What `heat_a1_of_gauge` (RNCExpansion) demands of its metric argument:** `hg`/`hgi` are stated as
  `ContDiff ℝ ⊤` — i.e. `C^∞`, GLOBALLY (`ContDiff`, not `ContDiffOn` on the ball).  Feeding `g̃` in
  therefore fails on TWO counts as stated: (a) order — `g̃` is `C²` not `C^∞`; (b) domain — `g̃`'s
  regularity is only `ContDiffOn` on `ball 0 (expRho)`, not global `ContDiff`.

* **What the ANALYTIC CONTENT of the `κ = 1/6` step actually needs (finite):**
  - `hgauge` (the symmetrized cyclic `∂Γ(0)` sum): `christoffel g̃` needs `pd g̃` (1st derivatives);
    `pd (christoffel g̃)` needs `pd² g̃` (2nd derivatives).  ⟹ needs `g̃ ∈ C²` at `0`.
  - `hκgeo` (the `√det g̃` 2-jet, `½ ∂_c∂_d √det g̃(0)`): needs `pd² g̃` (2nd derivatives).  ⟹ `C²`.
  So the genuine analytic demand is `g̃ ∈ C²` (second partials existing/continuous at `0`), which the
  proved regularity `contDiffOn_expPullbackMetric` MEETS.

* **VERDICT.**  `κ = 1/6` for `g̃` is reachable from **Rung 3** at the level of analytic content
  (C² suffices for the gauge and the `√det` 2-jet).  It is NOT reachable through
  `heat_a1_of_gauge` AS CURRENTLY STATED, because that theorem's `hg`/`hgi : ContDiff ℝ ⊤`
  over-demand `C^∞` and globality.  Two admissible closes, neither needing a higher exp-map rung:
    1. **Weaken `heat_a1_of_gauge`'s metric hypotheses** to finite `ContDiffOn ℝ 2` on a neighbourhood
       of `0` (its proof only touches `christoffel`, `pd christoffel` and the `√det` 2-jet at `0`,
       i.e. ≤ 2 derivatives — it does not consume `⊤`).  This is the load-bearing follow-up.
    2. Alternatively supply the gauge/`√det`-jet facts for `g̃` directly (bypassing the `ContDiff ⊤`
       interface), which again only needs `g̃ ∈ C²`.
  A higher rung (`exp_p ∈ C⁴`, Rung 4) is **NOT** required for `κ = 1/6`; it would only be needed if
  one insisted on routing `g̃` through the current `ContDiff ⊤` signature by literally producing a
  `C^∞` (or `C³`) pullback — an over-strong path.  The true blocker is the `⊤` in
  `heat_a1_of_gauge`, weakenable to finite `C²`.
-/

end QIQTH.PullbackMetric
