/-
  RNCExpansionFiniteReg — general-base-point finite-regularity (`ContDiffAt ℝ 2`) RNC primitives.

  Brick R3a of the RECENTER campaign (docs/qg_roadmap/RECENTER_CAMPAIGN_PLAN.md) toward the
  unconditional `a₁ = R/6` heat-kernel coefficient.

  STATE OF THE ART (do NOT under-credit): the `ContDiffAt ℝ 2` analogues of the RNC-expansion
  primitives are ALREADY LANDED, at base point `0`, inside `QIQTH.RNCExpansion` (committed ed2362c2):
    • `contDiffAt_prod`   — product of `C²`-at-`x` fields is `C²`;
    • `det_contDiffAt2`   — `det ∘ g` is `C²` at `0`;
    • `sqrtdet_pd_pd_c2`   — the RNC `√det g` second-partial 2-jet = `−⅓ Ric` at `0`;
    up through `heat_a1_of_gauge_c2`.

  What this file ADDS is the piece the origin-pinned versions do NOT cover and that the near-diagonal
  residual slice (R3b/R3c) needs: the SAME primitives at an ARBITRARY base point `x`, since the
  q-centered `expPullbackMetric` is evaluated near — not only at — the diagonal.  Concretely:
    • `det_contDiffAt_two`     — `det ∘ g` is `C²` at any `x` (general-`x` analogue of `det_contDiffAt2`);
    • `sqrtdet_contDiffAt_two` — `√det g` is `C²` at any `x` where `det (g x) ≠ 0`
        (via `det_contDiffAt_two` + Mathlib `ContDiffAt.sqrt`);
  together with the task's stable-named re-exports `prod_contDiffAt_two` (= `contDiffAt_prod`) and
  `sqrtdet_pd_pd_C2` (= `sqrtdet_pd_pd_c2`, the origin RNC 2-jet), so downstream R3b/R3c can import a
  single stable surface.

  No axioms, no `sorry`, no vacuous hypotheses.  Every hypothesis (the per-entry `C²` regularity and,
  for `√det`, the nonvanishing of `det (g x)`) is genuinely used.
-/
import Mathlib
import QIQTH.RNCExpansion
import QIQTH.LaplaceBeltramiFiniteReg

namespace QIQTH.RNCExpansion

open QIQTH.Curvature
open Finset Matrix

variable {n : ℕ}

/-- **Finite product of `C²`-at-`x` fields is `C²`** (general base point).  Task-named re-export of the
    landed `contDiffAt_prod`; provided as a stable name for the R3b/R3c import surface. -/
theorem prod_contDiffAt_two {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (x : Point n)
    (hF : ∀ i ∈ s, ContDiffAt ℝ 2 (fun y => F i y) x) :
    ContDiffAt ℝ 2 (fun y => ∏ i ∈ s, F i y) x :=
  contDiffAt_prod s F x hF

/-- **`det ∘ g` is `C²` at an ARBITRARY base point `x`** — the general-`x` analogue of the landed
    (origin-pinned) `det_contDiffAt2`.  `Matrix.det` is a polynomial in the entries
    (`Matrix.det_apply'` = a signed `Finset.sum` of `Finset.prod`s of entries), so `C²` of the entries
    at `x` propagates through `ContDiffAt.sum`, `contDiffAt_const.mul`, and `prod_contDiffAt_two`. -/
theorem det_contDiffAt_two (g : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) x) :
    ContDiffAt ℝ 2 (fun y => Matrix.det (g y)) x := by
  rw [show (fun y => Matrix.det (g y))
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g y (σ i) i)
      from funext (fun y => Matrix.det_apply' _)]
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul
    (prod_contDiffAt_two univ (fun i y => g y (σ i) i) x (fun i _ => hg2 (σ i) i))

/-- **`√det g` is `C²` at an arbitrary base point `x` where `det (g x) ≠ 0`.**  `det ∘ g` is `C²` at
    `x` (`det_contDiffAt_two`) and `Real.sqrt` is `C^∞` away from `0` (`ContDiffAt.sqrt`), so the
    composite is `C²`.  This is the general-`x` `√det` smoothness the near-diagonal residual slice
    (R3b/R3c) needs — the origin RNC 2-jet `sqrtdet_pd_pd_c2` only sees the germ at `0`. -/
theorem sqrtdet_contDiffAt_two (g : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) x)
    (hdet : Matrix.det (g x) ≠ 0) :
    ContDiffAt ℝ 2 (fun y => Real.sqrt (Matrix.det (g y))) x :=
  (det_contDiffAt_two g x hg2).sqrt hdet

/-- **The RNC `√det g` second-partial 2-jet at `C²`** (the R3b deliverable) — task-named re-export of
    the landed origin `sqrtdet_pd_pd_c2`: with entries `C²` at `0`, `g(0)=δ` (`hg0`), `∂g(0)=0`
    (`hdg0`), and the carried metric-Hessian trace `tr ∂∂g(0) = −⅔ Ric` (`htr`), the second partial of
    `√det g` at the origin is `−⅓ Ric_{cd}`.  Provided as a stable name for R3b/R3c. -/
theorem sqrtdet_pd_pd_C2 (g : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (c d : Fin n) :
    pd (fun y => pd (fun w => Real.sqrt (Matrix.det (g w))) d y) c 0 = -(1 / 3) * Ric c d :=
  sqrtdet_pd_pd_c2 g Ric hg2 hg0 hdg0 htr c d

end QIQTH.RNCExpansion
