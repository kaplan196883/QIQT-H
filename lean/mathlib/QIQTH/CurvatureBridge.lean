/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.CoordinateCurvature
import QIQTH.Curvature

/-!
# The curvature bridge — the two scalar-curvature formalizations are ONE base

Proves the repo's two scalar-curvature formalizations are ONE: the evaluable jet-based
`CoordinateCurvature.scalarCurvature`, fed a metric field's actual jets `(gi x, ∂g, ∂∂g)` and the
carried inverse-derivative identity `∂ₐg^{kl}=−g^{kp}(∂ₐg_{pq})g^{ql}`, equals the field-based
`Curvature.scalarCurv`.

So `Curvature.lean` is the canonical curvature base and `CoordinateCurvature` its proven evaluable
specialization — no duplicate concept.

⚠ HONEST: the inverse-derivative identity `hgiD` and metric-symmetry `hgs` are CARRIED hypotheses
(this matches `CoordinateCurvature`'s `dInvMetric` design; proving `hgiD` from `gi = g⁻¹` needs
matrix-inverse differentiation, not done here). Smoothness of the metric components (`hgC`) is the
honest analytic input for the second-derivative (Schwarz) commuting used in the `dChristoffel` step.

This is the coordinate/component scalar curvature; NOT the coordinate-free Riemann tensor of a
manifold (that is `QIQTH/ManifoldCurvature.lean`), NOT the general heat kernel. NOT the
conjecture/strong-principle/QG. No axioms, no `sorry`.
-/

open scoped BigOperators

namespace QIQTH.CurvatureBridge

variable {n : ℕ}

/-- Inverse-metric 0-jet fed to `CoordinateCurvature`: `g^{kl}` at `x`. -/
noncomputable def giM (gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n) :
    CoordinateCurvature.Mat (Fin n) :=
  Matrix.of (fun k l => gi x k l)

/-- Metric 1-jet fed to `CoordinateCurvature`: `dgM a i j = ∂ₐ g_{ij}` at `x`. -/
noncomputable def dgM (g : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n) :
    Fin n → CoordinateCurvature.Mat (Fin n) :=
  fun a => Matrix.of (fun i j => Curvature.pd (fun y => g y i j) a x)

/-- Metric 2-jet fed to `CoordinateCurvature`: `ddgM a b i j = ∂_b ∂ₐ g_{ij}` at `x`. -/
noncomputable def ddgM (g : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n) :
    Fin n → Fin n → CoordinateCurvature.Mat (Fin n) :=
  fun a b => Matrix.of (fun i j =>
    Curvature.pd (fun y => Curvature.pd (fun z => g z i j) a y) b x)

/-- **Christoffel bridge.** The jet-based `CoordinateCurvature.christoffel`, fed the metric field's
actual jets, equals the field-based `Curvature.christoffel`. Needs metric symmetry `hgs`. -/
theorem christoffel_bridge (g gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n)
    (hgs : ∀ y a b, g y a b = g y b a) (k i j : Fin n) :
    Curvature.christoffel g gi k i j x
      = CoordinateCurvature.christoffel (giM gi x) (dgM g x) k i j := by
  simp only [Curvature.christoffel, CoordinateCurvature.christoffel,
    CoordinateCurvature.lowerGamma, giM, dgM, Matrix.of_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  have e1 : (fun y => g y α j) = (fun y => g y j α) := funext fun y => hgs y α j
  have e2 : (fun y => g y α i) = (fun y => g y i α) := funext fun y => hgs y α i
  rw [e1, e2]

/-- ★★★ **The crux — derivative-of-Christoffel bridge.** The coordinate derivative of the field-based
`Curvature.christoffel` (via the product/sum/Leibniz `pd` calculus) equals the jet-based
`CoordinateCurvature.dChristoffel`, once fed the metric's actual jets, the carried inverse-derivative
identity `hgiD`, metric symmetry `hgs`, and smoothness `hgC` of the metric components (the honest
analytic input for the Schwarz mixed-partial commuting). -/
theorem dChristoffel_bridge (g gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n)
    (hgs : ∀ y a b, g y a b = g y b a)
    (hgi : ∀ k l a, Curvature.PdiffAt (fun y => gi y k l) a x)
    (hgiD : ∀ a k l, Curvature.pd (fun y => gi y k l) a x
            = CoordinateCurvature.dInvMetric (giM gi x) (dgM g x) a k l)
    (hgC : ∀ i j, ContDiff ℝ ⊤ (fun y => g y i j))
    (a k i j : Fin n) :
    Curvature.pd (fun y => Curvature.christoffel g gi k i j y) a x
      = CoordinateCurvature.dChristoffel (giM gi x) (dgM g x) (ddgM g x) a k i j := by
  -- differentiability of the per-index `lowerGamma` bracket field, and of the `gi · bracket` product.
  have hbrk : ∀ α : Fin n, Curvature.PdiffAt
      (fun y => Curvature.pd (fun z => g z α j) i y
        + Curvature.pd (fun z => g z α i) j y - Curvature.pd (fun z => g z i j) α y) a x := fun α =>
    ((Curvature.PdiffAt_pd (fun y => g y α j) (hgC α j) i a x).add
      (Curvature.PdiffAt_pd (fun y => g y α i) (hgC α i) j a x)).sub
      (Curvature.PdiffAt_pd (fun y => g y i j) (hgC i j) α a x)
  have hFα : ∀ α : Fin n, Curvature.PdiffAt
      (fun y => gi y k α * (Curvature.pd (fun z => g z α j) i y
        + Curvature.pd (fun z => g z α i) j y - Curvature.pd (fun z => g z i j) α y)) a x :=
    fun α => (hgi k α a).mul (hbrk α)
  -- push `pd` through the `½ · Σ` outer structure.
  simp only [Curvature.christoffel]
  rw [Curvature.pd_const_mul (1 / 2 : ℝ)
        (fun y => ∑ α : Fin n, gi y k α * (Curvature.pd (fun z => g z α j) i y
          + Curvature.pd (fun z => g z α i) j y - Curvature.pd (fun z => g z i j) α y))
        a x
        (Curvature.PdiffAt_sum Finset.univ
          (fun α y => gi y k α * (Curvature.pd (fun z => g z α j) i y
            + Curvature.pd (fun z => g z α i) j y - Curvature.pd (fun z => g z i j) α y))
          a x (fun α _ => hFα α)),
     Curvature.pd_sum Finset.univ
        (fun α y => gi y k α * (Curvature.pd (fun z => g z α j) i y
          + Curvature.pd (fun z => g z α i) j y - Curvature.pd (fun z => g z i j) α y))
        a x (fun α _ => hFα α)]
  -- unfold the RHS `dChristoffel` to a `½ · Σ` of the same shape, and match term-by-term.
  simp only [CoordinateCurvature.dChristoffel, CoordinateCurvature.dChristoffelOfDInv]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  -- Leibniz on `gi · bracket`, then the carried `∂g⁻¹` identity.
  rw [Curvature.pd_mul (fun y => gi y k l)
        (fun y => Curvature.pd (fun z => g z l j) i y
          + Curvature.pd (fun z => g z l i) j y - Curvature.pd (fun z => g z i j) l y)
        a x (hgi k l a) (hbrk l),
     hgiD a k l,
     Curvature.pd_sub _ _ a x
        ((Curvature.PdiffAt_pd (fun y => g y l j) (hgC l j) i a x).add
         (Curvature.PdiffAt_pd (fun y => g y l i) (hgC l i) j a x))
        (Curvature.PdiffAt_pd (fun y => g y i j) (hgC i j) l a x),
     Curvature.pd_add _ _ a x
        (Curvature.PdiffAt_pd (fun y => g y l j) (hgC l j) i a x)
        (Curvature.PdiffAt_pd (fun y => g y l i) (hgC l i) j a x),
     Curvature.pd_comm (fun z => g z l j) a i x (hgC l j),
     Curvature.pd_comm (fun z => g z l i) a j x (hgC l i),
     Curvature.pd_comm (fun z => g z i j) a l x (hgC i j)]
  -- metric symmetry to align `g_{l·}` with `g_{·l}`.
  have elj : (fun z => g z l j) = (fun z => g z j l) := funext fun z => hgs z l j
  have eli : (fun z => g z l i) = (fun z => g z i l) := funext fun z => hgs z l i
  rw [elj, eli]
  simp only [CoordinateCurvature.lowerGamma, CoordinateCurvature.dLowerGamma,
    giM, dgM, ddgM, Matrix.of_apply]

/-- **Riemann bridge** `R^k_{sij}`. The derivative pair matches by `dChristoffel_bridge`, the quadratic
`ΓΓ` pair by `christoffel_bridge`. -/
theorem riemann_bridge (g gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n)
    (hgs : ∀ y a b, g y a b = g y b a)
    (hgi : ∀ k l a, Curvature.PdiffAt (fun y => gi y k l) a x)
    (hgiD : ∀ a k l, Curvature.pd (fun y => gi y k l) a x
            = CoordinateCurvature.dInvMetric (giM gi x) (dgM g x) a k l)
    (hgC : ∀ i j, ContDiff ℝ ⊤ (fun y => g y i j))
    (k s i j : Fin n) :
    Curvature.riemann g gi k s i j x
      = CoordinateCurvature.riemann (giM gi x) (dgM g x) (ddgM g x) k s i j := by
  simp only [Curvature.riemann, CoordinateCurvature.riemann, CoordinateCurvature.riemannOf]
  rw [dChristoffel_bridge g gi x hgs hgi hgiD hgC i k j s,
      dChristoffel_bridge g gi x hgs hgi hgiD hgC j k i s]
  simp only [christoffel_bridge g gi x hgs, Finset.sum_sub_distrib]
  ring

/-- **Ricci bridge** `R_{sj} = Σ_k R^k_{skj}`. -/
theorem ricci_bridge (g gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n)
    (hgs : ∀ y a b, g y a b = g y b a)
    (hgi : ∀ k l a, Curvature.PdiffAt (fun y => gi y k l) a x)
    (hgiD : ∀ a k l, Curvature.pd (fun y => gi y k l) a x
            = CoordinateCurvature.dInvMetric (giM gi x) (dgM g x) a k l)
    (hgC : ∀ i j, ContDiff ℝ ⊤ (fun y => g y i j))
    (s j : Fin n) :
    Curvature.ricci g gi s j x
      = CoordinateCurvature.ricci (giM gi x) (dgM g x) (ddgM g x) s j := by
  simp only [Curvature.ricci, CoordinateCurvature.ricci]
  apply Finset.sum_congr rfl
  intro μ _
  exact riemann_bridge g gi x hgs hgi hgiD hgC μ s μ j

/-- ★ **Scalar-curvature bridge.** The evaluable jet-based `CoordinateCurvature.scalarCurvature`, fed
the metric field's actual jets and the carried inverse-derivative identity, equals the field-based
`Curvature.scalarCurv`. So the two scalar curvatures are ONE. -/
theorem scalarCurvature_bridge (g gi : Curvature.Point n → Fin n → Fin n → ℝ) (x : Curvature.Point n)
    (hgs : ∀ y a b, g y a b = g y b a)
    (hgi : ∀ k l a, Curvature.PdiffAt (fun y => gi y k l) a x)
    (hgiD : ∀ a k l, Curvature.pd (fun y => gi y k l) a x
            = CoordinateCurvature.dInvMetric (giM gi x) (dgM g x) a k l)
    (hgC : ∀ i j, ContDiff ℝ ⊤ (fun y => g y i j)) :
    CoordinateCurvature.scalarCurvature (giM gi x) (dgM g x) (ddgM g x)
      = Curvature.scalarCurv g gi x := by
  simp only [CoordinateCurvature.scalarCurvature, Curvature.scalarCurv]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro j _
  rw [← ricci_bridge g gi x hgs hgi hgiD hgC s j]
  simp only [giM, Matrix.of_apply]

end QIQTH.CurvatureBridge
