/-
  InverseChartSecondJetODEBridge — the BASE-PARAMETER ODE shape of the van-Vleck inverse chart's
  SECOND field-jet, DERIVED by differentiating the IFT algebraic closed form along the base parameter.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is one
  ODE-shape brick of the a₁=R/6 mixed-sliver campaign's chart-surface residue (plan v2, Task B,
  `tranquil-stargazing-fox.md`).  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses,
  no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM.  `InverseChartSecondJet.chartW0_secondJet_bound` supplies the inverse chart's second
  field-jet only as an IFT **algebraic closed form** (a bound on a composed CLM), NOT as an ODE:

      `Q z = (−mulLeftRight ℝ (E→L E) I I) ∘L (D²φ_z(W_z 0) ∘L I)`,   `I = Ring.inverse (Dφ_z(W_z 0))`.

  The consumer `ChartMixedThirdJetBasepoint.secondFieldJet_basepoint_hasDerivAt` wants the base-point
  derivative of this second jet in the LINEAR-ODE shape `X'(s) = DF(Y s)·X(s) + b(s)`.  J4-833 confirmed
  the τ-fiber Jacobi-ODE route to that shape is blocked at the `.choose`-opacity of `uniformInverseChart`
  (no constructive Newton/Banach iteration ⟹ no concrete τ-ODE supplier for `∂²_p V`).

  ## THE ROUTE THIS FILE BUILDS.  Differentiate the IFT closed form itself along the base parameter `s`
  (the chart / forward map depends on `s` through the base point).  Writing the applied second jet as
      `q s := −(I s) (H s (I s a) (I s b))`,   `I s = Ring.inverse (A s)`,  `A s = Dφ`,  `H s = D²φ`,
  the product rule gives a genuine linear ODE in `s`:
      `q'(s) = M(s)·(q s) + b(s)`,   `M(s) = −(I s)·A'(s)`,   `I' = −I·A'·I`,
      `b(s)[a,b] = −I·H'(Ia,Ib) − I·H(I'a,Ib) − I·H(Ia,I'b)`,
  where the OUTER-`I` differentiation term is EXACTLY `M·q` and the `H'`/inner-jet terms are the source.
  This was verified symbolically FIRST (`docs/qg_roadmap/j4_834_ift_second_jet_base_ode.py`, exact
  residual 0).

  ★ KEY STRUCTURAL POINT (why this side-steps J4-833's wall).  Every object on the right-hand side
  (`I, H, A', H'`) is a FORWARD jet — the forward map `φ = uniformFlowExp` is the smooth, `.choose`-FREE
  object.  So the base derivative of the OPAQUE inverse chart's second jet is expressed PURELY via
  forward jets, without ever needing a τ-ODE for `∂²_p V`.  The base-ODE coefficient produced here is
  `M = −I·A'` (the forward-Jacobian `s`-jet contracted with the inverse jet), which differs from the
  geodesic-field Jacobian `DF(Y s)` the consumer literally names — matching that exact coefficient would
  push `(M − DF)·q` into the source (documented, not attempted here).

  ## WHAT LANDS (all DERIVED; NO `sorry`, no new axioms, NOT `a₁ = R/6`).

    * `ift_secondJet_comp_apply` — the applied form of the exact `chartW0_secondJet_bound` composed CLM:
        `((−mulLeftRight ℝ (E→L E) I I) ∘L (D2 ∘L I)) a b = −(I (D2 (I a) (I b)))`.
      Ties the composed-CLM object literally used in the concrete file to the applied vector form.

    * `ift_secondJet_applied_hasDerivAt` — the base-parameter derivative of the applied second jet, in
      RAW product-rule form: given differentiable forward families `A` (invertible at `s₀`) and `H`,
        `HasDerivAt (fun s => −(Ring.inverse (A s)) (H s (Ring.inverse (A s) a) (Ring.inverse (A s) b)))
                    (rawDeriv) s₀`.

    * ★ `ift_secondJet_base_ode_hasDerivAt` — the SAME derivative REPACKAGED into the linear-ODE shape:
        `HasDerivAt (fun s => q s) ((−(I₀ * A')) (q s₀) + bsrc) s₀`,
      with `I₀ = Ring.inverse (A s₀)`, `q s₀` the second-jet vector, and `bsrc` the explicit source.
      This is the base-parameter ODE the consumer's shape wants, DERIVED from the `.choose`-free IFT form.

  ## HONEST SCOPE (what is NOT closed).  This is the ABSTRACT operator-calculus bridge — it takes the
  forward jets `A, H` and their `s`-derivatives `A', H'` as differentiable families (SATISFIABLE: any
  smooth invertible `A` and any `H` work; e.g. the forward flow `uniformFlowExp`, which IS base-smooth).
  It does NOT wire `A s = Dφ_{Y s}`, `H s = D²φ_{Y s}` to the concrete `uniformFlowExp` (that needs the
  forward flow's base-slot differentiability of `fderiv`/`fderiv²`, the `BaseFlowHderFamily` tower), and
  it does NOT reconcile the produced coefficient `M = −I·A'` with the consumer's `DF(Y s)` (that is a
  separate source-shift). It is one order of the base-parameter chain rule, `.choose`-free, fully proved.

  No `sorry`, no new axioms, no `:= True`; every hypothesis satisfiable and non-vacuous; none equals the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib

open ContinuousLinearMap
open scoped Topology

namespace QIQTH.InverseChartSecondJetODEBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The applied form of the exact composed-CLM second jet. -/

/-- **`ift_secondJet_comp_apply` — the exact `chartW0_secondJet_bound` composed CLM, applied.**
    The composed continuous-linear-map second jet used verbatim in `InverseChartSecondJet` unfolds, on
    two vectors, to the IFT applied form `−(I (D2 (I a) (I b)))`.  Pure CLM algebra.  NOT `a₁ = R/6`. -/
theorem ift_secondJet_comp_apply (I : E →L[ℝ] E) (D2 : E →L[ℝ] (E →L[ℝ] E)) (a b : E) :
    ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) I I).comp (D2.comp I)) a b
      = -(I (D2 (I a) (I b))) := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply]

/-! ### The base-parameter derivative of the applied second jet. -/

/-- **`ift_secondJet_applied_hasDerivAt` — RAW product-rule derivative.**  For differentiable forward
    families `A : ℝ → (E →L[ℝ] E)` (a unit at `s₀`) and `H : ℝ → (E →L[ℝ] E →L[ℝ] E)`, the applied
    inverse second jet `q s = −(Iₛ (Hₛ (Iₛ a) (Iₛ b)))`, `Iₛ = Ring.inverse (A s)`, has base-parameter
    derivative equal to the raw product-rule sum.  Chain of `HasDerivAt.clm_apply`.  NOT `a₁ = R/6`. -/
theorem ift_secondJet_applied_hasDerivAt
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {H : ℝ → (E →L[ℝ] E →L[ℝ] E)}
    {H' : E →L[ℝ] E →L[ℝ] E} {s₀ : ℝ}
    (hA : HasDerivAt A A' s₀) (hH : HasDerivAt H H' s₀) (hunit : IsUnit (A s₀)) (a b : E) :
    let I₀ : E →L[ℝ] E := Ring.inverse (A s₀)
    let Ip : E →L[ℝ] E := -(I₀ * A' * I₀)
    HasDerivAt (fun s => -(Ring.inverse (A s)) (H s (Ring.inverse (A s) a) (Ring.inverse (A s) b)))
      (-(Ip (H s₀ (I₀ a) (I₀ b))
          + I₀ (H' (I₀ a) (I₀ b) + (H s₀ (Ip a)) (I₀ b) + (H s₀ (I₀ a)) (Ip b)))) s₀ := by
  intro I₀ Ip
  -- unit witness and identification `Ring.inverse (A s₀) = I₀`
  set xu := hunit.unit with hxudef
  have hxu : (↑xu : E →L[ℝ] E) = A s₀ := hunit.unit_spec
  -- derivative of `s ↦ Ring.inverse (A s)`.
  have hgf : HasFDerivAt Ring.inverse (-mulLeftRight ℝ (E →L[ℝ] E) I₀ I₀) (A s₀) := by
    have h0 : (↑xu⁻¹ : E →L[ℝ] E) = I₀ := by
      simp only [I₀, ← hxu, Ring.inverse_unit]
    rw [← h0, ← hxu]; exact hasFDerivAt_ringInverse xu
  have hIc : HasDerivAt (fun s => Ring.inverse (A s))
      ((-mulLeftRight ℝ (E →L[ℝ] E) I₀ I₀) A') s₀ := hgf.comp_hasDerivAt s₀ hA
  -- rewrite the inverse-jet derivative into `Ip`.
  have hIcp : HasDerivAt (fun s => Ring.inverse (A s)) Ip s₀ := by
    convert hIc using 1
  have hI0 : Ring.inverse (A s₀) = I₀ := rfl
  -- `ua s = Iₛ a`, `ub s = Iₛ b`
  have hua : HasDerivAt (fun s => (Ring.inverse (A s)) a) (Ip a) s₀ := by
    have := hIcp.clm_apply (hasDerivAt_const s₀ a)
    simpa using this
  have hub : HasDerivAt (fun s => (Ring.inverse (A s)) b) (Ip b) s₀ := by
    have := hIcp.clm_apply (hasDerivAt_const s₀ b)
    simpa using this
  -- `Hu s = Hₛ (ua s)`
  have hHu : HasDerivAt (fun s => (H s) ((Ring.inverse (A s)) a))
      (H' (I₀ a) + (H s₀) (Ip a)) s₀ := by
    have := hH.clm_apply hua
    simpa [hI0] using this
  -- `w s = (Hu s) (ub s)`
  have hw : HasDerivAt (fun s => (H s) ((Ring.inverse (A s)) a) ((Ring.inverse (A s)) b))
      ((H' (I₀ a) + (H s₀) (Ip a)) (I₀ b) + (H s₀ (I₀ a)) (Ip b)) s₀ := by
    have := hHu.clm_apply hub
    simpa [hI0] using this
  -- `p s = Iₛ (w s)`, then negate.
  have hp : HasDerivAt
      (fun s => (Ring.inverse (A s)) ((H s) ((Ring.inverse (A s)) a) ((Ring.inverse (A s)) b)))
      (Ip (H s₀ (I₀ a) (I₀ b))
        + I₀ ((H' (I₀ a) + (H s₀) (Ip a)) (I₀ b) + (H s₀ (I₀ a)) (Ip b))) s₀ := by
    have := hIcp.clm_apply hw
    simpa [hI0] using this
  have hq := hp.neg
  -- the stated raw derivative matches the product-rule chain up to `add_apply`.
  convert hq using 1

/-! ### The linear-ODE shape. -/

/-- **★ `ift_secondJet_base_ode_hasDerivAt` — the base-parameter LINEAR ODE.**  The same derivative,
    repackaged: the applied inverse second jet `q s = −(Iₛ (Hₛ (Iₛ a) (Iₛ b)))` satisfies the linear ODE
    in the base parameter `s`
        `HasDerivAt q ((−(I₀ * A')) (q s₀) + bsrc) s₀`,
    with coefficient `M = −(I₀ * A')` (left-multiplication), value `q s₀` the second-jet vector, and the
    explicit source
        `bsrc = −(I₀ (H' (I₀ a) (I₀ b))) − (I₀ ((H s₀ (Ip a)) (I₀ b))) − (I₀ ((H s₀ (I₀ a)) (Ip b)))`,
        `Ip = −(I₀ * A' * I₀)`.
    Sympy-verified (`docs/qg_roadmap/j4_834_ift_second_jet_base_ode.py`, residual 0).  This is the
    base-point ODE shape the consumer wants, DERIVED `.choose`-free from the IFT closed form.  The outer-`I`
    differentiation term is EXACTLY `M·(q s₀)`; the `H'`/inner-jet terms are the source.  NOT `a₁ = R/6`. -/
theorem ift_secondJet_base_ode_hasDerivAt
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {H : ℝ → (E →L[ℝ] E →L[ℝ] E)}
    {H' : E →L[ℝ] E →L[ℝ] E} {s₀ : ℝ}
    (hA : HasDerivAt A A' s₀) (hH : HasDerivAt H H' s₀) (hunit : IsUnit (A s₀)) (a b : E) :
    let I₀ : E →L[ℝ] E := Ring.inverse (A s₀)
    let Ip : E →L[ℝ] E := -(I₀ * A' * I₀)
    HasDerivAt (fun s => -(Ring.inverse (A s)) (H s (Ring.inverse (A s) a) (Ring.inverse (A s) b)))
      ((-(I₀ * A')) (-(I₀ (H s₀ (I₀ a) (I₀ b))))
        + (-(I₀ (H' (I₀ a) (I₀ b))) - (I₀ ((H s₀ (Ip a)) (I₀ b))) - (I₀ ((H s₀ (I₀ a)) (Ip b))))) s₀ := by
  intro I₀ Ip
  have hraw := ift_secondJet_applied_hasDerivAt hA hH hunit a b
  convert hraw using 1
  -- algebraic identity: `M·(q s₀) = -(Ip · (H s₀ (I₀ a)(I₀ b)))`, plus source rearrangement.
  -- key: `(-(I₀*A'))(-(I₀ w)) = -( (-(I₀*A'*I₀)) w )` for `w = H s₀ (I₀ a)(I₀ b)`.
  have hcoef : (-(I₀ * A')) (-(I₀ (H s₀ (I₀ a) (I₀ b))))
      = -(Ip (H s₀ (I₀ a) (I₀ b))) := by
    simp only [Ip, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
      map_neg, neg_neg]
  rw [hcoef, map_add, map_add]
  abel

end QIQTH.InverseChartSecondJetODEBridge
