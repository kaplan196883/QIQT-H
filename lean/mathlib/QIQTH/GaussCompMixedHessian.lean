/-
  GaussCompMixedHessian — J4-1001: the MIXED-direction (i≠j, not just diagonal i=i) generalization of
  `ChartJetHessian.gaussComp_pd_pd`/`gaussComp_amp_pd_pd`, and its IDENTIFICATION with the abstract
  `heatHessMult` bilinear Gaussian-Hessian multiplier of J4-998 — the piece of item (b) ("the second-
  order chain rule for `kPrime`'s literal mixed coordinate partial") that Sol's GO/NO-GO consult (2026-08-
  22, gpt-5.6-sol high) identified as the one tractable, standalone sub-piece of the `hcomp` identification
  chain: "the general C² chain rule `∂ᵢ∂ⱼ[F(W x)] = F''[∂ᵢW,∂ⱼW] + F'·∂ᵢ∂ⱼW`, decoupled from
  `uniformInverseChart`/`kPrime`/`hcomp`."

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  chain-rule/Leibniz calculus brick, fully parametric in the composed map `V` and amplitude `A` (exactly
  as abstract as `ChartJetHessian.lean` already is) — it does NOT touch `uniformInverseChart`, `kPrime`,
  `witnessFieldDeriv`, or `hcomp`.  It does **NOT** discharge `hcomp`: the base-slot change of variables
  (item a), the truncation-tail control (item c), and the coordinate summation (item d) — plus actually
  INSTANTIATING `V := uniformInverseChart g gi hC hK z` and identifying `kPrime`'s literal mixed `fderiv`
  with the `pd`-form here (via `Curvature.pd_eq_fderiv`) — all remain open.  No `sorry`, no new axioms, no
  `:= True`, no vacuous hypothesis (non-vacuity witness `V := id`, `A := 1` supplied), none equal to the
  conclusion, NO existing file edited.  `a₁ = R/6` stays STRICTLY CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE.  `ChartJetHessian.gaussComp_pd_pd`/`gaussComp_amp_pd_pd` prove the on-DIAGONAL second
  coordinate partial `∂ᵢ∂ᵢ[G_τ∘V]` (and the amplitude-weighted version), matching `witnessFieldDeriv2 =
  pd(pd f i) i` — a genuinely different (and structurally simpler) object than the LITERAL `kPrime`, whose
  `j`-component `kPrime … i t s x z (Pi.single j 1) = leviSeries(s,z,0) · ∂ⱼ∂ᵢ[H_G(t−s,·,z)](x)` is a
  MIXED second coordinate partial (inner direction `i`, outer direction `j`, generally `i ≠ j`).  No
  banked brick proved the mixed case.  This file supplies it, by the SAME `pd`-on-lines technique
  (`Function.update`) `ChartJetHessian` uses, just with the outer differentiation taken along a possibly
  different coordinate `j`.

  ## WHAT LANDS (ns `QIQTH.GaussCompMixedHessian`).
    • `gaussComp_pd_pd_mixed` — ★★ the pure-Gaussian mixed second coordinate partial: for a composed map
      `V : Point n → Point n` with inner `i`-line jet field `P` (`hV1 : ∀ x k, HasDerivAt (V∘update·i)
      (P x k) (x i)`), outer `j`-line jet of `V` itself at `x₀` (`hVj1`, value `Pj0`), and outer `j`-line
      jet of the FIELD `P` at `x₀` (`hPj1`, value `Qj` — the genuine mixed second jet `∂ⱼ(∂ᵢV)`),
        `∂ⱼ∂ᵢ[G_τ∘V](x₀) = G_τ(V x₀) · [ ⟨V x₀,Pj0⟩⟨V x₀,P x₀⟩/(4τ²) − (⟨Pj0,P x₀⟩+⟨V x₀,Qj⟩)/(2τ) ]`.
      Specializes to `ChartJetHessian.gaussComp_pd_pd` at `j = i`, `Pj0 = P x₀`, `Qj = Q`.
    • `gaussComp_pd_pd_mixed_eq_heatHessMult_sub` — ★★★ THE IDENTIFICATION: the mixed second coordinate
      partial equals the J4-998 abstract `heatHessMult` bilinear multiplier MINUS the `Q`-jet correction:
        `∂ⱼ∂ᵢ[G_τ∘V](x₀) = heatHessMult τ Pj0 (P x₀) (V x₀) − G_τ(V x₀)·⟨V x₀,Qj⟩/(2τ)`.
      This directly bridges kPrime's LITERAL mixed chain-rule Hessian to the abstract moment-cancellation
      object J4-998/999/1000 already control the rate of — the missing link named (but not built) in the
      J4-1000 commit message's residue (iii).
    • `gaussComp_amp_pd_pd_mixed` — the amplitude-weighted Leibniz generalization (mirrors
      `ChartJetHessian.gaussComp_amp_pd_pd`, matching kPrime's actual amplitude-times-Gaussian shape via
      `SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`'s 3-term normal form, now for `i ≠ j`).
    • `gaussComp_pd_pd_mixed_hyp_satisfiable` — non-vacuity: `V := id`, direction jets `P := fun _ k =>
      Pi.single i 1 k` (the constant field `∂ᵢ(id) = eᵢ`), `Pj0 := Pi.single j 1`, `Qj := 0` (`id` is
      linear, so all second jets vanish) jointly satisfy every hypothesis.

  ## HONEST DISTANCE.  Fully abstract in `V`/`A`; does NOT instantiate `uniformInverseChart`, does NOT
  touch `kPrime`/`hcomp` literally, does NOT do the base-slot CoV (item a), truncation-tail (item c), or
  coordinate summation (item d).  `hCConv` NOT closed.  `hDuhamel`/`hDConv` unaffected.  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetHessian
import QIQTH.HeatHessianMomentCancellation

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianPolyBound
open QIQTH.HeatResidualBound QIQTH.HeatHessMoment

namespace QIQTH.GaussCompMixedHessian

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. The mixed second coordinate partial of the composed Gaussian.
    ############################################################################### -/

/-- **★★ `gaussComp_pd_pd_mixed` — THE MIXED SECOND COORDINATE PARTIAL.**  For `V : Point n → Point n`
    with inner `i`-line jet field `P` (`∀ x`), outer `j`-line jet `Pj0` of `V` itself at `x₀`, and outer
    `j`-line jet `Qj` of the FIELD `y ↦ P y` at `x₀` (the mixed second jet `∂ⱼ(∂ᵢV)`),
      `pd (pd (G_τ∘V) i) j x₀
          = G_τ(V x₀) · [ ⟨V x₀,Pj0⟩⟨V x₀,P x₀⟩/(4τ²) − (⟨Pj0,P x₀⟩ + ⟨V x₀,Qj⟩)/(2τ) ]`.
    Route: `φ := G_τ∘V` on the whole space has, at every `y`, `pd φ i y = φ(y)·h(y)` with `h(y) :=
    −⟨V y,P y⟩/(2τ)` (`gaussComp_pd`, ∀ y); differentiate this product in direction `j` at `x₀` via
    `pd_mul` (needs `φ`, `h` both `j`-differentiable at `x₀`, from `hVj1`/`hPj1`), then evaluate the two
    factor-derivatives (`pd φ j x₀` again by `gaussComp_pd` with `hVj1`; `pd h j x₀` by the product rule on
    `∑ V·P`).  Fully honest: no commutation hypothesis assumed, `i = j` recovers `ChartJetHessian.
    gaussComp_pd_pd`.  NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_mixed (V : Point n → Point n) (P : Point n → Fin n → ℝ)
    (Pj0 Qj : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hVj1 : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x₀ j s) k) (Pj0 k) (x₀ j))
    (hPj1 : ∀ k, HasDerivAt (fun s : ℝ => P (Function.update x₀ j s) k) (Qj k) (x₀ j)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) i y) j x₀
      = gaussDdim τ (V x₀)
        * ((∑ k, V x₀ k * Pj0 k) * (∑ k, V x₀ k * P x₀ k) / (4 * τ ^ 2)
            - ((∑ k, Pj0 k * P x₀ k) + (∑ k, V x₀ k * Qj k)) / (2 * τ)) := by
  -- (1) inner `pd` as a function (S1a ∀ y)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (P y) τ hτ i y (fun k => hV1 y k))
  rw [hinner]
  -- (2) `j`-differentiabilities of the two factors at `x₀`
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) j x₀ :=
    (gaussComp_hasDerivAt_line V Pj0 τ hτ j x₀ hVj1).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ j s) k) (x₀ j) :=
    fun k => (hVj1 k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => P (Function.update x₀ j s) k) (x₀ j) :=
    fun k => (hPj1 k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) j x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ j s) k * P (Function.update x₀ j s) k) (x₀ j)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) j x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ j s) k * P (Function.update x₀ j s) k) / (2 * τ))
        (x₀ j)
    exact (hsumPdiff.neg).div_const (2 * τ)
  -- (3) Leibniz on the S1a normal form, `j`-direction
  rw [pd_mul (fun y => gaussDdim τ (V y)) (fun y => -(∑ k, V y k * P y k) / (2 * τ)) j x₀ hGf hhf,
      gaussComp_pd V Pj0 τ hτ j x₀ hVj1,
      pd_neg_div_const (fun y => ∑ k, V y k * P y k) (2 * τ) j x₀ hsumPdiff]
  -- (4) `∂ⱼ(∑ V·P) = ∑ (Pj0·P + V·Qj)`
  have hpdsum : pd (fun y => ∑ k, V y k * P y k) j x₀
      = ∑ k, (Pj0 k * P x₀ k + V x₀ k * Qj k) := by
    rw [pd_sum (Finset.univ) (fun k y => V y k * P y k) j x₀
        (fun k _ => (hdV k).mul (hdP k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pd_mul (fun y => V y k) (fun y => P y k) j x₀ (hdV k) (hdP k)]
    have h1 : pd (fun y => V y k) j x₀ = Pj0 k := by simp only [pd]; exact (hVj1 k).deriv
    have h2 : pd (fun y => P y k) j x₀ = Qj k := by simp only [pd]; exact (hPj1 k).deriv
    rw [h1, h2]
  rw [hpdsum, Finset.sum_add_distrib]
  have hτ' : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-! ###############################################################################
    ### 2. Identification with `heatHessMult` — the J4-998 abstract multiplier.
    ############################################################################### -/

/-- **★★★ `gaussComp_pd_pd_mixed_eq_heatHessMult_sub` — THE IDENTIFICATION.**  The mixed second
    coordinate partial equals the J4-998 abstract Gaussian-Hessian multiplier `heatHessMult` MINUS the
    `Qj`-jet correction:
      `∂ⱼ∂ᵢ[G_τ∘V](x₀) = heatHessMult τ Pj0 (P x₀) (V x₀) − G_τ(V x₀)·⟨V x₀,Qj⟩/(2τ)`.
    Pure algebraic unfolding of `heatHessMult`'s definition against `gaussComp_pd_pd_mixed`'s RHS — the
    two brackets coincide termwise.  This is the missing link between kPrime's LITERAL mixed chain-rule
    Hessian and the abstract moment-cancellation object whose `τ^{−1/2}` rate J4-998/999/1000 already
    control (once `V`, `A` are instantiated to the concrete chart and the `Qj`-term is separately
    dominated — NOT done here).  NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_mixed_eq_heatHessMult_sub (V : Point n → Point n) (P : Point n → Fin n → ℝ)
    (Pj0 Qj : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hVj1 : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x₀ j s) k) (Pj0 k) (x₀ j))
    (hPj1 : ∀ k, HasDerivAt (fun s : ℝ => P (Function.update x₀ j s) k) (Qj k) (x₀ j)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) i y) j x₀
      = heatHessMult τ Pj0 (P x₀) (V x₀)
        - gaussDdim τ (V x₀) * (∑ k, V x₀ k * Qj k) / (2 * τ) := by
  rw [gaussComp_pd_pd_mixed V P Pj0 Qj τ hτ i j x₀ hV1 hVj1 hPj1]
  unfold heatHessMult
  ring

/-! ###############################################################################
    ### 3. The amplitude-weighted mixed Leibniz normal form.
    ############################################################################### -/

/-- **`gaussComp_amp_pd_pd_mixed`.**  The amplitude-weighted generalization of `gaussComp_pd_pd_mixed`,
    mirroring `ChartJetHessian.gaussComp_amp_pd_pd` for `i ≠ j`: for the full product `H := fun x =>
    gaussDdim τ (V x) · A x`,
      `∂ⱼ∂ᵢH(x₀) = [gaussComp_pd_pd_mixed]·A x₀
                     + (∂ᵢ(G_τ∘V))(x₀)·∂ⱼA(x₀) + (∂ⱼ(G_τ∘V))(x₀)·∂ᵢA(x₀)
                     + G_τ(V x₀)·∂ⱼ∂ᵢA(x₀)`,
    the mixed 4-term Leibniz normal form (the `i = j` case collapses the two cross terms into the `2·`
    coefficient of `gaussComp_amp_pd_pd`).  Matches `kPrime`'s literal amplitude-times-Gaussian shape
    (`SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`'s 3-term form, generalized off the diagonal).  NOT
    `a₁ = R/6`. -/
theorem gaussComp_amp_pd_pd_mixed (V : Point n → Point n) (A : Point n → ℝ)
    (P : Point n → Fin n → ℝ) (Pj0 Qj : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (x₀ : Point n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hVj1 : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x₀ j s) k) (Pj0 k) (x₀ j))
    (hPj1 : ∀ k, HasDerivAt (fun s : ℝ => P (Function.update x₀ j s) k) (Qj k) (x₀ j))
    (hA1i : ∀ x, PdiffAt A i x) (hA1j : PdiffAt A j x₀)
    (hA2 : PdiffAt (fun y => pd A i y) j x₀) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y) j x₀
      = gaussDdim τ (V x₀)
          * ((∑ k, V x₀ k * Pj0 k) * (∑ k, V x₀ k * P x₀ k) / (4 * τ ^ 2)
              - ((∑ k, Pj0 k * P x₀ k) + (∑ k, V x₀ k * Qj k)) / (2 * τ)) * A x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * P x₀ k) / (2 * τ))) * pd A j x₀
        + (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * Pj0 k) / (2 * τ))) * pd A i x₀
        + gaussDdim τ (V x₀) * pd (fun y => pd A i y) j x₀ := by
  -- Gaussian factor `i`-differentiability at every base point (needed for the inner Leibniz, ∀ y)
  have hGfP : ∀ y, PdiffAt (fun z => gaussDdim τ (V z)) i y :=
    fun y => (gaussComp_hasDerivAt_line V (P y) τ hτ i y (fun k => hV1 y k)).differentiableAt
  -- inner Leibniz normal form, ∀ y
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y)
      = (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y
          + gaussDdim τ (V y) * pd A i y) :=
    funext (fun y => pd_mul (fun z => gaussDdim τ (V z)) A i y (hGfP y) (hA1i y))
  rw [hinner]
  -- `j`-differentiability of the two summands at `x₀`
  have hGinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (P y) τ hτ i y (fun k => hV1 y k))
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) j x₀ :=
    (gaussComp_hasDerivAt_line V Pj0 τ hτ j x₀ hVj1).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ j s) k) (x₀ j) :=
    fun k => (hVj1 k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => P (Function.update x₀ j s) k) (x₀ j) :=
    fun k => (hPj1 k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) j x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ j s) k * P (Function.update x₀ j s) k) (x₀ j)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) j x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ j s) k * P (Function.update x₀ j s) k) / (2 * τ))
        (x₀ j)
    exact (hsumPdiff.neg).div_const (2 * τ)
  have hpdGf_pdiff : PdiffAt (fun y => pd (fun z => gaussDdim τ (V z)) i y) j x₀ := by
    rw [hGinner]; exact hGf.mul hhf
  -- outer sum + two Leibniz splits, `j`-direction
  rw [pd_add (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y)
        (fun y => gaussDdim τ (V y) * pd A i y) j x₀
        (hpdGf_pdiff.mul hA1j) (hGf.mul hA2),
      pd_mul (fun y => pd (fun z => gaussDdim τ (V z)) i y) A j x₀ hpdGf_pdiff hA1j,
      pd_mul (fun y => gaussDdim τ (V y)) (fun y => pd A i y) j x₀ hGf hA2]
  -- substitute the mixed Hessian (S1b-mixed) and the two first-order jets (S1a, directions i and j)
  rw [gaussComp_pd_pd_mixed V P Pj0 Qj τ hτ i j x₀ hV1 hVj1 hPj1,
      gaussComp_pd V Pj0 τ hτ j x₀ hVj1,
      gaussComp_pd V (P x₀) τ hτ i x₀ (fun k => hV1 x₀ k)]
  ring

/-! ###############################################################################
    ### 4. Non-vacuity — `V := id` (linear, all second jets vanish).
    ############################################################################### -/

/-- **Non-vacuity witness.**  `V := id`, inner jet field `P x k := if k = i then 1 else 0` (constant,
    `∂ᵢ(id) = eᵢ`), outer jets `Pj0 k := if k = j then 1 else 0`, `Qj := 0` (linear maps have vanishing
    second jets) jointly satisfy every hypothesis of `gaussComp_pd_pd_mixed`, for ANY `i ≠ j` (or `i = j`).
    A genuine, non-degenerate instance (not `V` constant / `P` the zero field). NOT `a₁ = R/6`. -/
theorem gaussComp_pd_pd_mixed_hyp_satisfiable (i j : Fin n) :
    ∃ (V : Point n → Point n) (P : Point n → Fin n → ℝ) (Pj0 Qj : Fin n → ℝ),
      (∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i)) ∧
      (∀ k, HasDerivAt (fun s : ℝ => V (Function.update (0 : Point n) j s) k) (Pj0 k) ((0:Point n) j)) ∧
      (∀ k, HasDerivAt (fun s : ℝ => P (Function.update (0 : Point n) j s) k) (Qj k)
        ((0:Point n) j)) := by
  classical
  refine ⟨id, fun _ k => if k = i then 1 else 0, fun k => if k = j then 1 else 0, fun _ => 0,
    ?_, ?_, ?_⟩
  · intro x k
    have hgoal : (fun _ k => if k = i then (1:ℝ) else 0) x k = if k = i then (1:ℝ) else 0 := rfl
    rw [show (fun s : ℝ => (id : Point n → Point n) (Function.update x i s) k)
        = (fun s : ℝ => Function.update x i s k) from rfl, hgoal]
    by_cases hk : k = i
    · subst hk; simpa using hasDerivAt_id (x k)
    · have heq : (fun s : ℝ => Function.update x i s k) = fun _ => x k := by
        funext s; rw [Function.update_of_ne hk]
      rw [heq, if_neg hk]; exact hasDerivAt_const _ _
  · intro k
    have hgoal : (fun k => if k = j then (1:ℝ) else 0) k = if k = j then (1:ℝ) else 0 := rfl
    rw [show (fun s : ℝ => (id : Point n → Point n) (Function.update (0 : Point n) j s) k)
        = (fun s : ℝ => Function.update (0 : Point n) j s k) from rfl, hgoal]
    by_cases hk : k = j
    · subst hk; simpa using hasDerivAt_id ((0 : Point n) k)
    · have heq : (fun s : ℝ => Function.update (0 : Point n) j s k) = fun _ => (0 : Point n) k := by
        funext s; rw [Function.update_of_ne hk]
      rw [heq, if_neg hk]; exact hasDerivAt_const _ _
  · intro k
    have hgoal : (fun _ : Fin n => (0:ℝ)) k = 0 := rfl
    rw [hgoal]
    have hPconst : (fun s : ℝ => (fun _ k => if k = i then (1:ℝ) else 0)
        (Function.update (0 : Point n) j s) k) = fun _ : ℝ => if k = i then (1:ℝ) else 0 := rfl
    rw [hPconst]
    exact hasDerivAt_const ((0 : Point n) j) (if k = i then (1:ℝ) else 0)

end QIQTH.GaussCompMixedHessian

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GaussCompMixedHessian
#print axioms gaussComp_pd_pd_mixed
#print axioms gaussComp_pd_pd_mixed_eq_heatHessMult_sub
#print axioms gaussComp_amp_pd_pd_mixed
#print axioms gaussComp_pd_pd_mixed_hyp_satisfiable
end AxiomChecks
