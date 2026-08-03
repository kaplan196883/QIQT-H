/-
  QIQTH / HeatResidualBound — ChartJetHessian.lean  (J4-130)

  ==========================================================================================
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel
  campaign.  It is NOT a₁ = R/6, and it proves NOTHING about R/6.  It supplies the exact
  chain-rule / Leibniz SECOND-`x`-derivative of a flat product Gaussian composed with a
  differentiable coordinate map — the derivative-layer counterpart of the banked order-0
  on-gate adapter (`vanVleckGatedWitness_gate_apply` / `vanVleckGatedWitness_zero_factor`).

  It is parametric in the composed map `V` and the amplitude `A`; it does NOT tie the
  Gaussian argument to the concrete inverse chart, and it makes NO estimates (that is
  S4/S5 later).  All hypotheses are honest first/second-`x`-jet facts of the composed map
  (satisfiable by any C²-along-the-`i`-line map — in particular the C⁴ chart pullback), and
  none is the conclusion.

  ------------------------------------------------------------------------------------------
  FINDINGS (read out of the repo before writing — the whole brick's shape depends on these):

  (F1)  `pd` convention  (QIQTH/Curvature.lean:30):
            `pd f i x = deriv (fun t => f (Function.update x i t)) (x i)`.
        i.e. the `i`-th COORDINATE partial derivative, taken by freezing all coordinates
        except `i`, varying coordinate `i` to the ABSOLUTE value `t`, and differentiating at
        `t = x i`.  So `pd (pd f i) i x₀ = ∂²` along the coordinate-`i` line through `x₀`.
        Because `Function.update x i (x i) = x` only EXTENSIONALLY (`Function.update_eq_self`,
        not defeq), the base point of every composed line derivative must be rewritten with
        `Function.update_eq_self` — done throughout below.

  (F2)  Witness `x`-structure  (QIQTH/AmplitudePackage.lean:130, :173):
            `vanVleckGatedWitness g gi hC hK S a b τ p q`  has field point `p` and base `q`.
        For `witnessSecondXDeriv … i τ z = pd (fun x => pd (fun x' => H_G τ x' z) i x) i 0`,
        the varying slot is the FIELD point `p = x'` (base `q = z` FIXED).  On the gate the
        A0 map gives the Gaussian argument as the CHART IMAGE
            `W z x' = uniformInverseChart g gi hC hK z x'`
        (base `q = z`, field `p = x'`) — so for the witness the composed map is
            `V := fun x' => uniformInverseChart g gi hC hK z x'`,   `V 0 = W z 0`.
        (The gate/`radialCutoff`/`Θ^{-1/2}·(u₀+u₁τ)` factors are the `x`-dependent amplitude
        `A`; near the gate interior the gate is the constant `1`, so `A` there is the smooth
        chart amplitude.  This file leaves `A` fully parametric.)

  Reused `pd`-Leibniz lemmas:  `pd_mul`, `pd_add`, `pd_sum`, `pd_const_mul`, `PdiffAt.mul`,
        `PdiffAt.add`, `PdiffAt_sum`  (QIQTH/Curvature.lean);  the flat 1-D Gaussian
        `HasDerivAt` bricks `heatKernel1D_hasDerivAt_x` (QIQTH/FlatHeatEquation.lean) and the
        product chain rule `HasDerivAt.fun_finsetProd`.
  ==========================================================================================
-/
import Mathlib
import QIQTH.GaussianHessianCancel
import QIQTH.HeatParametrixOrder

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianPolyBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    S1 — the exact chain-rule derivatives of a Gaussian composed with a map `V`.
    ############################################################################### -/

/-- **S1a (line form).**  For `V : Point n → Point n`, `τ > 0`, coordinate `i`, base `x`, and
    first `i`-line jet `P k` of the `k`-th component of `V` at `x`
      (`hV1 : ∀ k, HasDerivAt (fun s => V (update x i s) k) (P k) (x i)`),
    the composed Gaussian on the `i`-line has derivative
      `d/ds gaussDdim τ (V (update x i s)) |_{s = x i}
          = gaussDdim τ (V x) · (−(∑ₖ V x k · P k)/(2τ))`.
    (Log-derivative of the flat product Gaussian: each factor `G_τ(V_k)` contributes
    `(−V_k/2τ)·V'_k`.)  Pure 1-D calculus; no smoothness beyond the supplied jets. -/
theorem gaussComp_hasDerivAt_line (V : Point n → Point n) (P : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (x : Point n)
    (hV1 : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P k) (x i)) :
    HasDerivAt (fun s : ℝ => gaussDdim τ (V (Function.update x i s)))
      (gaussDdim τ (V x) * (-(∑ k, V x k * P k) / (2 * τ))) (x i) := by
  -- (i) each 1-D factor's derivative, via `heatKernel1D_hasDerivAt_x` composed with `hV1`.
  have hcomp : ∀ k : Fin n,
      HasDerivAt (fun s : ℝ => heatKernel1D τ (V (Function.update x i s) k))
        ((-(V x k) / (2 * τ)) * heatKernel1D τ (V x k) * P k) (x i) := by
    intro k
    have hg : HasDerivAt (fun w : ℝ => heatKernel1D τ w)
        ((-(V (Function.update x i (x i)) k) / (2 * τ))
            * heatKernel1D τ (V (Function.update x i (x i)) k))
        (V (Function.update x i (x i)) k) :=
      heatKernel1D_hasDerivAt_x τ _ hτ
    have hc := hg.comp (x i) (hV1 k)
    rw [Function.update_eq_self] at hc
    simpa [Function.comp] using hc
  -- (ii) the product chain rule over the `n` factors.
  have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (f := fun k s => heatKernel1D τ (V (Function.update x i s) k)) (x := x i)
    (f' := fun k => (-(V x k) / (2 * τ)) * heatKernel1D τ (V x k) * P k)
    (fun k _ => hcomp k)
  -- (iii) identify the base function with `gaussDdim τ (V (update x i ·))`.
  have hfun : (fun s : ℝ => ∏ k, heatKernel1D τ (V (Function.update x i s) k))
      = (fun s : ℝ => gaussDdim τ (V (Function.update x i s))) := by
    funext s; rw [gaussDdim]
  rw [hfun] at hprod
  -- (iv) close the derivative-value algebra.
  convert hprod using 1
  -- goal:  gaussDdim τ (V x) * (−(∑ V P)/(2τ)) = ∑ k, (∏_{j≠k} G_j) • deriv_k
  rw [gaussDdim]
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase k,
          heatKernel1D τ (V (Function.update x i (x i)) j))
        • ((-(V x k) / (2 * τ)) * heatKernel1D τ (V x k) * P k)
      = (∏ j, heatKernel1D τ (V x j)) * ((-(V x k) / (2 * τ)) * P k) := by
    intro k _
    rw [smul_eq_mul, Function.update_eq_self,
        ← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
          (fun j => heatKernel1D τ (V x j)) (Finset.mem_univ k)]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  -- reduce `∑ (−V_k/2τ)·P_k` to `(−∑ V_k P_k)/(2τ)` without `Finset.sum_neg`
  have hRHS : (∑ k, -V x k / (2 * τ) * P k) = (∑ k, V x k * P k) * (-(2 * τ)⁻¹) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hRHS]; ring

/-- **S1a (`pd` value form).**  The coordinate partial of the composed Gaussian:
      `pd (fun x => gaussDdim τ (V x)) i x = gaussDdim τ (V x) · (−(∑ₖ V x k · P k)/(2τ))`.
    Immediate from `gaussComp_hasDerivAt_line` via `HasDerivAt.deriv`. -/
theorem gaussComp_pd (V : Point n → Point n) (P : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (x : Point n)
    (hV1 : ∀ k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P k) (x i)) :
    pd (fun y => gaussDdim τ (V y)) i x
      = gaussDdim τ (V x) * (-(∑ k, V x k * P k) / (2 * τ)) := by
  simp only [pd]
  exact (gaussComp_hasDerivAt_line V P τ hτ i x hV1).deriv

/-! ### S1b — the exact second coordinate partial of the composed Gaussian. -/

/-- Division form of `pd_const_mul`: `∂ᵢ(−f/c) = −(∂ᵢf)/c`. -/
theorem pd_neg_div_const (f : Point n → ℝ) (c : ℝ) (i : Fin n) (x : Point n)
    (hf : PdiffAt f i x) :
    pd (fun y => -(f y) / c) i x = -(pd f i x) / c := by
  have h1 : (fun y : Point n => -(f y) / c) = (fun y => (-c⁻¹) * f y) := by
    funext y; ring
  rw [h1, pd_const_mul _ _ i x hf]; ring

/-- **S1b — the second coordinate partial (chain-rule Hessian).**  With first `i`-line jet field
    `P x k` (`hV1`, ∀ x) and second `i`-line jet `Q k` at `x₀` (`hP1`) of the components of `V`,
      `pd (pd (fun x => gaussDdim τ (V x)) i) i x₀
          = gaussDdim τ (V x₀) · [ (∑ₖ V x₀ k · P x₀ k)²/(4τ²)
                                    − (∑ₖ (P x₀ k)² + ∑ₖ V x₀ k · Q k)/(2τ) ]`.
    Route: `φ = gaussDdim τ ∘ V` on the `i`-line, `φ' = φ·h` with `h = −(∑ V·P)/(2τ)` (S1a),
    `φ'' = φ'·h + φ·h'`, `h' = −(∑ P² + ∑ V·Q)/(2τ)`.  Fully honest: the outer `pd`
    differentiates the S1a normal form (a genuine function equality, `hV1` ∀ x) — NO carried
    commutation hypothesis. -/
theorem gaussComp_pd_pd (V : Point n → Point n) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (x₀ : Point n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt (fun s : ℝ => P (Function.update x₀ i s) k) (Q k) (x₀ i)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z)) i y) i x₀
      = gaussDdim τ (V x₀)
        * ((∑ k, V x₀ k * P x₀ k) ^ 2 / (4 * τ ^ 2)
            - ((∑ k, P x₀ k ^ 2) + (∑ k, V x₀ k * Q k)) / (2 * τ)) := by
  -- (1) inner `pd` as a function (S1a ∀ y)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (P y) τ hτ i y (fun k => hV1 y k))
  rw [hinner]
  -- (2) differentiabilities of the two factors at `x₀`
  have hGf : PdiffAt (fun y => gaussDdim τ (V y)) i x₀ :=
    (gaussComp_hasDerivAt_line V (P x₀) τ hτ i x₀ (fun k => hV1 x₀ k)).differentiableAt
  have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hV1 x₀ k).differentiableAt
  have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => P (Function.update x₀ i s) k) (x₀ i) :=
    fun k => (hP1 k).differentiableAt
  have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * P (Function.update x₀ i s) k) (x₀ i)
    exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i x₀ := by
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * P (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  -- (3) Leibniz on the S1a normal form
  rw [pd_mul (fun y => gaussDdim τ (V y)) (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i x₀ hGf hhf,
      gaussComp_pd V (P x₀) τ hτ i x₀ (fun k => hV1 x₀ k),
      pd_neg_div_const (fun y => ∑ k, V y k * P y k) (2 * τ) i x₀ hsumPdiff]
  -- (4) `∂ᵢ(∑ V·P) = ∑ (P·P + V·Q)`
  have hpdsum : pd (fun y => ∑ k, V y k * P y k) i x₀
      = ∑ k, (P x₀ k * P x₀ k + V x₀ k * Q k) := by
    rw [pd_sum (Finset.univ) (fun k y => V y k * P y k) i x₀
        (fun k _ => (hdV k).mul (hdP k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pd_mul (fun y => V y k) (fun y => P y k) i x₀ (hdV k) (hdP k)]
    have h1 : pd (fun y => V y k) i x₀ = P x₀ k := by simp only [pd]; exact (hV1 x₀ k).deriv
    have h2 : pd (fun y => P y k) i x₀ = Q k := by simp only [pd]; exact (hP1 k).deriv
    rw [h1, h2]
  rw [hpdsum, Finset.sum_add_distrib]
  have hsq : (∑ k, P x₀ k * P x₀ k) = ∑ k, P x₀ k ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by ring)
  rw [hsq]
  have hτ' : τ ≠ 0 := hτ.ne'
  field_simp
  ring

/-! ###############################################################################
    S2 — the Leibniz normal form for the amplitude-weighted composed Gaussian.
    ############################################################################### -/

/-- **S2 — the Leibniz normal form.**  For the full product `H = (fun x => gaussDdim τ (V x)·A x)`
    (`A` = the amplitude in `x`, carried parametric with its own `i`-jets `pd A i x₀` and
    `pd(pd A i) i x₀`), the second coordinate partial is the twice-along-the-line product rule
      `pd (pd H i) i x₀
          = [S1b]·A x₀ + 2·[S1a-value]·(pd A i x₀) + gaussDdim τ (V x₀)·(pd(pd A i) i x₀)`,
    with `[S1b] = gaussComp_pd_pd` and `[S1a-value] = gaussDdim τ (V x₀)·(−(∑ V·P)/(2τ))`.
    This is the derivative-layer normal form the amplitude package `hD2Hexpand` consumes:
    a Hessian-weighted `A`-term, a gradient-weighted `∂A`-term, and a mass-weighted `∂²A`-term. -/
theorem gaussComp_amp_pd_pd (V : Point n → Point n) (A : Point n → ℝ)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (x₀ : Point n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt (fun s : ℝ => P (Function.update x₀ i s) k) (Q k) (x₀ i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i x₀) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y) i x₀
      = gaussDdim τ (V x₀)
          * ((∑ k, V x₀ k * P x₀ k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P x₀ k ^ 2) + (∑ k, V x₀ k * Q k)) / (2 * τ)) * A x₀
        + 2 * (gaussDdim τ (V x₀) * (-(∑ k, V x₀ k * P x₀ k) / (2 * τ))) * pd A i x₀
        + gaussDdim τ (V x₀) * pd (fun y => pd A i y) i x₀ := by
  -- Gaussian factor differentiabilities (S1a) at every base point
  have hGfP : ∀ y, PdiffAt (fun z => gaussDdim τ (V z)) i y :=
    fun y => (gaussComp_hasDerivAt_line V (P y) τ hτ i y (fun k => hV1 y k)).differentiableAt
  -- S1a normal form for `pd Gf` as a function (needed for the outer PdiffAt of `pd Gf`)
  have hGinner : (fun y => pd (fun z => gaussDdim τ (V z)) i y)
      = (fun y => gaussDdim τ (V y) * (-(∑ k, V y k * P y k) / (2 * τ))) :=
    funext (fun y => gaussComp_pd V (P y) τ hτ i y (fun k => hV1 y k))
  have hhf : PdiffAt (fun y => -(∑ k, V y k * P y k) / (2 * τ)) i x₀ := by
    have hdV : ∀ k, DifferentiableAt ℝ (fun s : ℝ => V (Function.update x₀ i s) k) (x₀ i) :=
      fun k => (hV1 x₀ k).differentiableAt
    have hdP : ∀ k, DifferentiableAt ℝ (fun s : ℝ => P (Function.update x₀ i s) k) (x₀ i) :=
      fun k => (hP1 k).differentiableAt
    have hsumPdiff : PdiffAt (fun y => ∑ k, V y k * P y k) i x₀ := by
      show DifferentiableAt ℝ
          (fun s : ℝ => ∑ k, V (Function.update x₀ i s) k * P (Function.update x₀ i s) k) (x₀ i)
      exact DifferentiableAt.fun_sum (fun k _ => (hdV k).mul (hdP k))
    show DifferentiableAt ℝ
        (fun s : ℝ => -(∑ k, V (Function.update x₀ i s) k * P (Function.update x₀ i s) k) / (2 * τ))
        (x₀ i)
    exact (hsumPdiff.neg).div_const (2 * τ)
  have hpdGf_pdiff : PdiffAt (fun y => pd (fun z => gaussDdim τ (V z)) i y) i x₀ := by
    rw [hGinner]; exact (hGfP x₀).mul hhf
  -- (1) inner Leibniz (∀ y)
  have hinner : (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y)
      = (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y
          + gaussDdim τ (V y) * pd A i y) :=
    funext (fun y => pd_mul (fun z => gaussDdim τ (V z)) A i y (hGfP y) (hA1 y))
  rw [hinner]
  -- (2) outer sum + two Leibniz splits
  rw [pd_add (fun y => pd (fun z => gaussDdim τ (V z)) i y * A y)
        (fun y => gaussDdim τ (V y) * pd A i y) i x₀
        (hpdGf_pdiff.mul (hA1 x₀)) ((hGfP x₀).mul hA2),
      pd_mul (fun y => pd (fun z => gaussDdim τ (V z)) i y) A i x₀ hpdGf_pdiff (hA1 x₀),
      pd_mul (fun y => gaussDdim τ (V y)) (fun y => pd A i y) i x₀ (hGfP x₀) hA2]
  -- (3) substitute S1b (pd∘pd of the Gaussian) and S1a (pd of the Gaussian)
  rw [gaussComp_pd_pd V P Q τ hτ i x₀ hV1 hP1,
      gaussComp_pd V (P x₀) τ hτ i x₀ (fun k => hV1 x₀ k)]
  ring

/-! ###############################################################################
    S3-seed — the CENTER (`x₀ = 0`) three-piece decomposition (exact; no estimates).
    ############################################################################### -/

/-- **S3-seed — the center normal form, decomposed.**  Specializing S2 to the RNC center
    `x₀ = 0` (write `Y := V 0` — for the concrete witness `Y = W z 0 = uniformInverseChart z 0`,
    `P 0`/`Q` the chart's first/second `i`-jets), the second coordinate partial splits EXACTLY into
      (i)  the canonical Hermite piece
             `gaussDdim τ Y · ((∑ Y·P)²/(4τ²) − (∑ P²)/(2τ)) · A 0`
           — with `Y ≈ −z`, `P ≈ −eᵢ` in the flat case this is the `((zᵢ)²−2τ)/(4τ²)`-shape of the
           amplitude package (`AmplitudeDerivativeData.hD2Hexpand`) up to the jet corrections;
      (ii) the centerJet term `gaussDdim τ Y · (−(∑ Y·Q)/(2τ)) · A 0` — the odd-parity candidate,
           left EXACT (NOT estimated: that is S4/S5);
      (iii) the cross (gradient-`∂A`) and mass (`∂²A`) amplitude terms.
    Pure regrouping of `gaussComp_amp_pd_pd`; NO estimates.  Instantiating `V := uniformInverseChart
    g gi hC hK z ·` and `A :=` the on-gate chart amplitude (banked `vanVleckGatedWitness_gate_apply`)
    turns this into the concrete `witnessSecondXDeriv` normal form on the gate interior. -/
theorem gaussComp_amp_center_decomp (V : Point n → Point n) (A : Point n → ℝ)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i : Fin n)
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n)) :
    pd (fun y => pd (fun z => gaussDdim τ (V z) * A z) i y) i (0 : Point n)
      = -- (i) canonical Hermite piece
        gaussDdim τ (V 0)
          * ((∑ k, V 0 k * P 0 k) ^ 2 / (4 * τ ^ 2) - (∑ k, P 0 k ^ 2) / (2 * τ)) * A 0
        -- (ii) centerJet (odd-parity candidate — kept EXACT)
      + gaussDdim τ (V 0) * (-(∑ k, V 0 k * Q k) / (2 * τ)) * A 0
        -- (iii) cross (gradient) + mass (∂²A) amplitude terms
      + (2 * (gaussDdim τ (V 0) * (-(∑ k, V 0 k * P 0 k) / (2 * τ))) * pd A i 0
          + gaussDdim τ (V 0) * pd (fun y => pd A i y) i 0) := by
  rw [gaussComp_amp_pd_pd V A P Q τ hτ i (0 : Point n) hV1 hP1 hA1 hA2]
  ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.gaussComp_hasDerivAt_line
#print axioms QIQTH.HeatResidualBound.gaussComp_pd
#print axioms QIQTH.HeatResidualBound.gaussComp_pd_pd
#print axioms QIQTH.HeatResidualBound.gaussComp_amp_pd_pd
#print axioms QIQTH.HeatResidualBound.gaussComp_amp_center_decomp
