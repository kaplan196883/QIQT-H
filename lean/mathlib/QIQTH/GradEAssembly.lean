/-
  GradEAssembly — J4-194: the `∇E` ABSORPTION ASSEMBLY (the `hEgrad`-shaped bound) of the
  `a₁ = R/6` heat-kernel campaign.  COMPOSES four already-banked bricks into the on-gate
  field-gradient bound of the residual normal form `E = χ·(G_τ·A) − annulusTerms`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign — the `hEgrad` amplitude-gradient assembly.  No `sorry`, no
  new axioms, no vacuous/unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file delivers (ns `QIQTH.GradEAssembly`).

    * ★ `gradGA_bound` — THE MAIN DELIVERABLE.  On the box `(0,T] × closedBall 0 b`,
        `|∂ᵢ(G_τ·A)(v)| ≤ C · ((√τ)⁻¹·(τ⁻¹)²) · gaussDdim (2τ) v`   ( = `C·τ^{−5/2}·G_{2τ}` ),
      with `A = residualCoeffA N g gi Θ u τ`, `C ≥ 0` assembled from `{hg,hgi,hw}`.  PURE composition
      of the four banked pieces:
        (1) J4-193 `gradGA_term_bound_skeleton`:
              `|∂ᵢ(G·A)| ≤ (|vᵢ|/2τ)·G_τ·|A| + G_τ·|∂ᵢA|`;
        (2) J4-190 `residualCoeffA_tau_weighted_bound`:  `τ²·|A| ≤ C₁`  (⟹ `|A| ≤ C₁·(τ⁻¹)²`);
        (3) J4-193 `residualCoeffA_grad_tau_weighted_bound`:  `τ²·|∂ᵢA| ≤ C₂` (⟹ `|∂ᵢA| ≤ C₂·(τ⁻¹)²`);
        (4) J4-191 `gaussDdim_linear_absorption` (`(|vᵢ|/τ)·G_τ ≤ Clin·(√τ)⁻¹·G_{2τ}`) and the
            `k=0` doubling-width lever `gaussDdim_radial_pow_absorption` (`G_τ ≤ C0·G_{2τ}`).
      Term 1 → `Clin·C₁·(√τ)⁻¹·(τ⁻¹)²·G_{2τ}`; Term 2 → `C0·C₂·√T·(√τ)⁻¹·(τ⁻¹)²·G_{2τ}`
      (the `√T` from `τ^{−2} = √τ·(√τ)⁻¹·τ^{−2} ≤ √T·(√τ)⁻¹·τ^{−2}` on `(0,T]`).

    * `residualCoeffA_slice_pdiffAt` — the field-slot `PdiffAt` of the residual amplitude slice, the
      `hA` input the skeleton needs, DISCHARGED from `{hg,hgi,hw}` via the joint `C^∞` upgrade
      `ThirdJetBounds.residualCoeffAWeighted_contDiff` + the pole-clearing identity.

    * `gradE_split_triangle` — the generic pointwise `|∂ᵢ(f₁−f₂)| ≤ |∂ᵢf₁| + |∂ᵢf₂|` (from `pd_sub`).

    * `gradE_bound_assembled` — the `E`-gradient triangle at the residual normal form: from
      `cutoffError_eq_cutoff_gauss_A_sub_annulus` (`E = χ·(G·A) − annulusTerms`),
        `|∂ᵢE| ≤ |∂ᵢ(χ·(G·A))| + |∂ᵢ annulusTerms|`.
      The on-gate `χ·(G·A)` piece is controlled (near the diagonal `χ≡1`) by `gradGA_bound`; the
      annulus-supported `∂ᵢ annulusTerms` is HONESTLY CARRIED as the remaining named term (its
      third-jet bound is the downstream annulus layer, NOT composed here).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## ★ THE τ-POWER ALIGNMENT VERDICT (honest, load-bearing — read it).

  The `hEgrad` consumer (`LeviLipschitz`/`GeneralBaseJets` §hEgrad) wants
      `|∂ᵢE| ≤ C_g · τ^{−1/2} · (G-shape)`,   `G-shape = baseKernelW 2 0 τ = gaussDdim (2τ)`.
  The composition above delivers `|∂ᵢ(G·A)| ≤ C·τ^{−5/2}·G_{2τ}` — a genuine `τ^{−2}` GAP versus the
  target `τ^{−1/2}·G_{2τ}`.  This `τ^{−2}` is NOT a new obstruction: it is EXACTLY the same `τ^{−2}`
  the ZEROTH bound already carries.  The banked zeroth carry (`RestrictedEboundW.hEboundW_le`) is
      `|E τ p q| ≤ C · baseKernelW 2 0 τ p q = C · gaussDdim (2τ) (p−q)`   (α = 0, τ-FREE),
  yet the raw amplitude `A = residualCoeffA` has a genuine `1/τ²` Laurent head (as `τ↓0`, `A→∞`).  So
  the raw zeroth composition `|E| = |χ·G_τ·A| ≤ (√2)ⁿ·G_{2τ}·(C₁/τ²)` is ITSELF `τ^{−2}·G_{2τ}`; the
  gap from that to the assumed τ-free `C·G_{2τ}` is precisely the C4c DeWitt-cancellation wall (the
  transport recursion is engineered to kill the singular low-order part, making the TRUE residual
  amplitude `O(τ^{N−1})` rather than `1/τ²`).  That wall is CARRIED, not derived, at zeroth order
  (`RestrictedEboundW` states this explicitly).

  VERDICT.  `gradGA_bound`'s `τ^{−5/2}·G_{2τ}` = (zeroth raw `τ^{−2}·G_{2τ}`) × (the extra `τ^{−1/2}`
  the linear Gaussian-absorption costs at the gradient).  Aligning to the target `τ^{−1/2}·G_{2τ}`
  requires the SAME C4c τ^{−2} cancellation the zeroth bound already assumes — it is the GRADIENT of
  the already-carried wall, NOT an independent gap.  Once the zeroth C4c bound is discharged (residual
  amplitude genuinely bounded, `α ≥ 0`, in place of `1/τ²`), re-running THIS composition with the
  bounded amplitude yields the target `τ^{−1/2}·G_{2τ}` verbatim.  This file bounds the honest
  `τ^{−5/2}` form from the CURRENT (uncancelled) `residualCoeffA`; it does not smuggle the C4c
  cancellation.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ThirdJetBounds
import QIQTH.GaussianGradAbsorption
import QIQTH.ErrorKernelFactorization

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.ResidueBound
open QIQTH.CompactJetBounds QIQTH.ThirdJetBounds QIQTH.GaussianGradAbsorption
open QIQTH.ErrorKernelFactorization QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz
open scoped BigOperators ContDiff

namespace QIQTH.GradEAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ## 1.  The field-slot `PdiffAt` of the residual amplitude slice (the skeleton's `hA` input). -/

/-- **`residualCoeffA_slice_pdiffAt`.**  For `t ≠ 0` the residual-amplitude slice
    `w ↦ residualCoeffA N g gi Θ u t w` is partially differentiable in every direction — the `hA`
    hypothesis the `∇(G·A)` skeleton needs, DISCHARGED from `{hg,hgi,hw}`.  Route: the joint `C^∞`
    upgrade `residualCoeffAWeighted_contDiff` gives the τ²-cleared amplitude `C^∞`, the pole-clearing
    identity `residualCoeffAWeighted_eq` turns the slice into `(1/t²)·(cleared slice)`, hence `C^∞`,
    hence `PdiffAt`.  NOT `a₁ = R/6`. -/
theorem residualCoeffA_slice_pdiffAt (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (t : ℝ) (ht : t ≠ 0) (i : Fin n) (v : Point n) :
    PdiffAt (fun w => residualCoeffA N g gi Θ u t w) i v := by
  have hFcd : ContDiff ℝ ∞ (fun p : ℝ × Point n => residualCoeffAWeighted N g gi Θ u p.1 p.2) :=
    residualCoeffAWeighted_contDiff N g gi Θ u hg hgi hw
  have hslice : ContDiff ℝ ∞ (fun w : Point n => residualCoeffAWeighted N g gi Θ u t w) :=
    hFcd.comp (contDiff_const.prodMk contDiff_id)
  have hAslice : ContDiff ℝ ∞ (fun w : Point n => residualCoeffA N g gi Θ u t w) := by
    have heqf : (fun w : Point n => residualCoeffA N g gi Θ u t w)
        = (fun w : Point n => (1 / t ^ 2) * residualCoeffAWeighted N g gi Θ u t w) := by
      funext w
      rw [← residualCoeffAWeighted_eq N g gi Θ u t ht w, ← mul_assoc, one_div,
        inv_mul_cancel₀ (pow_ne_zero 2 ht), one_mul]
    rw [heqf]
    exact contDiff_const.mul hslice
  exact PdiffAt_of_contDiff_inf _ hAslice i v

/-! ## 2.  ★ The on-gate `∇(G·A)` bound — the four-brick composition. -/

/-- **★ `gradGA_bound` — the on-gate `∇(G·A)` amplitude-gradient bound.**  On `(0,T] × closedBall 0 b`,
      `|∂ᵢ(gaussDdim τ · residualCoeffA N g gi Θ u τ)(v)|
          ≤ C · ((√τ)⁻¹ · (τ⁻¹)²) · gaussDdim (2τ) v`     ( = `C·τ^{−5/2}·G_{2τ}` ),
    with `C ≥ 0` assembled from `{hg,hgi,hw}`.  Composition of the four banked bricks (see header):
    the Leibniz skeleton (J4-193) splits into `(|vᵢ|/2τ)·G_τ·|A| + G_τ·|∂ᵢA|`; the τ²-weighted pole
    bounds (J4-190/J4-193) supply `|A|,|∂ᵢA| ≤ C_·/τ²`; the linear (`k=1`) and `k=0` Gaussian
    doubling-width absorptions (J4-191) turn `(|vᵢ|/τ)·G_τ` and `G_τ` into `G_{2τ}`-multiples.  The
    resulting `τ^{−5/2}` (NOT `τ^{−1/2}`) is the honest gradient of the still-uncancelled `1/τ²`
    amplitude — see the file-header τ-power ALIGNMENT VERDICT.  NOT `a₁ = R/6`. -/
theorem gradGA_bound (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (T b : ℝ) (i : Fin n)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (v : Point n), 0 < τ → τ ≤ T →
      v ∈ Metric.closedBall (0 : Point n) b →
      |pd (fun w => gaussDdim τ w * residualCoeffA N g gi Θ u τ w) i v|
        ≤ C * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2) * gaussDdim (2 * τ) v := by
  obtain ⟨C₁, hC₁, hAb⟩ := residualCoeffA_tau_weighted_bound N g gi Θ u T b hg hgi hw
  obtain ⟨C₂, hC₂, hGb⟩ := residualCoeffA_grad_tau_weighted_bound N g gi Θ u T b i hg hgi hw
  obtain ⟨Clin, hClin, hlin⟩ := gaussDdim_linear_absorption (n := n)
  obtain ⟨C0, hC0, hrad0⟩ := gaussDdim_radial_pow_absorption (n := n) 0
  refine ⟨Clin * C₁ + C0 * C₂ * Real.sqrt T,
    add_nonneg (mul_nonneg hClin.le hC₁)
      (mul_nonneg (mul_nonneg hC0.le hC₂) (Real.sqrt_nonneg T)),
    fun τ v hτ hτT hv => ?_⟩
  have hτne : τ ≠ 0 := hτ.ne'
  have hGnn : (0 : ℝ) ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  have hApos : (0 : ℝ) ≤ |residualCoeffA N g gi Θ u τ v| := abs_nonneg _
  have hpdApos : (0 : ℝ) ≤ |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := abs_nonneg _
  have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
  have hτ2ne : (τ ^ 2 : ℝ) ≠ 0 := ne_of_gt hτ2
  have hsqτpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hG2nn : (0 : ℝ) ≤ gaussDdim (2 * τ) v := gaussDdim_nonneg (2 * τ) v
  -- (2)/(3): pole bounds  `|A|, |∂ᵢA| ≤ C_··(τ⁻¹)²`.
  have hAle : |residualCoeffA N g gi Θ u τ v| ≤ C₁ * (τ⁻¹) ^ 2 := by
    have h := hAb τ v hτ hτT hv
    have e1 : |residualCoeffA N g gi Θ u τ v|
        = (τ ^ 2)⁻¹ * (τ ^ 2 * |residualCoeffA N g gi Θ u τ v|) := by
      rw [← mul_assoc, inv_mul_cancel₀ hτ2ne, one_mul]
    rw [e1]
    calc (τ ^ 2)⁻¹ * (τ ^ 2 * |residualCoeffA N g gi Θ u τ v|)
        ≤ (τ ^ 2)⁻¹ * C₁ := mul_le_mul_of_nonneg_left h (by positivity)
      _ = C₁ * (τ⁻¹) ^ 2 := by rw [inv_pow]; ring
  have hpdAle : |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| ≤ C₂ * (τ⁻¹) ^ 2 := by
    have h := hGb τ v hτ hτT hv
    have e1 : |pd (fun w => residualCoeffA N g gi Θ u τ w) i v|
        = (τ ^ 2)⁻¹ * (τ ^ 2 * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v|) := by
      rw [← mul_assoc, inv_mul_cancel₀ hτ2ne, one_mul]
    rw [e1]
    calc (τ ^ 2)⁻¹ * (τ ^ 2 * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v|)
        ≤ (τ ^ 2)⁻¹ * C₂ := mul_le_mul_of_nonneg_left h (by positivity)
      _ = C₂ * (τ⁻¹) ^ 2 := by rw [inv_pow]; ring
  -- (4): `G_τ ≤ C0·G_{2τ}` (the `k=0` doubling-width lever).
  have hG0 : gaussDdim τ v ≤ C0 * gaussDdim (2 * τ) v := by
    have h := hrad0 τ hτ v; simpa using h
  -- (4): the linear absorption at `j = i`.
  have hlinv : |v i| / τ * gaussDdim τ v ≤ Clin * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v :=
    hlin τ hτ v i
  -- (1): the Leibniz skeleton (with `hA` discharged).
  have hPd : PdiffAt (fun w => residualCoeffA N g gi Θ u τ w) i v :=
    residualCoeffA_slice_pdiffAt N g gi Θ u hg hgi hw τ hτne i v
  have hskel := gradGA_term_bound_skeleton N g gi Θ u τ hτ i v hPd
  -- Term 1  →  `Clin·C₁·(√τ)⁻¹·(τ⁻¹)²·G_{2τ}`.
  have hden : |v i| / (2 * τ) ≤ |v i| / τ := by
    have h2 : |v i| / (2 * τ) = (|v i| / τ) / 2 := by field_simp
    rw [h2]
    have hnn : (0 : ℝ) ≤ |v i| / τ := div_nonneg (abs_nonneg _) hτ.le
    linarith
  have hpos1 : (0 : ℝ) ≤ Clin * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v :=
    mul_nonneg (mul_nonneg hClin.le (by positivity)) hG2nn
  have hT1 : |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v|
      ≤ Clin * C₁ * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := by
    calc |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v|
        ≤ (|v i| / τ * gaussDdim τ v) * |residualCoeffA N g gi Θ u τ v| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden hGnn) hApos
      _ ≤ (Clin * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v) * |residualCoeffA N g gi Θ u τ v| :=
          mul_le_mul_of_nonneg_right hlinv hApos
      _ ≤ (Clin * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ) v) * (C₁ * (τ⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left hAle hpos1
      _ = Clin * C₁ * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := by ring
  -- Term 2  →  `C0·C₂·√T·(√τ)⁻¹·(τ⁻¹)²·G_{2τ}`  (the `√T` from `τ^{−2} ≤ √T·(√τ)⁻¹·τ^{−2}`).
  have hpos2 : (0 : ℝ) ≤ C0 * gaussDdim (2 * τ) v := mul_nonneg hC0.le hG2nn
  have hbb : (0 : ℝ) ≤ (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v := mul_nonneg (by positivity) hG2nn
  have hcc : (0 : ℝ) ≤ C0 * C₂ := mul_nonneg hC0.le hC₂
  have hTt : (1 : ℝ) ≤ Real.sqrt T * (Real.sqrt τ)⁻¹ := by
    have hsqle : Real.sqrt τ ≤ Real.sqrt T := Real.sqrt_le_sqrt hτT
    have hh : Real.sqrt τ * (Real.sqrt τ)⁻¹ = 1 := mul_inv_cancel₀ hsqτpos.ne'
    have hmono : Real.sqrt τ * (Real.sqrt τ)⁻¹ ≤ Real.sqrt T * (Real.sqrt τ)⁻¹ :=
      mul_le_mul_of_nonneg_right hsqle (by positivity)
    rwa [hh] at hmono
  have hT2 : gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v|
      ≤ C0 * C₂ * Real.sqrt T * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := by
    calc gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v|
        ≤ (C0 * gaussDdim (2 * τ) v) * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| :=
          mul_le_mul_of_nonneg_right hG0 hpdApos
      _ ≤ (C0 * gaussDdim (2 * τ) v) * (C₂ * (τ⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left hpdAle hpos2
      _ = C0 * C₂ * ((τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := by ring
      _ ≤ C0 * C₂ * ((Real.sqrt T * (Real.sqrt τ)⁻¹) * ((τ⁻¹) ^ 2 * gaussDdim (2 * τ) v)) := by
          apply mul_le_mul_of_nonneg_left _ hcc
          calc (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v
              = 1 * ((τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := (one_mul _).symm
            _ ≤ (Real.sqrt T * (Real.sqrt τ)⁻¹) * ((τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) :=
                mul_le_mul_of_nonneg_right hTt hbb
      _ = C0 * C₂ * Real.sqrt T * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) := by ring
  -- Combine.
  calc |pd (fun w => gaussDdim τ w * residualCoeffA N g gi Θ u τ w) i v|
      ≤ |v i| / (2 * τ) * gaussDdim τ v * |residualCoeffA N g gi Θ u τ v|
          + gaussDdim τ v * |pd (fun w => residualCoeffA N g gi Θ u τ w) i v| := hskel
    _ ≤ Clin * C₁ * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v)
          + C0 * C₂ * Real.sqrt T * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2 * gaussDdim (2 * τ) v) :=
        add_le_add hT1 hT2
    _ = (Clin * C₁ + C0 * C₂ * Real.sqrt T) * ((Real.sqrt τ)⁻¹ * (τ⁻¹) ^ 2)
          * gaussDdim (2 * τ) v := by ring

/-! ## 3.  The `E`-gradient triangle assembly (`pd` of the residual normal form). -/

/-- **`gradE_split_triangle` — the generic pointwise gradient triangle.**  For fields `f₁, f₂`
    partially differentiable in direction `i` at `v`,
      `|∂ᵢ(f₁ − f₂)(v)| ≤ |∂ᵢf₁(v)| + |∂ᵢf₂(v)|`.
    Pure `pd_sub` + the scalar triangle inequality.  NOT `a₁ = R/6`. -/
theorem gradE_split_triangle (f₁ f₂ : Point n → ℝ) (i : Fin n) (v : Point n)
    (h1 : PdiffAt f₁ i v) (h2 : PdiffAt f₂ i v) :
    |pd (fun w => f₁ w - f₂ w) i v| ≤ |pd f₁ i v| + |pd f₂ i v| := by
  rw [pd_sub f₁ f₂ i v h1 h2]
  calc |pd f₁ i v - pd f₂ i v|
      = |pd f₁ i v + -(pd f₂ i v)| := by rw [sub_eq_add_neg]
    _ ≤ |pd f₁ i v| + |-(pd f₂ i v)| := abs_add_le _ _
    _ = |pd f₁ i v| + |pd f₂ i v| := by rw [abs_neg]

/-- **`gradE_bound_assembled` — the `E`-gradient triangle at the residual normal form.**  From the
    banked factorization `E = χ·(G_τ·A) − annulusTerms`
    (`cutoffError_eq_cutoff_gauss_A_sub_annulus`, at the concrete parametrix
    `H = heatParametrix N Θ u τ`), the field-gradient of the residual `E = cutoffErrorKernel …` splits
      `|∂ᵢE(v)| ≤ |∂ᵢ(χ·(G_τ·A))(v)| + |∂ᵢ annulusTerms(v)|`.
    The on-gate term `∂ᵢ(χ·(G_τ·A))` is controlled by `gradGA_bound` (near the diagonal `χ≡1`); the
    annulus-supported `∂ᵢ annulusTerms` is HONESTLY CARRIED as the named remaining term (the annulus
    third-jet layer — banked cutoff-derivative supports + the `√τ`-gain annulus levers — is NOT
    composed here).  The two `PdiffAt` and the metric-symmetry `hgisymm` hypotheses are genuine,
    satisfiable, non-vacuous.  NOT `a₁ = R/6`. -/
theorem gradE_bound_assembled (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (a b τ : ℝ) (hτ : 0 < τ) (i : Fin n) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (h1 : PdiffAt (fun w => radialCutoff a b w
      * (gaussDdim τ w * residualCoeffA N g gi Θ u τ w)) i v)
    (h2 : PdiffAt (fun w => annulusTerms g gi a b (heatParametrix N Θ u τ) w) i v) :
    |pd (fun w => cutoffErrorKernel g gi a b (heatParametrix N Θ u τ)
          (fun w' => deriv (fun s => heatParametrix N Θ u s w') τ) w) i v|
      ≤ |pd (fun w => radialCutoff a b w
            * (gaussDdim τ w * residualCoeffA N g gi Θ u τ w)) i v|
        + |pd (fun w => annulusTerms g gi a b (heatParametrix N Θ u τ) w) i v| := by
  have hE : (fun w => cutoffErrorKernel g gi a b (heatParametrix N Θ u τ)
        (fun w' => deriv (fun s => heatParametrix N Θ u s w') τ) w)
      = (fun w => radialCutoff a b w * (gaussDdim τ w * residualCoeffA N g gi Θ u τ w)
          - annulusTerms g gi a b (heatParametrix N Θ u τ) w) := by
    funext w
    exact cutoffError_eq_cutoff_gauss_A_sub_annulus N g gi Θ u a b τ hτ w hw (hgisymm w)
  rw [hE]
  exact gradE_split_triangle _ _ i v h1 h2

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms residualCoeffA_slice_pdiffAt
#print axioms gradGA_bound
#print axioms gradE_split_triangle
#print axioms gradE_bound_assembled

end AxiomChecks

end QIQTH.GradEAssembly
