/-
  GaussianProductCollapse — J4-936: the PRODUCT→SINGLE Gaussian envelope collapse, junction piece (5)
  of J4-933's `hCensusBound` re-audit.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── ★ THE CONSUMER REQUIREMENT. ──
    J4-933's headline domain bridge (`CensusDomainBridge.census_full_of_ball_bound_and_gaussEnv`)
    consumes an off-ball SINGLE-Gaussian envelope `henv : ∀ z, ρ ≤ ‖z‖ → |Φ z| ≤ Cenv·gaussDdim λ z`.
    But the concrete census integrand (`HCrossDerivEngineWired.hEnv_of_witnessCrudeEnv`, J4-929) is
    dominated by a PRODUCT of two Gaussians in the SAME variable `z`:
        `|deriv(witness)(a−s)·F s z 0| ≤ (Ccr·τ⁻¹·gaussDdim (wL·τ) (0−z))·(CF·gaussDdim (wF·s) z)`,
    with `τ = a−s`.  So piece (5) is to COLLAPSE that product of two Gaussians into a single Gaussian
    (times a constant), yielding exactly the `Cenv·gaussDdim λ z` shape `henv` needs.

  ── ★★ IT COLLAPSES EXACTLY (a heat-kernel semigroup identity). ──
    The two 1-D heat kernels `heatKernel1D a x = (√(4πa))⁻¹·e^{−x²/(4a)}` and `heatKernel1D b x`
    multiply to a single 1-D heat kernel of the REDUCED width `c = ab/(a+b)`, with the leftover
    normalization equal to `heatKernel1D (a+b) 0`:
        `heatKernel1D a x · heatKernel1D b x = heatKernel1D (a+b) 0 · heatKernel1D (ab/(a+b)) x`.
    (Exp: `−x²/(4a) − x²/(4b) = −x²(a+b)/(4ab) = −x²/(4·ab/(a+b))`; normalization:
    `√(4πa)·√(4πb) = √(4π(a+b))·√(4π·ab/(a+b))` since both square to `16π²ab`.)  Taking the product
    over the `n` coordinates gives the `d`-dimensional collapse
        `gaussDdim a x · gaussDdim b x = (heatKernel1D (a+b) 0)ⁿ · gaussDdim (ab/(a+b)) x`.
    Since `heatKernel1D (a+b) 0 > 0`, the prefactor is a genuine nonnegative constant, and
    `ab/(a+b) > 0` is a genuine positive width.  Combined with `gaussDdim` evenness (`0−z = −z`), the
    product bound becomes the single-Gaussian envelope `Cenv·gaussDdim λ z` with
    `Cenv = A·B·(heatKernel1D (a+b) 0)ⁿ ≥ 0`, `λ = ab/(a+b) > 0`.

  ── WHAT IS PROVEN.
    • `heatKernel1D_mul_collapse` — the exact 1-D product identity.
    • `gaussDdim_mul_collapse` (★): the exact `d`-dimensional product identity
        `gaussDdim a x · gaussDdim b x = (heatKernel1D (a+b) 0)ⁿ · gaussDdim (ab/(a+b)) x`.
    • `gaussProduct_single_gaussEnv` (★★): the census-shaped collapse — from `0<α,0<β,0≤A,0≤B`,
        produces `Cenv ≥ 0`, `λ > 0` such that any `val ≤ A·gaussDdim α (0−z)·(B·gaussDdim β z)`
        satisfies `val ≤ Cenv·gaussDdim λ z` — i.e. EXACTLY the `henv` hypothesis of
        `census_full_of_ball_bound_and_gaussEnv`, with `α = wL·τ`, `β = wF·s`, `A = Ccr·τ⁻¹`, `B = CF`.
    • `gaussProduct_single_gaussEnv_hyp_satisfiable` — non-vacuity at genuine positive widths.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  These are EXACT
  Gaussian-semigroup identities, strictly weaker than and orthogonal to the CoV/`R/6` conclusion.
  Non-vacuous: the widths `α,β>0` and constants `A,B≥0` are freely satisfiable and the produced
  envelope fires on genuine Gaussian products.  No existing banked file is edited.
-/
import Mathlib
import QIQTH.WidthAdapters
import QIQTH.GaussianConvolution
import QIQTH.ResidueBound

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.WidthAdapters QIQTH.GaussianConvolution QIQTH.ResidueBound

namespace QIQTH.GaussianProductCollapse

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §A — the exact 1-D heat-kernel product identity. -/

/-- **The 1-D heat-kernel product collapse (EXACT).**  For `a, b > 0`,
        `heatKernel1D a x · heatKernel1D b x = heatKernel1D (a+b) 0 · heatKernel1D (ab/(a+b)) x` .
    The two Gaussians multiply to a single Gaussian of reduced width `ab/(a+b)`, the leftover
    normalization being `heatKernel1D (a+b) 0`.  NOT `a₁ = R/6`. -/
theorem heatKernel1D_mul_collapse (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    heatKernel1D a x * heatKernel1D b x
      = heatKernel1D (a + b) 0 * heatKernel1D (a * b / (a + b)) x := by
  have hab : (0 : ℝ) < a + b := by linarith
  have habne : a + b ≠ 0 := ne_of_gt hab
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  -- the exponential factors combine (sum of the two exponents = the reduced-width exponent).
  have hexp : Real.exp (-x ^ 2 / (4 * a)) * Real.exp (-x ^ 2 / (4 * b))
      = Real.exp (-(0 : ℝ) ^ 2 / (4 * (a + b)))
          * Real.exp (-x ^ 2 / (4 * (a * b / (a + b)))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  -- the normalization constants combine (`√(4πa)·√(4πb) = √(4π(a+b))·√(4π·ab/(a+b))`).
  have hconst : (Real.sqrt (4 * Real.pi * a))⁻¹ * (Real.sqrt (4 * Real.pi * b))⁻¹
      = (Real.sqrt (4 * Real.pi * (a + b)))⁻¹
          * (Real.sqrt (4 * Real.pi * (a * b / (a + b))))⁻¹ := by
    rw [← mul_inv, ← mul_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  simp only [heatKernel1D]
  rw [mul_mul_mul_comm, hconst, hexp]
  ring

/-! ### §B — the `d`-dimensional product identity. -/

/-- **★ The `d`-dimensional Gaussian product collapse (EXACT).**  For `a, b > 0`,
        `gaussDdim a x · gaussDdim b x = (heatKernel1D (a+b) 0)ⁿ · gaussDdim (ab/(a+b)) x` .
    The coordinatewise 1-D collapse, taken over the `n` factors: the `n` leftover normalizations
    accumulate into `(heatKernel1D (a+b) 0)ⁿ`, and the reduced-width Gaussians reassemble into
    `gaussDdim (ab/(a+b))`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_mul_collapse (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Point n) :
    gaussDdim a x * gaussDdim b x
      = (heatKernel1D (a + b) 0) ^ n * gaussDdim (a * b / (a + b)) x := by
  simp only [gaussDdim]
  rw [← Finset.prod_mul_distrib,
    Finset.prod_congr rfl (fun k _ => heatKernel1D_mul_collapse a b (x k) ha hb),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### §C — the census-shaped single-Gaussian envelope (junction piece (5)). -/

/-- **★★ `gaussProduct_single_gaussEnv` — the product→single-Gaussian envelope collapse.**  From
    `0 < α`, `0 < β` and `0 ≤ A`, `0 ≤ B`, there is a nonnegative constant `Cenv` and a positive width
    `λ` such that ANY quantity `val` dominated by the two-Gaussian product `A·gaussDdim α (0−z)·(B·gaussDdim β z)`
    is dominated by the SINGLE Gaussian `Cenv·gaussDdim λ z`.  Concretely
        `Cenv = A·B·(heatKernel1D (α+β) 0)ⁿ`,   `λ = α·β/(α+β)`.
    This is EXACTLY the `henv : |Φ z| ≤ Cenv·gaussDdim λ z` hypothesis of J4-933's
    `census_full_of_ball_bound_and_gaussEnv`, with `α = wL·τ`, `β = wF·s`, `A = Ccr·τ⁻¹`, `B = CF`
    (the concrete crude-environment envelope of `hEnv_of_witnessCrudeEnv`).  Junction piece (5) of
    J4-933's `hCensusBound` re-audit.  NOT `a₁ = R/6`. -/
theorem gaussProduct_single_gaussEnv
    (A B α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ (Cenv lam : ℝ), 0 < lam ∧ 0 ≤ Cenv ∧
      ∀ (z : Point n) (val : ℝ),
        val ≤ A * gaussDdim α (0 - z) * (B * gaussDdim β z) →
        val ≤ Cenv * gaussDdim lam z := by
  have habpos : (0 : ℝ) < α + β := by linarith
  have hkpos : 0 < heatKernel1D (α + β) 0 := heatKernel1D_pos _ _ habpos
  refine ⟨A * B * (heatKernel1D (α + β) 0) ^ n, α * β / (α + β),
    div_pos (mul_pos hα hβ) habpos,
    mul_nonneg (mul_nonneg hA hB) (pow_nonneg hkpos.le n), ?_⟩
  intro z val hbd
  refine hbd.trans (le_of_eq ?_)
  rw [zero_sub, gaussDdim_neg]
  rw [show A * gaussDdim α z * (B * gaussDdim β z)
        = A * B * (gaussDdim α z * gaussDdim β z) by ring,
    gaussDdim_mul_collapse α β hα hβ z]
  ring

/-- **Non-vacuity of `gaussProduct_single_gaussEnv`.**  The hypothesis bundle is satisfiable at genuine
    positive widths `α = β = 1` and constants `A = B = 1`, and the produced envelope genuinely fires on
    the real Gaussian product `val = gaussDdim 1 (0−z)·gaussDdim 1 z` at any `z`: it is `≤ Cenv·gaussDdim λ z`.
    So the collapse is exercised on an actual product of Gaussians, not a degenerate bundle.  NOT `a₁ = R/6`. -/
theorem gaussProduct_single_gaussEnv_hyp_satisfiable :
    ∃ (A B α β : ℝ) (_ : 0 < α) (_ : 0 < β) (_ : 0 ≤ A) (_ : 0 ≤ B)
      (Cenv lam : ℝ), 0 < lam ∧ 0 ≤ Cenv ∧
      ∀ (z : Point n),
        gaussDdim α (0 - z) * gaussDdim β z ≤ Cenv * gaussDdim lam z := by
  obtain ⟨Cenv, lam, hlam, hCenv, hbd⟩ :=
    gaussProduct_single_gaussEnv (n := n) 1 1 1 1 one_pos one_pos zero_le_one zero_le_one
  refine ⟨1, 1, 1, 1, one_pos, one_pos, zero_le_one, zero_le_one, Cenv, lam, hlam, hCenv, ?_⟩
  intro z
  have := hbd z (gaussDdim 1 (0 - z) * gaussDdim 1 z) (by ring_nf; rfl)
  simpa using this

end QIQTH.GaussianProductCollapse

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GaussianProductCollapse
#print axioms heatKernel1D_mul_collapse
#print axioms gaussDdim_mul_collapse
#print axioms gaussProduct_single_gaussEnv
#print axioms gaussProduct_single_gaussEnv_hyp_satisfiable
end AxiomChecks
