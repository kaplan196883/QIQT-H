/-
  C4cDecomposition — M6 / C4c: the precise decomposition of the global off-diagonal parametrix
  residual bound `hEboundW`, isolating the REACHABLE sub-pieces (global Gaussian comparison,
  Gaussian-cofactor global domination, near/far splice) from the deep FAR-FIELD cutoff and the
  OFF-DIAGONAL all-base-point walls, toward `hEboundW : ∀ τ p q, 0<τ → |E τ p q| ≤ C·baseKernelW 2 0
  τ p q`.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHERE C4c SITS (read it — this file does not fabricate; it decomposes and lands what is reachable).

  The conditional true-kernel `a₁ = R/6` (`TrueKernelA1.trueKernel_diagonal_a1_eq_R6`) is proved
  MODULO one labeled analytic primitive, the GLOBAL width-2 one-step residual bound

      `hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C · baseKernelW 2 0 τ p q`      (C4c),

  where `E` is the abstract two-point space-time residual and `baseKernelW 2 0 τ p q = gaussDdim (2τ)
  (p−q)` is the width-2 (doubled-time) base kernel.  `ParametrixHEboundWiring` already DISCHARGED the
  LOCAL, base-point-`0`, near-diagonal part (`residualN0_local_baseKernelW_slice`) and reduced Neumann
  convergence to `hEboundW` alone.  C4c's residue has exactly TWO components:

    (1) FAR-FIELD — the bound off the RNC injectivity ball (`‖v‖` beyond where normal coordinates and
        the `O(r²)` deviation estimates hold);
    (2) OFF-DIAGONAL / ALL BASE POINTS — the genuine two-point kernel `E(τ,p,q)` for `q ≠ 0` (the
        parametrix around EVERY base point, not the fixed `q = 0` diagonal slice).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE LANDS (the REACHABLE part of C4c — all GLOBAL, no ball).

    ▸ `gaussDdim_le_scaled_baseKernelW_two` — ★ THE GLOBAL GAUSSIAN COMPARISON (the far-field enabler):
          `gaussDdim t v ≤ (√2)ⁿ · baseKernelW 2 0 t v 0`   for ALL `v`   (`0 < t`).
      The narrow same-time Gaussian is dominated by the width-2 (doubled-time) base kernel EVERYWHERE
      — no ball.  This is the analytic reason a Gaussian-tail residual is globally width-2-dominated:
      `gaussDdim t / gaussDdim (2t) = 2^{n/2}·exp(−r²/8t) ≤ 2^{n/2}` uniformly in `v`.  Route:
      `gaussDdim_le_gaussDdimWide` (narrow ≤ wide) ∘ `gaussDdimWide_eq_scaled_baseKernelW`.

    ▸ `residual_global_baseKernelW_of_gaussianCofactor` — ★ THE GAUSSIAN-COFACTOR GLOBAL DOMINATION
      (the far-field REDUCED to cofactor boundedness).  If a residual factors as narrow-Gaussian times
      a GLOBALLY bounded cofactor, `∀ v, |R v| ≤ B · gaussDdim t v` (`B ≥ 0`), then it is dominated by
      the width-2 base kernel GLOBALLY — no ball:
          `∀ v, |R v| ≤ (B·(√2)ⁿ) · baseKernelW 2 0 t v 0` .
      This pins the far-field wall (1) to exactly one honest input: the GLOBAL boundedness of the
      parametrix's Gaussian cofactor `Θ^{−1/2}·Σ u_k t^k` — which the RAW parametrix does NOT satisfy
      off the injectivity ball (conjugate points/cut locus: `Θ` vanishes, `u_k` unbounded), and which
      only a CUTOFF-parametrix construction supplies.  The hypothesis is genuine and load-bearing
      (`R ≡ 0` and `R = gaussDdim` satisfy it; the raw parametrix residual does not, globally).

    ▸ `residual_global_baseKernelW_of_near_far` — the NEAR/FAR splice: a near-diagonal ball bound
      (`‖v‖ < ρ`, PROVED) plus a far-field bound (`ρ ≤ ‖v‖`, the wall) assemble to the GLOBAL
      single-base-point bound.  Trivial case-split on `‖v‖ < ρ`, but it precisely names the far-field
      as the SINGLE remaining sub-primitive on the diagonal chart.

    ▸ `residualN0_global_baseKernelW_reduced` — ★ THE F2 REDUCTION (diagonal chart).  For the ACTUAL
      residual `parametrixResidualN 0` there is an EXPLICIT radius `ρ > 0` (from the proved near slice)
      such that the SINGLE far-field input on `ρ ≤ ‖v‖` UPGRADES to the global (all `v`) base-point-`0`
      width-2 bound.  The near part is discharged by `residualN0_local_baseKernelW_slice`; the whole
      base-point-`0` global bound is thereby reduced to ONE far-field sub-primitive.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST VERDICT (binding).

  • REACHABLE (LANDED here): the global Gaussian comparison, the Gaussian-cofactor global domination,
    and the near/far reduction of the base-point-`0` bound to the single far-field sub-primitive.
    These shrink C4c: on the diagonal chart, C4c reduces to "the residual is globally
    (narrow-Gaussian × BOUNDED cofactor)".

  • NOT reachable as a loop-brick (the genuine walls, stated precisely, NOT papered over):
      (1) FAR-FIELD.  The parametrix formula `gaussDdim · Θ^{−1/2}·Σ u_k t^k` IS globally defined, but
          its geometric cofactor is NOT globally bounded (conjugate points/cut locus off the
          injectivity ball).  Supplying the hypothesis of `residual_global_baseKernelW_of_gaussianCofactor`
          therefore requires a genuine CUTOFF-parametrix construction `H̃ = χ·H` (`χ` smooth,
          `χ ≡ 1` near `0`, supported in the injectivity ball), re-deriving the residual identity for
          `H̃` and bounding the cutoff-derivative terms `∇χ·∇H`, `Δχ·H` on an annulus bounded away
          from `0` (where `gaussDdim ∼ exp(−c/t)` IS a Gaussian tail).  The analytic heart is
          elementary, but the construction needs Riemannian distance, injectivity radius, smooth
          cutoffs, and the `Δ_g(χH)` product rule — NONE in Mathlib.  A sustained, community-scale
          build, not a single brick.
      (2) OFF-DIAGONAL / ALL BASE POINTS `q ≠ 0`.  Everything here (and in the whole residual chain)
          is the fixed base point `0`: `parametrixResidualN 0`, single RNC coordinate `v = p − 0`.
          The genuine two-point `E(τ,p,q)` for `q ≠ 0` is the parametrix around EVERY base point,
          requiring normal-coordinate recentering infrastructure + uniform-in-`q` constants.  The
          COEFFICIENT-determination half already generalizes to a FREE base point `p` (the (b)-side
          `VanVleckRicciUnconditional.vanVleck_ricci_unconditional` carries `(p v : Point n)` free),
          so the off-diagonal residue is NOT the coefficient ODE but the recentering / two-point-`E`
          construction + uniform constants — a separate community-scale build.

  So C4c is NOT reducible to a SINGLE far-field primitive: it splits into the far-field cutoff (1) AND
  the off-diagonal/all-base-point two-point construction (2).  On the fixed diagonal chart (`q = 0`)
  it DOES reduce to the single far-field sub-primitive (this file, `..._reduced`), which in turn
  reduces to global Gaussian-cofactor boundedness (`..._of_gaussianCofactor`) — the cutoff.

  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.  Grounded in Rosenberg,
  *The Laplacian on a Riemannian Manifold*, §3.2, and the Grigor'yan Gaussian-tail program.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring
import QIQTH.ParametrixResidualN0Bound
import QIQTH.GaussianWidthTolerant

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. ★ The global Gaussian comparison — the far-field enabler (no ball). -/

/-- **★ THE GLOBAL GAUSSIAN COMPARISON.**  The narrow same-time Gaussian is dominated by the width-2
    (doubled-time) base kernel EVERYWHERE — no ball restriction:
        `gaussDdim t v ≤ (√2)ⁿ · baseKernelW 2 0 t v 0`   (`0 < t`, all `v`).
    This is the analytic reason a Gaussian-tail residual is globally width-2-dominated: the ratio
    `gaussDdim t v / gaussDdim (2t) v = 2^{n/2}·exp(−r²/8t) ≤ 2^{n/2}` is bounded uniformly in `v`.
    Route: `gaussDdim_le_gaussDdimWide` (narrow ≤ wide) then `gaussDdimWide_eq_scaled_baseKernelW`
    (`gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`). -/
theorem gaussDdim_le_scaled_baseKernelW_two {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdim t v ≤ Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  calc gaussDdim t v ≤ gaussDdimWide t v := gaussDdim_le_gaussDdimWide ht v
    _ = Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := gaussDdimWide_eq_scaled_baseKernelW ht v

/-! ### 2. ★ The Gaussian-cofactor global domination — far-field reduced to cofactor boundedness. -/

/-- **★ THE GAUSSIAN-COFACTOR GLOBAL DOMINATION.**  If a residual factors as the narrow Gaussian times
    a GLOBALLY bounded cofactor — `∀ v, |R v| ≤ B · gaussDdim t v` with `B ≥ 0` — then it is dominated
    by the width-2 base kernel GLOBALLY, with NO ball:
        `∀ v, |R v| ≤ (B · (√2)ⁿ) · baseKernelW 2 0 t v 0` .
    This pins the far-field wall to ONE honest input: the GLOBAL boundedness of the parametrix's
    Gaussian cofactor `Θ^{−1/2}·Σ u_k t^k`.  The RAW parametrix residual does NOT satisfy the
    hypothesis off the injectivity ball (conjugate points/cut locus make `Θ^{−1/2}` singular and `u_k`
    unbounded) — only a CUTOFF-parametrix construction supplies it.  The hypothesis is genuine and
    load-bearing (satisfied by `R ≡ 0` and `R = gaussDdim`; failed by the raw residual globally),
    never vacuous.  Route: apply the global Gaussian comparison `gaussDdim_le_scaled_baseKernelW_two`
    inside the bound. -/
theorem residual_global_baseKernelW_of_gaussianCofactor {R : Point n → ℝ} {t B : ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hbd : ∀ v, |R v| ≤ B * gaussDdim t v) :
    ∀ v : Point n, |R v| ≤ (B * Real.sqrt 2 ^ n) * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  intro v
  calc |R v| ≤ B * gaussDdim t v := hbd v
    _ ≤ B * (Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0) :=
          mul_le_mul_of_nonneg_left (gaussDdim_le_scaled_baseKernelW_two ht v) hB
    _ = (B * Real.sqrt 2 ^ n) * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by ring

/-! ### 3. The near/far splice — isolating the far-field as the single sub-primitive. -/

/-- **THE NEAR/FAR SPLICE.**  A near-diagonal ball bound (`‖v‖ < ρ`) plus a far-field bound
    (`ρ ≤ ‖v‖`) — with the SAME constant `C` and dominating kernel — assemble to the GLOBAL bound:
        `∀ v, |R v| ≤ C · baseKernelW 2 0 t v 0` .
    A trivial case-split on `‖v‖ < ρ`, but it precisely names the far-field as the SINGLE remaining
    sub-primitive once the near part (here `residualN0_local_baseKernelW_slice`) is proved. -/
theorem residual_global_baseKernelW_of_near_far {R : Point n → ℝ} {t C ρ : ℝ}
    (hnear : ∀ v : Point n, ‖v‖ < ρ → |R v| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) t v 0)
    (hfar : ∀ v : Point n, ρ ≤ ‖v‖ → |R v| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) t v 0) :
    ∀ v : Point n, |R v| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  intro v
  rcases lt_or_ge ‖v‖ ρ with h | h
  · exact hnear v h
  · exact hfar v h

/-! ### 4. ★ The F2 reduction on the diagonal chart — far-field is the single remaining input. -/

/-- **★ THE F2 REDUCTION (base-point-`0` chart).**  For the ACTUAL parametrix residual
    `parametrixResidualN 0` there is an EXPLICIT radius `ρ > 0` (from the PROVED near-diagonal slice)
    such that the SINGLE far-field input on `ρ ≤ ‖v‖` upgrades to the GLOBAL (all `v`) base-point-`0`
    width-2 bound `|parametrixResidualN 0 …| ≤ C' · baseKernelW 2 0 t v 0`, with
    `C' = (1 + 32·n²·M·W + L)·(√2)ⁿ`.  The near part is discharged by
    `residualN0_local_baseKernelW_slice`; the whole base-point-`0` global bound is reduced to the ONE
    far-field sub-primitive.  All curvature/RNC/coefficient hypotheses are inherited verbatim —
    genuine, load-bearing, none vacuous.  This is the diagonal-chart half of C4c; the off-diagonal /
    all-base-point `q ≠ 0` two-point residue is the separate wall (see file header).  NOT the global
    `hEboundW`, NOT `a₁ = R/6`. -/
theorem residualN0_global_baseKernelW_reduced
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hCd : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ((∀ v : Point n, ρ ≤ ‖v‖ →
          |parametrixResidualN 0 g gi Θ u t v|
            ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n)
                * baseKernelW (2 : ℝ) (0 : ℝ) t v 0)
        → ∀ v : Point n,
          |parametrixResidualN 0 g gi Θ u t v|
            ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n)
                * baseKernelW (2 : ℝ) (0 : ℝ) t v 0) := by
  obtain ⟨ρ, hρ, hnear⟩ :=
    residualN0_local_baseKernelW_slice g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv
      hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap
  exact ⟨ρ, hρ, fun hfar => residual_global_baseKernelW_of_near_far hnear hfar⟩

end QIQTH.HeatResidualBound
