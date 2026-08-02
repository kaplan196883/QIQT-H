/-
  HeatConvDeriv — J4-115: the `hDConv` ASSEMBLY (D5 of the hDuhamel campaign).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  The restricted `a₁ = R/6` capstone still carries the regularity conjunct
      `hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t`,
  the `t`-differentiability of the space-time Duhamel convolution at the moving diagonal.  This file
  builds the ASSEMBLY that reduces it to a single, precisely-stated singular carry — the delta-family
  limit — while banking everything else.

  ROUTE VERDICT (ε-truncation, NOT ℝ-convolution).  Two routes were assessed (and the ℝ-convolution
  route consulted externally):

    (A) ℝ-CONVOLUTION.  Under the vanishing facts `A(τ≤0)=0`, `B(s≤0)=0` the interval integral
        `∫ s in 0..u` extends to the full line (this file's `heatConv_eq_integral_full`, V1).  BUT the
        resulting object is NOT a Mathlib `f ⋆ g` convolution: after the inner `z`-integral the
        integrand is a time-dependent pairing `s ↦ ∫ z, A(u−s) x z · B s z y`, which Mathlib's
        convolution API cannot see as a bilinear `f(u−s)·g(s)` without Banach-valued slices and a
        continuous `L²`-type pairing.  Worse, `∂_τ A ~ τ^{-n/2-1}` is NOT integrable-dominated near
        `τ = 0`, so differentiating the full-line integral still hits the endpoint singularity.  NOT
        cheaper in Lean; the boundary/delta issue is not removed.  (V1 kept as a standalone bridge.)

    (B) ε-TRUNCATION (adopted).  `C_ε(u) := heatConvFrozen A B u (u−ε) x y = ∫ s in 0..(u−ε), …`
        keeps every inner time `u−s ≥ ε > 0`, away from the singularity, so `C_ε` is CLEANLY
        differentiable (`heatConv_eps_hasDerivAt` / `heatConv_eps_differentiable`, from the engine's
        joint two-variable derivative composed with the diagonal shift `v ↦ (v, v−ε)`).  Then
        `heatConv = lim_{ε→0} C_ε` with the derivatives `C_ε'` converging LOCALLY UNIFORMLY near `t`;
        `hasDerivAt_of_tendstoLocallyUniformlyOn` upgrades that to `HasDerivAt` of the limit WITHOUT
        needing the derivative's VALUE — so the delta-family limit is never evaluated, only its
        locally-uniform convergence is used.  That convergence IS the sole singular carry
        (`hDConv_of_deltaFamily`, conditional on `hDelta`).

  WHAT LANDS (the green prefix).
    (V1)  `heatConv_eq_integral_full` — the vanishing-extension bridge: `heatConv A B u x y`
          equals the full-line Bochner integral `∫ s, ∫ z, A(u−s) x z · B s z y` when `0 ≤ u`,
          `A(τ≤0)=0`, `B(s≤0)=0`.  UNCONDITIONAL.
    (V2a) `heatConvFrozen_upper_differentiableAt` — pure upper-limit `t`-differentiability of the
          frozen convolution (from the engine's FTC C2 payoff).  Genuine engine hypotheses.
    (V2b) `heatConvFrozen_under_differentiableAt` — pure under-integral `t`-differentiability at a
          frozen upper limit `b` (from the engine's ε-truncated Leibniz C3ε).  Genuine engine hyps.
    (V2c) `heatConvFrozen_diagShift_hasDerivAt` — the chain-rule bridge: a JOINT two-variable
          `HasFDerivAt` at `(u, u−ε)` composed with `v ↦ (v, v−ε)` yields the diagonal-shift
          `HasDerivAt`.  UNCONDITIONAL.
    (V2d) `heatConv_eps_hasDerivAt` / `heatConv_eps_differentiable` — differentiability of the
          ε-truncated convolution `C_ε`, from the carried joint two-variable derivative (the regular,
          away-from-singularity 2-D Leibniz — a genuine input, NOT the conclusion).

  THE PAYOFF (conditional).
    `hDConv_of_deltaFamily` — `DifferentiableAt ℝ (fun u => heatConv A B u x y) t`, GIVEN a family of
    approximants `C_m` with derivatives `DC_m`, and the SINGLE singular carry
        `hDelta : TendstoLocallyUniformlyOn DC D atTop U`   (delta-family: derivatives converge
        locally uniformly near `t`),
    plus the regular calculus (eventual `HasDerivAt` of the `C_m`, dischargeable by V2d) and the
    tail-convergence `C_m → heatConv`.  Via `hasDerivAt_of_tendstoLocallyUniformlyOn`.

  ⚠ HONEST FIREWALL.  This is the ABSTRACT assembly, parametric in `A B`.  It does NOT discharge
  `hDConv` for the concrete `H` / `leviSeries (heatOp g gi H)` — that needs (i) the concrete joint
  2-D `HasFDerivAt` for the gated van-Vleck parametrix (the Gaussian domination of `∂_τ H` away from
  the diagonal), and (ii) the concrete delta-family limit `hDelta` (the Lemma-3.14 brick).  Both are
  separately-labeled bricks.  NO `sorry`, no new axioms, no `expRho` in statements, no vacuous
  hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatConvRegularity

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### V1. The vanishing-extension bridge (interval → full line). -/

/-- **(V1) THE VANISHING-EXTENSION BRIDGE.**  When the left kernel vanishes at nonpositive time
    (`A(τ≤0)=0`, killing `s > u`), the right kernel vanishes at nonpositive time (`B(s≤0)=0`, killing
    `s < 0`), and `0 ≤ u`, the `intervalIntegral` `∫ s in 0..u` extends to the full-line Bochner
    integral:
        `heatConv A B u x y = ∫ s, (∫ z, A(u−s) x z · B s z y)`.
    Proof: `intervalIntegral.integral_of_le` rewrites `∫ s in 0..u` to `∫ s in Ioc 0 u`; the inner
    `s`-integrand vanishes off `Ioc 0 u` (for `s ≤ 0` via `B`, for `u < s` via `A(u−s)` at negative
    time), so `setIntegral_eq_integral_of_forall_compl_eq_zero` extends the domain to all of `ℝ`.
    This is the honest content behind the (rejected) ℝ-convolution route; kept as a standalone bridge.
    UNCONDITIONAL. -/
theorem heatConv_eq_integral_full (A B : ℝ → Point n → Point n → ℝ) (u : ℝ) (x y : Point n)
    (hu : 0 ≤ u)
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q, A τ p q = 0)
    (hBzero : ∀ s, s ≤ 0 → ∀ p q, B s p q = 0) :
    heatConv A B u x y = ∫ s, (∫ z, A (u - s) x z * B s z y) := by
  unfold heatConv
  rw [intervalIntegral.integral_of_le hu]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => ?_)
  have hz : ∀ z, A (u - s) x z * B s z y = 0 := by
    intro z
    by_cases hs0 : s ≤ 0
    · rw [hBzero s hs0 z y, mul_zero]
    · push_neg at hs0
      have hle : ¬ s ≤ u := fun hle => hs (Set.mem_Ioc.mpr ⟨hs0, hle⟩)
      push_neg at hle
      rw [hAzero (u - s) (by linarith) x z, zero_mul]
  simp only [hz, MeasureTheory.integral_zero]

/-! ### V2a / V2b. The two partial differentiabilities of the frozen convolution (from the engine). -/

/-- **(V2a) PURE UPPER-LIMIT `t`-DIFFERENTIABILITY.**  With the outer `t` inside `A` FROZEN at `τ₀`,
    the frozen convolution `u ↦ heatConvFrozen A B τ₀ u x y` is `DifferentiableAt` `t`.  Directly the
    `.differentiableAt` of the engine's FTC C2 payoff `heatConvFrozen_hasDerivAt_upper_of_dominated`.
    Carries exactly that lemma's genuine domination/continuity inputs. -/
theorem heatConvFrozen_upper_differentiableAt (A B : ℝ → Point n → Point n → ℝ)
    (τ₀ t : ℝ) (x y : Point n)
    (bound : Point n → ℝ) (hbound : Integrable bound volume)
    (hmeas : ∀ s, AEStronglyMeasurable (fun z => A (τ₀ - s) x z * B s z y) volume)
    (hle : ∀ s, ∀ᵐ z ∂volume, ‖A (τ₀ - s) x z * B s z y‖ ≤ bound z)
    (hcont : ∀ᵐ z ∂volume, Continuous (fun s => A (τ₀ - s) x z * B s z y)) :
    DifferentiableAt ℝ (fun u => heatConvFrozen A B τ₀ u x y) t :=
  (heatConvFrozen_hasDerivAt_upper_of_dominated A B τ₀ t x y bound hbound hmeas hle hcont).differentiableAt

/-- **(V2b) PURE UNDER-INTEGRAL `t`-DIFFERENTIABILITY (frozen upper limit).**  With the outer upper
    limit FROZEN at `b` (the ε-truncation keeping inner times `u−s ≥ t−b > 0` away from the
    singularity), `u ↦ ∫ s in 0..b, ∫ z, A(u−s) x z · B s z y` is `DifferentiableAt` `τ₀`.  The
    `.differentiableAt` of the engine's ε-truncated Leibniz `heatConv_hasDerivAt_underIntegral`. -/
theorem heatConvFrozen_under_differentiableAt (A dAu B : ℝ → Point n → Point n → ℝ)
    (τ₀ b : ℝ) (x y : Point n) (nb : Set ℝ) (hnb : nb ∈ 𝓝 τ₀)
    (hFmeas : ∀ u, AEStronglyMeasurable
      (fun s => ∫ z, A (u - s) x z * B s z y) (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable (fun s => ∫ z, A (τ₀ - s) x z * B s z y) volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dAu (τ₀ - s) x z * B s z y) (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ u ∈ nb,
      ‖∫ z, dAu (u - s) x z * B s z y‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ u ∈ nb,
      HasDerivAt (fun u => ∫ z, A (u - s) x z * B s z y)
        (∫ z, dAu (u - s) x z * B s z y) u) :
    DifferentiableAt ℝ (fun u => ∫ s in (0)..b, ∫ z, A (u - s) x z * B s z y) τ₀ :=
  (heatConv_hasDerivAt_underIntegral A dAu B τ₀ b x y nb hnb hFmeas hFint hF'meas
    bound hbdd hbound hdiff).differentiableAt

/-! ### V2c / V2d. The ε-truncated convolution `C_ε` and its diagonal differentiability. -/

/-- **(V2c) THE DIAGONAL-SHIFT CHAIN RULE.**  A JOINT two-variable Fréchet derivative of the frozen
    convolution at the shifted diagonal point `(u, u−ε)` transfers, via composition with the smooth
    diagonal shift `v ↦ (v, v−ε)` (derivative `(1,1)`), to the one-variable `HasDerivAt` of the
    ε-truncated convolution `C_ε(v) := heatConvFrozen A B v (v−ε) x y`, with derivative `L (1,1)`.
    Pure `HasFDerivAt.comp_hasDerivAt`.  UNCONDITIONAL. -/
theorem heatConvFrozen_diagShift_hasDerivAt (A B : ℝ → Point n → Point n → ℝ)
    (x y : Point n) (u ε : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hG : HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 x y) L (u, u - ε)) :
    HasDerivAt (fun v => heatConvFrozen A B v (v - ε) x y) (L (1, 1)) u := by
  have hmap : HasDerivAt (fun v : ℝ => (v, v - ε)) ((1 : ℝ), (1 : ℝ)) u :=
    (hasDerivAt_id' u).prodMk ((hasDerivAt_id' u).sub_const ε)
  have hcomp := hG.comp_hasDerivAt u hmap
  simpa [Function.comp] using hcomp

/-- **(V2d, `HasDerivAt`) DIFFERENTIABILITY OF THE ε-TRUNCATED CONVOLUTION.**  From the carried joint
    two-variable `HasFDerivAt` at `(u, u−ε)`, the ε-truncated convolution `C_ε(v) := heatConvFrozen A
    B v (v−ε) x y` has derivative `L (1,1)` at `u`.  (Re-export of V2c.)  The joint `HasFDerivAt` is
    the regular, away-from-singularity 2-D Leibniz (`ε > 0`); genuine input, NOT the conclusion. -/
theorem heatConv_eps_hasDerivAt (A B : ℝ → Point n → Point n → ℝ)
    (x y : Point n) (u ε : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hG : HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 x y) L (u, u - ε)) :
    HasDerivAt (fun v => heatConvFrozen A B v (v - ε) x y) (L (1, 1)) u :=
  heatConvFrozen_diagShift_hasDerivAt A B x y u ε L hG

/-- **(V2d, `DifferentiableAt`) DIFFERENTIABILITY OF THE ε-TRUNCATED CONVOLUTION.**  The
    `.differentiableAt` of `heatConv_eps_hasDerivAt`: `C_ε` is `DifferentiableAt u`, given the joint
    two-variable derivative at `(u, u−ε)`.  This is the "`C_ε` piece" — bankable modulo the genuine
    2-D Leibniz carry.  Discharges the eventual-`HasDerivAt` regular calculus feeding the payoff. -/
theorem heatConv_eps_differentiable (A B : ℝ → Point n → Point n → ℝ)
    (x y : Point n) (u ε : ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hG : HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 x y) L (u, u - ε)) :
    DifferentiableAt ℝ (fun v => heatConvFrozen A B v (v - ε) x y) u :=
  (heatConv_eps_hasDerivAt A B x y u ε L hG).differentiableAt

/-! ### The payoff — `hDConv` conditional on the delta-family limit. -/

/-- **★ J4-115 — `hDConv` FROM THE DELTA-FAMILY LIMIT.**  The `t`-differentiability of the diagonal
    Duhamel convolution, reduced to a SINGLE singular carry.  Given:

    * an open neighborhood `U ∋ t`;
    * a family of approximants `C_m` (e.g. the ε-truncations `C_{1/(m+1)}`) with candidate derivatives
      `DC_m`, EVENTUALLY differentiable on `U` (`hf` — the regular, away-from-singularity calculus,
      dischargeable by `heatConv_eps_hasDerivAt`);
    * tail convergence `C_m → heatConv A B ·` pointwise on `U` (`hfg`);
    * **the delta-family limit** `hDelta : TendstoLocallyUniformlyOn DC D atTop U` — the derivatives
      converge LOCALLY UNIFORMLY near `t` (this is where the `A(0⁺)=δ` boundary term lives; the
      assembly never evaluates it, only uses its locally-uniform convergence),

    the diagonal convolution `u ↦ heatConv A B u x y` is `DifferentiableAt t`.  Via
    `hasDerivAt_of_tendstoLocallyUniformlyOn`: the limit of the (locally-uniformly convergent)
    derivatives IS a derivative of the limit function — so only DIFFERENTIABILITY (existence), not the
    derivative's value, is produced, and the delta-family limit is never identified explicitly.

    ⚠ CONDITIONAL on `hDelta` (and the regular carries `hf`, `hfg`).  `hDelta` is genuinely
    non-vacuous (it fails without the Gaussian domination controlling `C_m'` uniformly) and is NOT the
    conclusion in disguise (it speaks only of the explicit regularized derivatives, on a whole
    neighborhood, with an existential limit whose value is irrelevant).  NOT `a₁ = R/6`. -/
theorem hDConv_of_deltaFamily (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (t : ℝ)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (C DC : ℕ → ℝ → ℝ) (D : ℝ → ℝ)
    (hf : ∀ᶠ m in Filter.atTop, ∀ u ∈ U, HasDerivAt (C m) (DC m u) u)
    (hfg : ∀ u ∈ U, Filter.Tendsto (fun m => C m u) Filter.atTop (𝓝 (heatConv A B u x y)))
    (hDelta : TendstoLocallyUniformlyOn DC D Filter.atTop U) :
    DifferentiableAt ℝ (fun u => heatConv A B u x y) t :=
  (hasDerivAt_of_tendstoLocallyUniformlyOn hUopen hDelta hf hfg htU).differentiableAt

/-! ### Campaign map — from this assembly to the concrete `hDConv`.

    This file lands the ABSTRACT `hDConv` assembly.  The remaining bricks to the concrete capstone
    carry, in dependency order:

    ▸ (D5-concrete-1)  the JOINT 2-D `HasFDerivAt` of `fun p => heatConvFrozen H (leviSeries E) p.1
      p.2 0 0` at `(u, u−ε)` for the gated van-Vleck `H`, `E = heatOp g gi H`.  Away from the diagonal
      (`ε > 0`), this is dominated 2-D Leibniz — the engine's `heatConvInner_hasDerivAt` (τ) plus the
      FTC (upper limit) glued by a joint continuous-partials argument, fed the Gaussian domination of
      `∂_τ H` / `∂_τ (leviSeries E)`.  Discharges `hG` of `heatConv_eps_hasDerivAt`, hence `hf`.

    ▸ (D5-concrete-2)  the tail convergence `hfg`: `C_{1/(m+1)} → heatConv H (leviSeries E)`
      pointwise, from interval-integrability + shrinking-tail (`ε → 0`) dominated convergence.

    ▸ (D5-concrete-3 = Lemma 3.14)  the DELTA-FAMILY LIMIT `hDelta`: the ε-truncated derivatives
      converge locally uniformly near `t`, i.e. the boundary term `∫ z, H(ε) leviSeries E(u−ε)`
      converges (to the delta-family evaluation) locally uniformly.  This is the sole irreducible
      singular analytic input; it is the same content the classical parametrix proof supplies via the
      heat-semigroup delta initial condition.

    None of D5-concrete-1..3 is attempted here; each is a genuine, separately-labeled brick. -/

end QIQTH.HeatResidualBound
