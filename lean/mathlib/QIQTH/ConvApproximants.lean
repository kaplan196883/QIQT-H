/-
  ConvApproximants — J4-116: the CONCRETE APPROXIMANTS `C_m / DC_m / ε_m` for the diagonal Duhamel
  convolution `hDConv` (D5-concrete-1+2 of the hDuhamel campaign).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `HeatConvDeriv.hDConv_of_deltaFamily` reduces
      `hDConv : DifferentiableAt ℝ (fun u => heatConv A B u x y) t`
  to an ABSTRACT delta-family (`C DC : ℕ → ℝ → ℝ`, `D : ℝ → ℝ`) with three carries `hf`, `hfg`,
  `hDelta`.  This file supplies the CONCRETE choice of that family — the ε-truncations with
  `ε_m := 1/(m+1)` — and DISCHARGES two of the three carries with genuine, non-vacuous inputs, leaving
  ONLY the delta-family local-uniform limit `hDelta` (the Lemma-3.14 brick) plus the two singular
  carries the deferred-joint-`q` architecture already runs on.

  WHAT LANDS.
    (A1)  `epsSeq m := 1/(m+1)` with `epsSeq_pos`, `epsSeq_tendsto` (→ 0).  The concrete ε-sequence
          the truncations `C_m u := heatConvFrozen A B u (u − ε_m) x y` are built on.
    (A2)  `heatConv_tail_tendsto` — the TAIL CONVERGENCE `hfg`:  `C_m u → heatConv A B u x y` for
          `u > 0`, from the SINGLE genuine carry that the inner `s`-integrand
          `s ↦ ∫ z, A(u−s) x z · B s z y` is interval-integrable on `[0,u]` (the C1-type carry,
          dischargeable from the Gaussian dominations via the semigroup identity `gaussDdim_conv`).
          Route: the primitive `a ↦ ∫ s in 0..a, (inner s)` is `ContinuousOn [0,u]`
          (`continuousOn_primitive_interval'`); `u − ε_m → u` from within `[0,u]` (eventually, since
          `ε_m ↓ 0`, `u > 0`); compose.  The `(u−s)^{−n/2}` endpoint singularity of `A` is CONTROLLED
          under the `z`-integral by the Chapman–Kolmogorov semigroup identity (`∫_z G(u−s)·G(s) =
          G(u)`, `QIQTH.GaussianConvolution.gaussDdim_conv`), which is exactly what makes the inner
          integrand bounded-near-endpoint, hence interval-integrable — the honest content behind the
          carried hypothesis.  UNCONDITIONAL modulo that one carry.
    (A4)  `hDConv_of_delta_epsFamily` — the PAYOFF for the concrete ε-family: `hDConv` conditional
          ONLY on (i) the interval-integrability carry `hFII` (C1), (ii) the joint two-variable
          `HasFDerivAt` carry `hJoint` at the shifted diagonals `(u, u−ε_m)` (D5-concrete-1, the
          regular away-from-singularity 2-D Leibniz), and (iii) the delta-family local-uniform limit
          `hDelta` (Lemma 3.14).  Everything else (`hf` via `heatConv_eps_hasDerivAt` V2d, `hfg` via
          A2) is discharged from the landed packages.
    (A4-conc)  `hDConv_gatedWitnessN1_epsFamily` — the same payoff with `A := H_G` the concrete gated
          van-Vleck witness and `B := leviSeries (heatOp g gi H_G)`, exhibiting the actual kernels the
          restricted `a₁=R/6` capstone carries; still conditional on the SAME three carries.

  ⚠ HONEST FIREWALL.  `hFII`, `hJoint`, `hDelta` are the three genuine singular/regularity carries of
  the diagonal Leibniz rule; each fails without its content and none is the conclusion.  This file
  does NOT discharge them for the concrete van-Vleck `H_G` — they are the deferred-joint-`q`
  measurability/derivative package (`hFII`, `hJoint`) and the Lemma-3.14 brick (`hDelta`), consistent
  with the landed architecture.  NO `sorry`, no new axioms, no `expRho` in statements, no vacuous
  hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatConvDeriv
import QIQTH.GatedWitnessPackage

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### A1. The concrete ε-sequence. -/

/-- **(A1) THE CONCRETE ε-SEQUENCE** `ε_m := 1/(m+1)` on which the ε-truncated approximants
    `C_m u := heatConvFrozen A B u (u − ε_m) x y` are built. -/
noncomputable def epsSeq : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)

/-- `ε_m > 0`. -/
theorem epsSeq_pos (m : ℕ) : 0 < epsSeq m := by unfold epsSeq; positivity

/-- `ε_m → 0` (the truncation vanishes). -/
theorem epsSeq_tendsto : Filter.Tendsto epsSeq Filter.atTop (𝓝 0) := by
  unfold epsSeq; exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### A2. The tail convergence `hfg` — the concrete `C_m → heatConv`. -/

/-- **(A2) THE TAIL CONVERGENCE.**  For `u > 0` and a general ε-sequence `ε ↓ 0`, the ε-truncated
    convolution converges to the genuine convolution:
        `heatConvFrozen A B u (u − ε_m) x y  →  heatConv A B u x y`   as `m → ∞`,
    GIVEN only that the inner `s`-integrand `s ↦ ∫ z, A(u−s) x z · B s z y` is interval-integrable on
    `[0,u]` (`hFII`).  The primitive `a ↦ ∫ s in 0..a, (inner s)` is `ContinuousOn [0,u]`
    (`intervalIntegral.continuousOn_primitive_interval'`); since `ε_m > 0`, `ε_m → 0` and `u > 0`,
    the shifted upper limit `u − ε_m` lies in `[0,u]` eventually and converges to `u` from within, so
    the primitive values converge — this is exactly `hfg`.

    The interval-integrability carry is genuine and NON-vacuous: the inner integrand carries the
    `(u−s)^{−n/2}` endpoint singularity of `A`, which is CONTROLLED under the `z`-integral by the
    Chapman–Kolmogorov semigroup identity `∫_z G(u−s)(x−z)·G(s)(z−y) = G(u)(x−y)`
    (`QIQTH.GaussianConvolution.gaussDdim_conv`) — the honest content that makes the carry hold for
    the Gaussian-dominated `H` / `leviSeries E`. -/
theorem heatConv_tail_tendsto (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u : ℝ) (hu : 0 < u)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m) (hε0 : Filter.Tendsto ε Filter.atTop (𝓝 0))
    (hFII : IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 u) :
    Filter.Tendsto (fun m => heatConvFrozen A B u (u - ε m) x y) Filter.atTop
      (𝓝 (heatConv A B u x y)) := by
  -- the primitive `a ↦ ∫ s in 0..a, (inner s)` is continuous on `[0,u]`.
  have hcont : ContinuousOn
      (fun a => ∫ s in (0:ℝ)..a, ∫ z, A (u - s) x z * B s z y) (Set.uIcc 0 u) :=
    intervalIntegral.continuousOn_primitive_interval' (a := 0) hFII Set.left_mem_uIcc
  -- eventually the shifted upper limit lies in `[0,u]`.
  have hev : ∀ᶠ m in Filter.atTop, u - ε m ∈ Set.uIcc 0 u := by
    have h1 : ∀ᶠ m in Filter.atTop, ε m < u := hε0.eventually (eventually_lt_nhds hu)
    filter_upwards [h1] with m hm
    rw [Set.uIcc_of_le hu.le, Set.mem_Icc]
    exact ⟨by linarith [hεpos m], by linarith [hεpos m]⟩
  -- and it converges to `u` from within `[0,u]`.
  have htend : Filter.Tendsto (fun m => u - ε m) Filter.atTop (𝓝[Set.uIcc 0 u] u) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (tendsto_const_nhds (x := u)).sub hε0) hev
  -- continuity within at `u` composed with the shift.
  have hcwa : Filter.Tendsto (fun a => ∫ s in (0:ℝ)..a, ∫ z, A (u - s) x z * B s z y)
      (𝓝[Set.uIcc 0 u] u)
      (𝓝 (∫ s in (0:ℝ)..u, ∫ z, A (u - s) x z * B s z y)) :=
    hcont u Set.right_mem_uIcc
  have hcomp := hcwa.comp htend
  simpa only [Function.comp, heatConvFrozen, heatConv] using hcomp

/-! ### A4. The payoff — `hDConv` from the concrete ε-family. -/

/-- **★ J4-116 (A4) — `hDConv` FROM THE CONCRETE ε-FAMILY.**  The `t`-differentiability of the
    diagonal Duhamel convolution, instantiated on the CONCRETE ε-truncations
    `C_m u := heatConvFrozen A B u (u − ε_m) x y` (`ε_m = 1/(m+1)`).  Given, on an open
    neighborhood `U ∋ t` of positive times:

    * `hFII` — the inner `s`-integrand is interval-integrable on `[0,u]` for each `u ∈ U` (the C1
      carry; discharges `hfg` via `heatConv_tail_tendsto` / A2);
    * `hJoint` — the JOINT two-variable `HasFDerivAt` of `p ↦ heatConvFrozen A B p.1 p.2 x y` at the
      shifted diagonals `(u, u−ε_m)`, eventually in `m`, uniformly for `u ∈ U` (the regular,
      away-from-singularity 2-D Leibniz, D5-concrete-1; discharges `hf` via `heatConv_eps_hasDerivAt`
      / V2d);
    * `hDelta` — the DELTA-FAMILY local-uniform limit of the derivatives `u ↦ L m u (1,1)` on `U`
      (Lemma 3.14; the sole irreducible singular analytic input),

    the diagonal convolution `u ↦ heatConv A B u x y` is `DifferentiableAt t`.  Via
    `hDConv_of_deltaFamily`.  ⚠ CONDITIONAL on `hFII`, `hJoint`, `hDelta` — all genuine, none the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hDConv_of_delta_epsFamily (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (t : ℝ)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U) (hUpos : ∀ u ∈ U, 0 < u)
    (hFII : ∀ u ∈ U, IntervalIntegrable (fun s => ∫ z, A (u - s) x z * B s z y) volume 0 u)
    (L : ℕ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hJoint : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 x y) (L m u) (u, u - epsSeq m))
    (D : ℝ → ℝ)
    (hDelta : TendstoLocallyUniformlyOn (fun m u => L m u (1, 1)) D Filter.atTop U) :
    DifferentiableAt ℝ (fun u => heatConv A B u x y) t := by
  refine hDConv_of_deltaFamily A B x y t U hUopen htU
    (fun m u => heatConvFrozen A B u (u - epsSeq m) x y)
    (fun m u => L m u (1, 1)) D ?_ ?_ hDelta
  · -- `hf`: eventual differentiability of the ε-truncations from the joint 2-D derivative (V2d).
    filter_upwards [hJoint] with m hm
    intro u hu
    exact heatConv_eps_hasDerivAt A B x y u (epsSeq m) (L m u) (hm u hu)
  · -- `hfg`: the tail convergence (A2).
    intro u hu
    exact heatConv_tail_tendsto A B x y u (hUpos u hu) epsSeq epsSeq_pos epsSeq_tendsto (hFII u hu)

/-! ### A4-conc. The concrete van-Vleck gated witness `H_G`. -/

/-- **THE CONCRETE `N = 1` GATED VAN-VLECK WITNESS `H_G`** — the actual left kernel `H` the restricted
    `a₁=R/6` capstone carries: the gate-`S`-restricted, radially-cut-off order-1 van-Vleck parametrix
    in the uniform inverse chart.  Named so the concrete `hDConv` corollary reads cleanly. -/
noncomputable def vanVleckGatedWitness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    ℝ → Point n → Point n → ℝ :=
  gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))

/-- **★★ J4-116 (A4-conc) — `hDConv` FOR THE CONCRETE VAN-VLECK `H_G`.**  The `t`-differentiability of
    the diagonal Duhamel convolution `u ↦ heatConv H_G (leviSeries (heatOp g gi H_G)) u 0 0` — the
    EXACT `hDConv` carry of `trueKernel_diagonal_a1_eq_R6_residual_restricted` — with `H_G` the concrete
    gated van-Vleck witness (`vanVleckGatedWitness`) and `B = leviSeries (heatOp g gi H_G)`.  A direct
    specialization of `hDConv_of_delta_epsFamily` at `A := H_G`, `B := leviSeries (heatOp g gi H_G)`,
    `x = y = 0`.  Conditional on the SAME three genuine carries — interval-integrability `hFII` (C1),
    the joint 2-D `HasFDerivAt` `hJoint` (D5-concrete-1), and the delta-family limit `hDelta`
    (Lemma 3.14).  NOT `a₁ = R/6`. -/
theorem hDConv_gatedWitnessN1_epsFamily (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U) (hUpos : ∀ u ∈ U, 0 < u)
    (hFII : ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u)
    (L : ℕ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hJoint : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) p.1 p.2 0 0)
          (L m u) (u, u - epsSeq m))
    (D : ℝ → ℝ)
    (hDelta : TendstoLocallyUniformlyOn (fun m u => L m u (1, 1)) D Filter.atTop U) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u 0 0) t :=
  hDConv_of_delta_epsFamily (vanVleckGatedWitness g gi hC hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) 0 0 t U hUopen htU hUpos
    hFII L hJoint D hDelta

end QIQTH.HeatResidualBound
