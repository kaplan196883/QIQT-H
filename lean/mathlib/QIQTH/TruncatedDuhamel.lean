/-
  TruncatedDuhamel — J4-122: the ε-TRUNCATED DUHAMEL SKELETON (the finite-ε identity chain that
  reduces the capstone's `hDuhamel` input to the single hard `hDaLim` carry).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  The restricted `a₁ = R/6` capstone
  (`ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`, and its parents) still
  carries the Duhamel-principle output as an EXPLICIT hypothesis:
      `hDuhamel : heatOp g gi (fun u p q => heatConv H F u p q) t 0 0
                     = F t 0 0 + heatConv (heatOp g gi H) F t 0 0`   (with `F = leviSeries (heatOp g gi H)`).
  This file builds the ε-truncation skeleton that REDUCES `hDuhamel` to a single limit carry — the
  `Da`-limit `hDaLim` (whose target is a SPECIFIC laplaceBeltrami + Levi-convolution value) — plus the
  already-discharged boundary limit (`BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`) and the
  `hDConv` derivative-of-the-limit machinery.

  ROUTE (Sol plan bricks 2.1–2.4 + the reduction capstone).  With `E := heatOp g gi H`, freeze the
  upper limit at `u − ε_m` (`ε_m := epsSeq m = 1/(m+1)`, keeping all inner times `≥ ε_m > 0`, away
  from the `s = t` singularity), so the truncated convolution
      `heatConvFrozen H F v (v − ε_m) 0 0 = ∫ s in 0..(v−ε_m), ∫ z, H(v−s) 0 z · F s z 0`
  is CLEANLY differentiable.  Its `v`-derivative splits (2.4) into the `τ₀`-slot Leibniz `Da` (2.1)
  plus the FTC boundary term (`BoundaryTrunc`); the `Da`-slot integrand `∂_r H` decomposes (2.3) as
  `Δ_g H + E` (the definition of `heatOp`), giving `Da = LapTrunc + Etrunc`.  Hence the truncated
  `heatOp` equals `BoundaryTrunc + Etrunc`.  Taking `m → ∞`: `BoundaryTrunc → F` (the delta initial
  condition, J4-120), `Da → Δ_g(H*F) + E*F` (`hDaLim`), and the derivative of the true convolution is
  the limit of the truncated derivatives (`hDConv`), so `heatOp(H*F) = F + E*F`.

  WHAT LANDS (this file).
    • defs `DaTrunc`, `BoundaryTrunc`, `Etrunc`, `LapTrunc` — the ε-truncated objects (reusing
      `heatConvFrozen`, `heatOp`, `laplaceBeltrami`; boundary term in the `u − (u − ε_m)` form so it
      matches `heatConvFrozen_hasFDerivAt_of_partials` / `BoundaryAssembly` VERBATIM).
    • (Brick 2.1) `hDa_trunc` — the `τ₀`-slot under-integral Leibniz `Da = ∫∫ ∂_r H · F`, REUSING the
      engine `heatConv_hasDerivAt_underIntegral` (C3ε).
    • (Brick 2.3) `hE_combination` — the algebraic split `Da = LapTrunc + Etrunc`, from the pointwise
      `heatOp` identity `∂_r H = Δ_g H + E` and integral linearity (`integral_add`).
    • (Brick 2.4) `truncDuhamel_deriv` — the truncated diagonal derivative `= Da + BoundaryTrunc`
      (REUSING `heatConvFrozen_hasFDerivAt_of_partials` (F2) + `heatConv_eps_hasDerivAt` (V2d)); and
      `heatOp_trunc` — the truncated heat operator `= BoundaryTrunc + Etrunc` (2.4 + 2.3, algebra).
    • ★ (the REDUCTION CAPSTONE) `hDuhamel_of_daLim` — `hDuhamel` from the three limit carries
      (`hDaLim`, `hBoundaryLim`, `hDerivConv`), by `tendsto_nhds_unique` + `ring` (the exact
      Δ-cancellation: the SAME `laplaceBeltrami` expression appears in `hDaLim`'s target and in the
      `heatOp` unfold).
    • `hDuhamel_leviSeries_of_daLim` — the thin corollary with `F := leviSeries (heatOp g gi H)`,
      matching the capstone `hDuhamel` shape VERBATIM.

  ⚠ HONEST FIREWALL.
    LANDED: bricks 2.1, 2.3, 2.4, the reduction capstone, and the Levi corollary — all proven, axiom
      clean (`propext, Classical.choice, Quot.sound`).
    CARRIED (labelled, none the conclusion, none vacuous):
      • Brick 2.1's engine inputs (measurability / integrability / uniform-derivative bound / the
        pointwise `HasDerivAt` family of `∂_r H`) — the C3ε differentiation-under-∫ carries.
      • Brick 2.2 (`hLap` of `hE_combination`) — the **Laplacian ↔ space-time-integral interchange**
        `LapTrunc = ∫∫ Δ_g H · F`.  This is the second-order differentiation-under-the-integral fact;
        it is DEFERRED (carried as the `hLap` hypothesis of `hE_combination`), the riskiest analytic
        brick, exactly as flagged by the plan.  It is a genuine interchange (fails without the spatial
        Gaussian-derivative dominations of `H`), NOT the file's conclusion.
      • Brick 2.3's integrability carries (`hLapZ`/`hEZ`/`hLapS`/`hES`).
      • Brick 2.4's partial-derivative carries (`hpar`/`htime`/`hR`), verbatim the F2 interface of
        `heatConvFrozen_hasFDerivAt_of_partials`.
      • The reduction capstone's three limit carries — `hDaLim` (the sole hard limit; its target is a
        SPECIFIC value), `hBoundaryLim` (PROVEN content: `BoundaryAssembly.boundary_tendstoLocally-
        UniformlyOn` pointwise), `hDerivConv` (the `hDConv` derivative-of-the-limit machinery,
        `HeatConvDeriv.hDConv_of_deltaFamily`).
    NO `sorry`, no new axioms, no `expRho` in statements.  NOT `a₁ = R/6` — this is ONE brick of the
    campaign (the ε-truncated Duhamel skeleton).
-/
import Mathlib
import QIQTH.ConvCarriesDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 0. The ε-truncated objects. -/

/-- **The `τ₀`-slot derivative `Da`** of the ε-truncated Duhamel convolution: with the outer upper
    limit FROZEN at `u − ε_m`, the derivative of `a ↦ heatConvFrozen H F a (u−ε_m) 0 0` at `u`.
    Matches the `Da` shape carried by `ConvCarriesDischarge.hDConv_of_delta_final`'s `hpar`. -/
noncomputable def DaTrunc (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  deriv (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) u

/-- **The FTC boundary term `BoundaryTrunc`** of the ε-truncation
    `∫ z, H(u−(u−ε_m)) 0 z · F(u−ε_m) z 0` (the J4-117/120 boundary term, in the `u−(u−ε_m)` form so
    it matches `heatConvFrozen_hasFDerivAt_of_partials`'s `htime` value and `BoundaryAssembly`
    VERBATIM; note `u − (u − ε_m) = ε_m`). -/
noncomputable def BoundaryTrunc (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  ∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0

/-- **The ε-truncated residual convolution `Etrunc`** `= heatConvFrozen (heatOp g gi H) F u (u−ε_m)
    0 0` — the space-time convolution of the parametrix residual `E = heatOp g gi H` with `F`, with
    the upper limit frozen at `u − ε_m`.  (`heatOp`'s spatial `Δ` acts in the second `Point`-slot;
    here the kernel is evaluated at `x = 0`.) -/
noncomputable def Etrunc (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ)
    (m : ℕ) (u : ℝ) : ℝ :=
  ∫ s in (0)..(u - epsSeq m), ∫ z, heatOp g gi H (u - s) 0 z * F s z 0

/-- **The ε-truncated Laplacian `LapTrunc`** `= Δ_{g,x} (heatConvFrozen H F u (u−ε_m) · 0)` at the
    origin — the spatial Laplace–Beltrami of the truncated convolution. -/
noncomputable def LapTrunc (g gi : Point n → Fin n → Fin n → ℝ) (H F : ℝ → Point n → Point n → ℝ)
    (m : ℕ) (u : ℝ) : ℝ :=
  laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0

/-! ### 1. Brick 2.1 — the `τ₀`-slot under-integral Leibniz `hDa_trunc`. -/

/-- **★ J4-122 (Brick 2.1) — THE `τ₀`-SLOT UNDER-INTEGRAL LEIBNIZ.**  With the outer upper limit
    FROZEN at `u − ε_m`, the `τ₀`-slot derivative `Da` of the truncated convolution passes under both
    integrals:
        `DaTrunc H F m u = ∫ s in 0..(u−ε_m), ∫ z, ∂_r H(u−s) 0 z · F s z 0`.
    Direct `.deriv` of the engine `heatConv_hasDerivAt_underIntegral` (C3ε) with the pointwise
    `∂_r`-kernel `dAu := fun τ p q => deriv (fun r => H r p q) τ`.  All hypotheses are the engine's
    genuine differentiation-under-∫ carries (measurability, base/derivative integrability, a uniform
    integrable derivative bound, and the pointwise `HasDerivAt` family of `∂_r H`); none is the
    conclusion. -/
theorem hDa_trunc (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (nb : Set ℝ) (hnb : nb ∈ 𝓝 u)
    (hFmeas : ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 (u - epsSeq m))
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a) :
    DaTrunc H F m u
      = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0 := by
  have hHD := heatConv_hasDerivAt_underIntegral H
    (fun τ p q => deriv (fun r => H r p q) τ) F u (u - epsSeq m) 0 0 nb hnb
    hFmeas hFint hF'meas bound hbdd hbound hdiff
  unfold DaTrunc
  exact hHD.deriv

/-! ### 2. Brick 2.3 — the E-combination `Da = LapTrunc + Etrunc`. -/

/-- **★ J4-122 (Brick 2.3) — THE E-COMBINATION.**  Given the `Da`-integral form (Brick 2.1, `hDa`)
    and the Laplacian-interchange form (Brick 2.2, `hLap` — the DEFERRED second-order
    differentiation-under-∫), the `τ₀`-slot derivative splits:
        `DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u`.
    Pure algebra: pointwise `∂_r H(u−s) = Δ_g H(u−s) + heatOp g gi H (u−s)` (the DEFINITION of
    `heatOp`), then integral linearity (`integral_add` inner, `intervalIntegral.integral_add` outer).
    Carries the four genuine integrability side conditions (`hLapZ`/`hEZ` in `z`, `hLapS`/`hES` in
    `s`); none is the conclusion. -/
theorem hE_combination (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hDa : DaTrunc H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
    (hLap : LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
    (hLapZ : ∀ s, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ s, Integrable (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m)) :
    DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u := by
  rw [hDa, hLap]
  unfold Etrunc
  have hpt : ∀ s, (∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      = (∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        + (∫ z, heatOp g gi H (u - s) 0 z * F s z 0) := by
    intro s
    rw [← integral_add (hLapZ s) (hEZ s)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    have hdd : deriv (fun r => H r 0 z) (u - s)
        = laplaceBeltrami g gi (fun x => H (u - s) x z) 0 + heatOp g gi H (u - s) 0 z := by
      simp only [heatOp]; ring
    rw [hdd]; ring
  rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
  exact intervalIntegral.integral_add hLapS hES

/-! ### 3. Brick 2.4 — the truncated diagonal derivative and the truncated heat operator. -/

/-- **★ J4-122 (Brick 2.4a) — THE TRUNCATED DIAGONAL DERIVATIVE.**  The `v`-derivative of the
    diagonal ε-truncated convolution splits into the `τ₀`-slot `Da` plus the FTC boundary term:
        `deriv (fun v => heatConvFrozen H F v (v−ε_m) 0 0) u = DaTrunc H F m u + BoundaryTrunc H F m u`.
    Route: `heatConvFrozen_hasFDerivAt_of_partials` (F2) assembles the joint 2-D `HasFDerivAt` at the
    shifted diagonal `(u, u−ε_m)`; `heatConv_eps_hasDerivAt` (V2d) composes with the diagonal shift
    `v ↦ (v, v−ε_m)`, whose derivative `L(1,1)` evaluates to `Da + Boundary`.  Carries the three F2
    partial derivatives (`hpar`/`htime`/`hR`), verbatim the F2 interface; none is the conclusion. -/
theorem truncDuhamel_deriv (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hpar : HasDerivAt (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) (DaTrunc H F m u) u)
    (htime : HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
        (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0) (u - epsSeq m))
    (hR : HasFDerivAt (fun p : ℝ × ℝ =>
        heatConvFrozen H F p.1 p.2 0 0 - heatConvFrozen H F p.1 (u - epsSeq m) 0 0
          - heatConvFrozen H F u p.2 0 0) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m)) :
    deriv (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0) u
      = DaTrunc H F m u + BoundaryTrunc H F m u := by
  have hjoint := heatConvFrozen_hasFDerivAt_of_partials H F 0 0 u (u - epsSeq m)
    (DaTrunc H F m u) hpar htime hR
  have heps := heatConv_eps_hasDerivAt H F 0 0 u (epsSeq m) _ hjoint
  rw [heps.deriv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one,
    BoundaryTrunc]

/-- **★ J4-122 (Brick 2.4b) — THE TRUNCATED HEAT OPERATOR.**  Combining the truncated diagonal
    derivative (`hderiv`, Brick 2.4a) with the E-combination (`hEcomb`, Brick 2.3):
        `heatOp g gi (fun v x y => heatConvFrozen H F v (v−ε_m) x y) u 0 0
           = BoundaryTrunc H F m u + Etrunc g gi H F m u`.
    Pure algebra on `heatOp = ∂_v − Δ_g`: the derivative slot is `Da + Boundary` (2.4a), the `Δ`-slot
    is `LapTrunc`, and `Da − LapTrunc = Etrunc` (2.3). -/
theorem heatOp_trunc (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hderiv : deriv (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0) u
        = DaTrunc H F m u + BoundaryTrunc H F m u)
    (hEcomb : DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u) :
    heatOp g gi (fun v x y => heatConvFrozen H F v (v - epsSeq m) x y) u 0 0
      = BoundaryTrunc H F m u + Etrunc g gi H F m u := by
  show deriv (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0) u
        - laplaceBeltrami g gi (fun p => heatConvFrozen H F u (u - epsSeq m) p 0) 0
      = BoundaryTrunc H F m u + Etrunc g gi H F m u
  rw [hderiv,
    show laplaceBeltrami g gi (fun p => heatConvFrozen H F u (u - epsSeq m) p 0) 0
        = LapTrunc g gi H F m u from rfl,
    hEcomb]
  ring

/-! ### 4. ★ THE REDUCTION CAPSTONE — `hDuhamel` from `hDaLim`. -/

/-- **★★★ J4-122 (THE REDUCTION CAPSTONE) — `hDuhamel` FROM THE `Da`-LIMIT.**  The Duhamel-principle
    output `hDuhamel` of the restricted `a₁ = R/6` capstone,
        `heatOp g gi (fun u p q => heatConv H F u p q) t 0 0 = F t 0 0 + heatConv (heatOp g gi H) F t 0 0`,
    REDUCED to three limit carries:

    * `hDaLim`      — the `Da`-limit: the truncated `τ₀`-slot derivatives converge to the SPECIFIC
      value `Δ_{g,x}(H*F)(t) + (E*F)(t)` (`E = heatOp g gi H`).  This is the sole hard limit; its
      target is a specific `laplaceBeltrami + heatConv` value, stated with the VERBATIM `laplaceBeltrami`
      expression so the `Δ`-cancellation below is exact.
    * `hBoundaryLim`— the boundary limit `BoundaryTrunc → F t 0 0` (PROVEN content — the delta initial
      condition, `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn` specialized pointwise at `t`).
    * `hDerivConv`  — the `hDConv` machinery: the truncated derivatives `Da + Boundary` converge to the
      derivative of the TRUE convolution (`HeatConvDeriv.hDConv_of_deltaFamily`, the
      derivative-of-the-limit = limit-of-derivatives fact); a genuine analytic carry, NOT the
      conclusion.

    Proof: `Da + Boundary → (Δ(H*F) + E*F) + F` by `Tendsto.add`, and `→ deriv(H*F)` by `hDerivConv`;
    `tendsto_nhds_unique` pins `deriv(H*F) t = Δ(H*F)(t) + E*F(t) + F(t)`.  Unfolding
    `heatOp = deriv − Δ` and cancelling the (identical) `Δ` term by `ring` gives the result. -/
theorem hDuhamel_of_daLim (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (hBoundaryLim : Filter.Tendsto (fun m => BoundaryTrunc H F m t) Filter.atTop
        (𝓝 (F t 0 0)))
    (hDaLim : Filter.Tendsto (fun m => DaTrunc H F m t) Filter.atTop
        (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F t x 0) 0
              + heatConv (heatOp g gi H) F t 0 0)))
    (hDerivConv : Filter.Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv H F u 0 0) t))) :
    heatOp g gi (fun u p q => heatConv H F u p q) t 0 0
      = F t 0 0 + heatConv (heatOp g gi H) F t 0 0 := by
  have hlim2 : Filter.Tendsto (fun m => DaTrunc H F m t + BoundaryTrunc H F m t) Filter.atTop
      (𝓝 ((laplaceBeltrami g gi (fun x => heatConv H F t x 0) 0
              + heatConv (heatOp g gi H) F t 0 0) + F t 0 0)) :=
    hDaLim.add hBoundaryLim
  have hderiv_eq : deriv (fun u => heatConv H F u 0 0) t
      = (laplaceBeltrami g gi (fun x => heatConv H F t x 0) 0
              + heatConv (heatOp g gi H) F t 0 0) + F t 0 0 :=
    tendsto_nhds_unique hDerivConv hlim2
  show deriv (fun u => heatConv H F u 0 0) t
        - laplaceBeltrami g gi (fun p => heatConv H F t p 0) 0
      = F t 0 0 + heatConv (heatOp g gi H) F t 0 0
  rw [hderiv_eq]
  ring

/-- **★★★★ J4-122 (LEVI COROLLARY) — the reduction capstone for `F := leviSeries (heatOp g gi H)`.**
    The reduction capstone instantiated at the actual Levi series, matching the `hDuhamel` carry of
    `ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` VERBATIM.  Reduces that
    carry to the three limit inputs `hDaLim`/`hBoundaryLim`/`hDerivConv`.  STILL CONDITIONAL; NOT
    `a₁ = R/6`. -/
theorem hDuhamel_leviSeries_of_daLim (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (hBoundaryLim : Filter.Tendsto
        (fun m => BoundaryTrunc H (leviSeries (heatOp g gi H)) m t) Filter.atTop
        (𝓝 (leviSeries (heatOp g gi H) t 0 0)))
    (hDaLim : Filter.Tendsto
        (fun m => DaTrunc H (leviSeries (heatOp g gi H)) m t) Filter.atTop
        (𝓝 (laplaceBeltrami g gi
                (fun x => heatConv H (leviSeries (heatOp g gi H)) t x 0) 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)))
    (hDerivConv : Filter.Tendsto
        (fun m => DaTrunc H (leviSeries (heatOp g gi H)) m t
          + BoundaryTrunc H (leviSeries (heatOp g gi H)) m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t))) :
    heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
      = leviSeries (heatOp g gi H) t 0 0
        + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 :=
  hDuhamel_of_daLim g gi H (leviSeries (heatOp g gi H)) t hBoundaryLim hDaLim hDerivConv

end QIQTH.HeatResidualBound
