/-
  DaLimLocUnif — J4-148: the LOCALLY-UNIFORM upgrade of the `hDaLim` chain.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `LapTruncAssembly` (J4-139) discharged the `Da`-limit POINTWISE at a fixed `u`
  (`hDaLim_full`: `DaTrunc H F m u → Δ_g(H*F) + E*F`).  But `DuhamelLimitWiring.derivConv_tendsto`
  consumes its `hDerivLU` input in the LOCALLY-UNIFORM shape
      `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u) D atTop U`,
  and `DuhamelLimitWiring.hDuhamel_final` consumes `hDaLimLU` in the loc-unif shape
      `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => Δ_g(H*F) u + E*F u) atTop U`.
  This file UPGRADES the pointwise chain to exactly those loc-unif shapes.  The mathematical content is
  that the sliver / tail estimates carried at each `u` have `u`-FREE constants (the `B(ε_m)`/`Be(ε_m)`
  rates are strip-level, independent of `u`); the WORK here is the filter/compact plumbing that turns a
  `u`-uniform bound on a compact `K` into `TendstoUniformlyOn`, then `TendstoLocallyUniformlyOn` on `U`
  (mirroring the `BoundaryAssembly` compact-reduction pattern).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file).
    (aux)  `tendstoUniformlyOn_of_bound` — the uniform-squeeze workhorse: a `u`-free norm bound
           `‖f u − F m u‖ ≤ b m` on `K` with `b m → 0` gives `TendstoUniformlyOn F f atTop K`
           (`Metric.tendstoUniformlyOn_iff` + eventually `b m < η`).
    (bnd)  `lapTrunc_sub_bound` — the per-`(m,u)` sliver bound extracted from `lapTrunc_tendsto`'s guts:
           `‖Δ_g(H*F) u − LapTrunc … m u‖ ≤ B(ε_m)` (adjacency splitting + `hSliver`).
    (U1)   `etrunc_tendstoUniformlyOn` — the `K`-uniform `Etrunc` limit
           (`Etrunc → heatConv E F · 0 0` uniformly on `K`), from the `u`-uniform tail bound.
    (U2)   `lapTrunc_tendstoUniformlyOn` — the `K`-uniform `LapTrunc` limit
           (`LapTrunc → Δ_g(H*F)` uniformly on `K`), via `lapTrunc_sub_bound` + the squeeze workhorse.
    (U3) ★ `hDaLimLU_discharge` — THE loc-unif `Da`-limit in `hDuhamel_final`'s EXACT `hDaLimLU` shape:
           `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u) (fun u => Δ_g(H*F) u + E*F u) atTop U`.
           Compact-reduce (`tendstoLocallyUniformlyOn_iff_forall_isCompact`, `U` open); on each `K` the
           combined bound `‖(Δ+E) − DaTrunc‖ ≤ B(ε_m)+Be(ε_m)` (triangle, via `hEcomb`) → 0.
    (U4) ★ `hDerivLU_discharge` — THE `hDerivLU` in `derivConv_tendsto`'s EXACT input shape:
           `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u)
             (fun u => (Δ_g(H*F) u + E*F u) + F u 0 0) atTop U`, from U3 + the boundary loc-unif via
           `tendstoLocallyUniformlyOn_add`.

  ⚠ HONEST FIREWALL.
    LANDED (this file): the uniform-squeeze workhorse, the per-`(m,u)` sliver bound, U1, U2, the loc-unif
      `Da`-limit U3, and the `hDerivLU` assembly U4 — each proven, no `sorry`, no new axioms, no `expRho`
      in statements.  U3/U4 are in the VERBATIM shapes consumed by `hDuhamel_final`/`derivConv_tendsto`.
    CARRIED (labelled, none the conclusion, none vacuous):
      • the RNC gauge (`hgi`/`hΓ`) + the interchange family (`hInterchange`/`hLapFull`) + adjacency
        integrabilities (`hII_lo`/`hII_hi`) — the `LapTrunc` sliver-identity inputs, now quantified
        `∀ u ∈ U` (the same facts as the pointwise `lapTrunc_tendsto`, `u`-uniform).
      • the sliver bound `B`/`hSliver` + rate `hBlim` — with `B` `u`-FREE (`hSliver` quantified
        `∀ u ∈ U`, bound `B(ε_m)`); dischargeable from the concrete `√ε` witness bound summed over
        coordinates (strip-level constants).
      • the tail bound `Be`/`hEbnd` + rate `hEblim` — the `u`-uniform `Etrunc` tail estimate
        (`‖E*F − Etrunc‖ ≤ Be(ε_m)`); the `u`-free Gaussian-domination tail, carried in the `u`-uniform
        shape (the pointwise `etrunc_tendsto` gives no explicit rate — this is its uniform strengthening).
      • `hEcomb` — `DaTrunc = LapTrunc + Etrunc` (the E-combination), quantified `∀ m u`.
      • U4's `hbdryLU` — the boundary loc-unif `BoundaryTrunc → F · 0 0`, already PROVEN by
        `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn` (reconciled to the `BoundaryTrunc` shape),
        supplied as a carried input.
    NOT `a₁ = R/6` — this is ONE brick (the loc-unif upgrade of the `hDaLim` chain) of the campaign.
-/
import Mathlib
import QIQTH.LapTruncAssembly
import QIQTH.DeltaFamilyBoundary

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### aux — the uniform-squeeze workhorse.
    ############################################################################### -/

/-- **★ aux — `tendstoUniformlyOn_of_bound`.**  If a `u`-FREE numerical bound
    `‖f u − F m u‖ ≤ b m` holds for all `u ∈ K` with `b m → 0`, the family converges UNIFORMLY on `K`:
        `TendstoUniformlyOn F f atTop K`.
    `Metric.tendstoUniformlyOn_iff` reduces to `∀ η, eventually ∀ u ∈ K, dist < η`; the eventual
    `b m < η` (from `b → 0`) plus `dist (f u) (F m u) = ‖f u − F m u‖ ≤ b m` closes.  This is the
    filter/compact content of the pointwise→uniform upgrade. -/
theorem tendstoUniformlyOn_of_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {K : Set ℝ} (b : ℕ → ℝ)
    (hbnd : ∀ m, ∀ u ∈ K, ‖f u - F m u‖ ≤ b m)
    (hblim : Tendsto b atTop (𝓝 0)) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hblim.eventually (Iio_mem_nhds hη)] with m hbm u hu
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hbnd m u hu) hbm

/-! ###############################################################################
    ### bnd — the per-`(m,u)` `LapTrunc` sliver bound.
    ############################################################################### -/

/-- **★ bnd — `lapTrunc_sub_bound`.**  The per-`(m,u)` sliver bound extracted from `lapTrunc_tendsto`'s
    guts: at an RNC center (`hgi`/`hΓ`), with the finite-gap interchange `hInterchange`, the untruncated
    interchange `hLapFull`, the adjacency integrabilities `hII_lo`/`hII_hi`, and the sliver bound
    `hSliver`,
        `‖Δ_g(H*F) u − LapTrunc g gi H F m u‖ ≤ B (ε_m)`.
    Route: `lapTrunc_eq_sum_pdpd` + `hInterchange` express `LapTrunc` as `∑ᵢ ∫₀^{u−ε_m}`;
    `integral_add_adjacent_intervals` peels the sliver so the difference IS exactly `∑ᵢ` the sliver;
    `hSliver` bounds it.  NOT `a₁ = R/6`. -/
theorem lapTrunc_sub_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ i : Fin n,
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ i : Fin n,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ i : Fin n,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver :
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m)) :
    ‖laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 - LapTrunc g gi H F m u‖
      ≤ B (epsSeq m) := by
  have step1 : LapTrunc g gi H F m u
      = ∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
    rw [lapTrunc_eq_sum_pdpd g gi H F m u hgi hΓ]
    exact Finset.sum_congr rfl (fun i _ => hInterchange i)
  have hL : LapTrunc g gi H F m u
      = laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        - ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
    rw [step1, hLapFull, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hadj := intervalIntegral.integral_add_adjacent_intervals (hII_lo i) (hII_hi i)
    linarith [hadj]
  rw [hL]
  have hring : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      - (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
          - ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
      = ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by ring
  rw [hring]
  exact hSliver

/-! ###############################################################################
    ### U1 — the `K`-uniform `Etrunc` limit.
    ############################################################################### -/

/-- **★★ U1 — `etrunc_tendstoUniformlyOn`.**  THE `K`-UNIFORM `Etrunc` LIMIT.  With a `u`-uniform tail
    bound `‖E*F u − Etrunc … m u‖ ≤ Be(ε_m)` on `K` (the `u`-free Gaussian-domination tail estimate) and
    the rate `Be(ε_m) → 0`, the truncated residual convolution converges UNIFORMLY on `K`:
        `TendstoUniformlyOn (fun m u => Etrunc g gi H F m u)
          (fun u => heatConv (heatOp g gi H) F u 0 0) atTop K`.
    Direct `tendstoUniformlyOn_of_bound`.  (This is the uniform strengthening of the pointwise
    `etrunc_tendsto`, whose continuity-of-primitive argument gives no explicit rate; the `u`-uniform tail
    bound is the carried strip-level estimate.)  NOT `a₁ = R/6`. -/
theorem etrunc_tendstoUniformlyOn (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (K : Set ℝ)
    (Be : ℝ → ℝ)
    (hEbnd : ∀ m, ∀ u ∈ K,
        ‖heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u‖ ≤ Be (epsSeq m))
    (hEblim : Tendsto (fun m => Be (epsSeq m)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun m u => Etrunc g gi H F m u)
      (fun u => heatConv (heatOp g gi H) F u 0 0) atTop K :=
  tendstoUniformlyOn_of_bound (fun m => Be (epsSeq m)) hEbnd hEblim

/-! ###############################################################################
    ### U2 — the `K`-uniform `LapTrunc` limit.
    ############################################################################### -/

/-- **★★ U2 — `lapTrunc_tendstoUniformlyOn`.**  THE `K`-UNIFORM `LapTrunc` LIMIT.  Mirrors the pointwise
    `lapTrunc_tendsto` with every per-`u` sliver-identity input quantified `∀ u ∈ K` and the sliver bound
    `B` `u`-FREE (`hSliver` quantified `∀ u ∈ K`, bound `B(ε_m)`); via `lapTrunc_sub_bound` the difference
    is `≤ B(ε_m)` uniformly on `K`, so `tendstoUniformlyOn_of_bound` gives
        `TendstoUniformlyOn (fun m u => LapTrunc g gi H F m u)
          (fun u => laplaceBeltrami g gi (heatConv H F u · 0) 0) atTop K`.
    NOT `a₁ = R/6`. -/
theorem lapTrunc_tendstoUniformlyOn (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (K : Set ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : ∀ u ∈ K, laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ K,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ (m : ℕ), ∀ u ∈ K,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun m u => LapTrunc g gi H F m u)
      (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0) atTop K :=
  tendstoUniformlyOn_of_bound (fun m => B (epsSeq m))
    (fun m u hu => lapTrunc_sub_bound g gi H F m u hgi hΓ pdpdH
      (fun i => hInterchange m i u hu) (hLapFull u hu)
      (fun i => hII_lo m i u hu) (fun i => hII_hi m i u hu) B (hSliver m u hu))
    hBlim

/-! ###############################################################################
    ### U3 — ★ the loc-unif `Da`-limit in `hDuhamel_final`'s `hDaLimLU` shape.
    ############################################################################### -/

/-- **★★★ U3 — `hDaLimLU_discharge`.**  THE LOCALLY-UNIFORM `Da`-LIMIT, in the EXACT `hDaLimLU` shape
    consumed by `DuhamelLimitWiring.hDuhamel_final`:
        `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
          (fun u => laplaceBeltrami g gi (heatConv H F u · 0) 0 + heatConv (heatOp g gi H) F u 0 0)
          atTop U`.
    Route: compact-reduce (`tendstoLocallyUniformlyOn_iff_forall_isCompact`, `U` open); on each compact
    `K ⊆ U`, `hEcomb` (`DaTrunc = LapTrunc + Etrunc`) + the triangle inequality give the combined `u`-free
    bound `‖(Δ_g(H*F) u + E*F u) − DaTrunc H F m u‖ ≤ B(ε_m) + Be(ε_m)` (via `lapTrunc_sub_bound` and the
    tail bound `hEbnd`), which `→ 0` (`hBlim.add hEblim`); `tendstoUniformlyOn_of_bound` closes.  This is
    the loc-unif form of `LapTruncAssembly.hDaLim_full`.  ⚠ CONDITIONAL on the carried sliver/tail/RNC
    family (all `∀ u ∈ U`, constants `u`-free); none the conclusion.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hLapFull : ∀ u ∈ U, laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ (m : ℕ), ∀ u ∈ U,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0))
    (Be : ℝ → ℝ)
    (hEbnd : ∀ (m : ℕ), ∀ u ∈ U,
        ‖heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u‖ ≤ Be (epsSeq m))
    (hEblim : Tendsto (fun m => Be (epsSeq m)) atTop (𝓝 0))
    (hEcomb : ∀ (m : ℕ) (u : ℝ),
        DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u) :
    TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
      (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
            + heatConv (heatOp g gi H) F u 0 0) atTop U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopen]
  intro K hKU hKcompact
  refine tendstoUniformlyOn_of_bound (fun m => B (epsSeq m) + Be (epsSeq m)) ?_
    (by simpa using hBlim.add hEblim)
  intro m u hu
  show ‖laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        + heatConv (heatOp g gi H) F u 0 0 - DaTrunc H F m u‖ ≤ B (epsSeq m) + Be (epsSeq m)
  have hLb : ‖laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 - LapTrunc g gi H F m u‖
      ≤ B (epsSeq m) :=
    lapTrunc_sub_bound g gi H F m u hgi hΓ pdpdH
      (fun i => hInterchange m i u (hKU hu)) (hLapFull u (hKU hu))
      (fun i => hII_lo m i u (hKU hu)) (fun i => hII_hi m i u (hKU hu))
      B (hSliver m u (hKU hu))
  have hEb : ‖heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u‖ ≤ Be (epsSeq m) :=
    hEbnd m u (hKU hu)
  rw [hEcomb m u]
  have hring : laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        + heatConv (heatOp g gi H) F u 0 0 - (LapTrunc g gi H F m u + Etrunc g gi H F m u)
      = (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 - LapTrunc g gi H F m u)
        + (heatConv (heatOp g gi H) F u 0 0 - Etrunc g gi H F m u) := by ring
  rw [hring]
  exact le_trans (norm_add_le _ _) (add_le_add hLb hEb)

/-! ###############################################################################
    ### U4 — ★ the `hDerivLU` in `derivConv_tendsto`'s exact input shape.
    ############################################################################### -/

/-- **★★★ U4 — `hDerivLU_discharge`.**  THE `hDerivLU` INPUT of `DuhamelLimitWiring.derivConv_tendsto`,
    in its EXACT loc-unif shape:
        `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u)
          (fun u => (laplaceBeltrami g gi (heatConv H F u · 0) 0 + heatConv (heatOp g gi H) F u 0 0)
                + F u 0 0) atTop U`.
    A direct `tendstoLocallyUniformlyOn_add` of the loc-unif `Da`-limit `hDaLimLU` (U3's output shape)
    and the boundary loc-unif `hbdryLU` (`BoundaryTrunc → F · 0 0`, already PROVEN by
    `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, supplied as a carried input).  The target `D`
    matches the `hDerivLU` assembled inside `hDuhamel_final` VERBATIM.  NOT `a₁ = R/6`. -/
theorem hDerivLU_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) atTop U)
    (hbdryLU : TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u)
        (fun u => F u 0 0) atTop U) :
    TendstoLocallyUniformlyOn
        (fun m u => DaTrunc H F m u + BoundaryTrunc H F m u)
        (fun u => (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) + F u 0 0) atTop U :=
  tendstoLocallyUniformlyOn_add hDaLimLU hbdryLU

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.tendstoUniformlyOn_of_bound
#print axioms QIQTH.HeatResidualBound.lapTrunc_sub_bound
#print axioms QIQTH.HeatResidualBound.etrunc_tendstoUniformlyOn
#print axioms QIQTH.HeatResidualBound.lapTrunc_tendstoUniformlyOn
#print axioms QIQTH.HeatResidualBound.hDaLimLU_discharge
#print axioms QIQTH.HeatResidualBound.hDerivLU_discharge
