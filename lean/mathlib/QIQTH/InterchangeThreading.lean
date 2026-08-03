/-
  InterchangeThreading — J4-142: CLOSING THE INTERCHANGE GROUP of the conditional `hDuhamel`.
  Threads the freshly-banked proven discharges (`SecondOrderInterchange.hInterchange_discharge`,
  `TruncatedDuhamel.hDa_trunc`) into their slots in `SliverSumPlumbing.hDuhamel_semifinal`, and
  reduces the remaining second-order geometric carries (`hLap`, `hLapFull`) to genuine
  identification / limit inputs.  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT
  `a₁ = R/6`, and proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (all landed, ns `QIQTH.HeatResidualBound`).
    • `SecondOrderInterchange.hInterchange_discharge` — the per-`(m,i)` second-order interchange,
      VERBATIM the `hInterchange` carry of `hDuhamel_semifinal`, from its `dH`/`dHH` engine families.
    • `TruncatedDuhamel.hDa_trunc` — the `τ₀`-slot under-integral Leibniz, VERBATIM the per-`m` `hDa`
      slot of `hE_combination`; `TruncatedDuhamel.hE_combination` — the `Da = LapTrunc + Etrunc` split.
    • `LapTruncAssembly.lapTrunc_eq_sum_pdpd` — the RNC flat reduction `LapTrunc = ∑ᵢ ∂ᵢ∂ᵢ(frozen)`;
      `sliverBound_tendsto_zero` — the proven `√ε` rate; `SliverSumPlumbing.sliver_sum_bound` /
      `hDuhamel_semifinal` — the sliver plumbing and the ONE-THEOREM residue enumeration.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file).

    (T1a) `hDa_threaded` — the `hDa` slot of `hE_combination` filled by `hDa_trunc` at every `m`
          (the shapes are IDENTICAL — a clean per-`m` thread of the C3ε Leibniz engine).
    (T1b) `hLap_threaded` — the `hLap` slot (the Δ-version `LapTrunc = ∫∫ Δ_g(H-slice)·F`) reduced to
          the pd∘pd interchange: `lapTrunc_eq_sum_pdpd` + `hInterchange` express `LapTrunc` as
          `∑ᵢ ∫∫ pdpdH i·F`; pushing `∑ᵢ` under both integrals (`intervalIntegral.integral_finsetSum`,
          `integral_finsetSum`) and using the INTEGRAND-LEVEL flat reduction
          `∑ᵢ pdpdH i (u−s) z = Δ_g (H-slice)(0)` (`laplaceBeltrami_at_rnc_center` on `fun x ↦ H(u−s) x z`,
          same gauge, + the identification `hpdpdH_slice`) collapses to the Δ-form.
    (T1c) `hEcomb_discharged` — `hE_combination` with `hDa`+`hLap` filled: `∀ m, Da = LapTrunc + Etrunc`.

    (T2) ★★ `hLapFull_of_lims` — the untruncated `hLapFull`.  The truncated identities (`lapTrunc_eq_
          sum_pdpd` + `hInterchange`) give `laplaceBeltrami g gi (frozen) 0 = ∑ᵢ ∫₀^{u−ε_m} ∫ pdpdH·F`;
          the LHS C²-limit `hLHSlim` (carried) and the RHS limit (`∑ᵢ ∫₀^{u−ε_m} → ∑ᵢ ∫₀^u`, squeezed by
          the sliver bound + the PROVEN `√ε` rate via `integral_add_adjacent_intervals` /
          `squeeze_zero_norm`) meet at the same value (`tendsto_nhds_unique`), producing the exact
          `hLapFull` carried shape `Δ_g(H*F)(0) = ∑ᵢ ∫₀^u ∫ pdpdH·F`.

    (T3) ★★★ `hDuhamel_penultimate` — `hDuhamel_semifinal` with the INTERCHANGE group
          `{hInterchange, hLapFull, hDa, hLap}` REPLACED by their builders:
          `hInterchange_discharge`'s carried families ⟹ `hInterchange`; `hDa_trunc`'s families ⟹ `hDa`;
          `hpdpdH_slice`/`hpdpdZ` (+ built `hInterchange`, gauge, `hII_lo`) ⟹ `hLap`; `hLHSlim` (+ built
          `hInterchange`, gauge, `hII_lo`/`hII_hi`, the sliver bound from `hbnd`) ⟹ `hLapFull`.  The
          Duhamel-principle output conditional on the UPDATED grouped residue.  Pure threading.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — the UPDATED grouped residue of `hDuhamel_penultimate` (each a genuine fact,
  NONE the conclusion, none vacuous).

    GAUGE            `hgi` (`g⁻¹(0)=δ`), `hΓ` (`Γ(0)=0`) — the RNC normalization at the center `0`.
    INTERCHANGE      (was `{hInterchange, hLapFull, hDa, hLap}`; NOW the DISCHARGE INPUTS)
      • second-order engine (`hInterchange_discharge`): `dH`/`dHH` kernels, `hpdpdH`
        (`pdpdH i τ z = dHH τ 0 z`, the identification of the parameter with the concrete second
        field-partial), the field neighborhood `V`/`hVopen`/`hV0`, the first-order interchange `hQ1I`
        on `V`, and the dominated-differentiation families `snbI`/`hFmeasI`/`hFintI`/`hF'measI`/
        `boundI`/`hbddI`/`hboundI`/`hdiffI`.
      • `Da`-Leibniz engine (`hDa_trunc`): `nbDa`/`hFmeasDa`/`hFintDa`/`hF'measDa`/`boundDa`/`hbddDa`/
        `hboundDa`/`hdiffDa` — the C3ε families.
      • Δ-integrand reduction: `hpdpdH_slice` (`∂ᵢ∂ᵢ(H-slice)(0) = pdpdH i (u−s) z`, the concrete
        second field-partial of the `H`-slice — a genuine geometric identification), `hpdpdZ` (`z`-
        integrability of `pdpdH i·F`).
      • untruncated limit: `hLHSlim` (`Δ_g(frozen) → Δ_g(H*F)`, the derivative-of-limit content,
        carried labelled, consistent with the F2 family).
    INTEGRABILITY    `hII_lo`/`hII_hi` (adjacency-split of `pdpdH·F`), `hLapZ`/`hEZ` (`z`),
                     `hLapS`/`hES` (`s`), `hmeas` (residual `s`-measurability).
    GEOMETRIC-MODULI `D0`/`D1`/`hD0`/`hD1`/`hbnd` (the per-coordinate `√ε` sliver amplitudes; `hbnd`
                     also feeds the `hLapFull` sliver bound), `r₀`/`τ₀`, `hAnear`, `hu₀cont`/`hu₀one`/
                     `hu₀bdd`/`hu₁bdd`.
    AMPLITUDE        `A₀`/`A₁`, `E₀`/`E₁`, `C_L` with nonnegativities.
    DOMINATION       `hAdom`, `hEdom`, `hEzero`, `hBdom`.
    F2-REGULARITY    `hderiv`, `D`/`hDerivLU`, `hfg`.
    MEASURABILITY    `hBcont`, `hAmeas`/`hBmeas`, `hu₀meas`/`hu₁meas`.

    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6` —
    this is ONE brick (closing the INTERCHANGE group of the conditional `hDuhamel`) of the campaign.
-/
import Mathlib
import QIQTH.SliverSumPlumbing
import QIQTH.SecondOrderInterchange

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### T1a — thread `hDa_trunc` into `hE_combination`'s `hDa` slot.
    ############################################################################### -/

/-- **★ T1a — `hDa_threaded`.**  The `hDa` slot of `hE_combination` is EXACTLY the conclusion of
    `hDa_trunc` (identical shapes), so a per-`m` thread of the C3ε under-integral Leibniz engine
    supplies it at every `m`:
        `∀ m, DaTrunc H F m u = ∫ s in 0..(u−ε_m), ∫ z, ∂_r H(u−s) 0 z · F s z 0`.
    All carries are `hDa_trunc`'s genuine differentiation-under-∫ inputs (per `m`); none is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hDa_threaded (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (nb : ℕ → Set ℝ) (hnb : ∀ m, nb m ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ) (a : ℝ), AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ m, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ m, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℕ → ℝ → ℝ) (hbdd : ∀ m, IntervalIntegrable (bound m) volume 0 (u - epsSeq m))
    (hbound : ∀ m, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ bound m s)
    (hdiff : ∀ m, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a) :
    ∀ m, DaTrunc H F m u
      = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0 :=
  fun m => hDa_trunc H F m u (nb m) (hnb m) (hFmeas m) (hFint m) (hF'meas m)
    (bound m) (hbdd m) (hbound m) (hdiff m)

/-! ###############################################################################
    ### T1b — reduce `hE_combination`'s `hLap` (the Δ-version) to the pd∘pd interchange.
    ############################################################################### -/

/-- **★★ T1b — `hLap_threaded`.**  The `hLap` slot of `hE_combination` is the Δ-version
        `LapTrunc g gi H F m u = ∫ s in 0..(u−ε_m), ∫ z, Δ_g (fun x ↦ H(u−s) x z) 0 · F s z 0`.
    It is reduced to the pd∘pd interchange `hInterchange`: the RNC flat reduction
    (`lapTrunc_eq_sum_pdpd`, gauge `hgi`/`hΓ`) writes `LapTrunc = ∑ᵢ ∂ᵢ∂ᵢ(frozen)`, `hInterchange`
    rewrites each to `∫∫ pdpdH i·F`, and pushing `∑ᵢ` under BOTH integrals
    (`intervalIntegral.integral_finsetSum` with `hII_lo`, `integral_finsetSum` with `hpdpdZ`) reduces
    to the INTEGRAND-LEVEL flat reduction `∑ᵢ pdpdH i (u−s) z = Δ_g (fun x ↦ H(u−s) x z) 0`, itself
    `laplaceBeltrami_at_rnc_center` on the `H`-slice (SAME gauge) + the identification `hpdpdH_slice`.
    Carries the genuine interchange, the identification, and the `z`-integrability; none is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hLap_threaded (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hpdpdH_slice : ∀ (i : Fin n) (s : ℝ) (z : Point n),
        pd (fun y => pd (fun x => H (u - s) x z) i y) i 0 = pdpdH i (u - s) z)
    (hpdpdZ : ∀ (s : ℝ) (i : Fin n),
        Integrable (fun z => pdpdH i (u - s) z * F s z 0) volume)
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m)) :
    ∀ m, LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0 := by
  intro m
  -- LapTrunc = ∑ᵢ ∫∫ pdpdH i·F  (RNC flat reduction + finite-gap interchange)
  have h1 : LapTrunc g gi H F m u
      = ∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
    rw [lapTrunc_eq_sum_pdpd g gi H F m u hgi hΓ]
    exact Finset.sum_congr rfl (fun i _ => hInterchange m i)
  rw [h1, ← intervalIntegral.integral_finsetSum (fun i _ => hII_lo m i)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  rw [← integral_finsetSum Finset.univ (fun i _ => hpdpdZ s i)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  dsimp only
  rw [← Finset.sum_mul]
  congr 1
  rw [laplaceBeltrami_at_rnc_center g gi (fun x => H (u - s) x z) 0 hgi hΓ]
  exact Finset.sum_congr rfl (fun i _ => (hpdpdH_slice i s z).symm)

/-! ###############################################################################
    ### T1c — `hE_combination` with `hDa`+`hLap` filled.
    ############################################################################### -/

/-- **★ T1c — `hEcomb_discharged`.**  `hE_combination` at every `m` with its `hDa` slot filled by
    `hDa_threaded` (T1a) and its `hLap` slot by `hLap_threaded` (T1b):
        `∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u`.
    Carries the four E-combination integrabilities (`hLapZ`/`hEZ` in `z`, `hLapS`/`hES` in `s`) plus
    the T1a/T1b outputs.  NOT `a₁ = R/6`. -/
theorem hEcomb_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hDa : ∀ m, DaTrunc H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
    (hLap : ∀ m, LapTrunc g gi H F m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
    (hLapZ : ∀ s, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ s, Integrable (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : ∀ m, IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ m, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m)) :
    ∀ m, DaTrunc H F m u = LapTrunc g gi H F m u + Etrunc g gi H F m u :=
  fun m => hE_combination g gi H F m u (hDa m) (hLap m) hLapZ hEZ (hLapS m) (hES m)

/-! ###############################################################################
    ### T2 — the untruncated `hLapFull` reduction.
    ############################################################################### -/

/-- **★★ T2 — `hLapFull_of_lims`.**  The untruncated interchange `hLapFull`,
        `Δ_g (fun x ↦ heatConv H F u x 0) 0 = ∑ᵢ ∫₀^u ∫ pdpdH i (u−s) z · F s z 0`,
    from the truncated identities and two limits.  The truncated identity
    `Δ_g (frozen) 0 = ∑ᵢ ∫₀^{u−ε_m} ∫ pdpdH·F` follows from `lapTrunc_eq_sum_pdpd` (`LapTrunc` IS
    `Δ_g(frozen) 0`) + `hInterchange`.  The LHS `hLHSlim` (`Δ_g(frozen) → Δ_g(H*F)`, carried) and the
    RHS limit (`∑ᵢ ∫₀^{u−ε_m} → ∑ᵢ ∫₀^u`, squeezed by the sliver bound `hSliver`/`hBlim` via
    `integral_add_adjacent_intervals` (`hII_lo`/`hII_hi`) + `squeeze_zero_norm`) converge to the same
    value; `tendsto_nhds_unique` pins the equality.  Genuine carries; NOT `a₁ = R/6`. -/
theorem hLapFull_of_lims (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : ∀ (m : ℕ) (i : Fin n),
        pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0
          = ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (B : ℝ → ℝ)
    (hSliver : ∀ m,
        ‖∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0‖
          ≤ B (epsSeq m))
    (hBlim : Tendsto (fun m => B (epsSeq m)) atTop (𝓝 0))
    (hLHSlim : Tendsto
        (fun m => laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0)
        atTop (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0))) :
    laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
  -- truncated identity: Δ_g(frozen) = ∑ᵢ ∫₀^{u−ε_m}...
  have hstep : ∀ m, laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0
      = ∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
    intro m
    show LapTrunc g gi H F m u = _
    rw [lapTrunc_eq_sum_pdpd g gi H F m u hgi hΓ]
    exact Finset.sum_congr rfl (fun i _ => hInterchange m i)
  -- RHS limit: ∑ᵢ ∫₀^{u−ε_m} → ∑ᵢ ∫₀^u  (squeeze by the sliver bound)
  have hRHSlim : Tendsto
      (fun m => ∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
      atTop (𝓝 (∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)) := by
    have hL : ∀ m,
        (∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          = (∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
            - ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 := by
      intro m
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hadj := intervalIntegral.integral_add_adjacent_intervals (hII_lo m i) (hII_hi m i)
      linarith [hadj]
    have hbound : ∀ m,
        ‖(∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          - (∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)‖ ≤ B (epsSeq m) := by
      intro m
      rw [hL m]
      set S := ∑ i, ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 with hS
      have hring : (∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0) - S
            - ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 = -S := by ring
      rw [hring, norm_neg]
      exact hSliver m
    have h0 : Tendsto
        (fun m => (∑ i, ∫ s in (0)..(u - epsSeq m), ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          - (∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)) atTop (𝓝 0) :=
      squeeze_zero_norm hbound hBlim
    exact (tendsto_sub_nhds_zero_iff).mp h0
  -- transfer the LHS limit through `hstep`, then unique-limit.
  exact tendsto_nhds_unique (hLHSlim.congr hstep) hRHSlim

/-! ###############################################################################
    ### T3 — `hDuhamel_penultimate`: the INTERCHANGE group discharged.
    ############################################################################### -/

/-- **★★★ T3 — `hDuhamel_penultimate`.**  `SliverSumPlumbing.hDuhamel_semifinal` with the INTERCHANGE
    group `{hInterchange, hLapFull, hDa, hLap}` REPLACED by the builders that discharge them:
      • `hInterchange_discharge` (`dH`/`dHH` engine families + `hpdpdH`/`hQ1I`) ⟹ `hInterchange`;
      • `hDa_threaded` (`hDa_trunc` C3ε families) ⟹ `hDa`;
      • `hLap_threaded` (`hpdpdH_slice`/`hpdpdZ` + built `hInterchange` + gauge + `hII_lo`) ⟹ `hLap`;
      • `hLapFull_of_lims` (`hLHSlim` + built `hInterchange` + gauge + `hII_lo`/`hII_hi` + the sliver
        bound from `hbnd` via `sliver_sum_bound`) ⟹ `hLapFull`.
    The Duhamel-principle output
        `heatOp g gi (heatConv H F · · ·) u 0 0 = F u 0 0 + heatConv (heatOp g gi H) F u 0 0`
    conditional ONLY on the UPDATED grouped residue (see the header firewall).  Pure interface
    threading — the INTERCHANGE group is now built from identification/engine/limit inputs.  NOT
    `a₁ = R/6`. -/
theorem hDuhamel_penultimate (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : u ∈ U)
    (hUpos : ∀ w ∈ U, 0 < w) (hUT : ∀ w ∈ U, w ≤ T)
    -- GAUGE
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    -- INTERCHANGE PARAMETER + second-order engine (⟹ hInterchange)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (dH dHH : ℝ → Point n → Point n → ℝ)
    (hpdpdH : ∀ i τ z, pdpdH i τ z = dHH τ 0 z)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1I : ∀ (m : ℕ) (i : Fin n), ∀ y ∈ V,
        pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m), ∫ z, dH (u - s) y z * F s z 0)
    (snbI : Set ℝ) (hsnbI : snbI ∈ 𝓝 (0 : ℝ))
    (hFmeasI : ∀ (m : ℕ) (i : Fin n) (w : ℝ), AEStronglyMeasurable
      (fun s => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFintI : ∀ (m : ℕ) (i : Fin n), IntervalIntegrable
      (fun s => ∫ z, dH (u - s) (0 : Point n) z * F s z 0) volume 0 (u - epsSeq m))
    (hF'measI : ∀ (m : ℕ) (i : Fin n), AEStronglyMeasurable
      (fun s => ∫ z, dHH (u - s) (0 : Point n) z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundI : ℕ → Fin n → ℝ → ℝ)
    (hbddI : ∀ (m : ℕ) (i : Fin n), IntervalIntegrable (boundI m i) volume 0 (u - epsSeq m))
    (hboundI : ∀ (m : ℕ) (i : Fin n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snbI,
      ‖∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ boundI m i s)
    (hdiffI : ∀ (m : ℕ) (i : Fin n), ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snbI,
      HasDerivAt (fun w => ∫ z, dH (u - s) (Function.update (0 : Point n) i w) z * F s z 0)
        (∫ z, dHH (u - s) (Function.update (0 : Point n) i w) z * F s z 0) w)
    -- `Da`-Leibniz engine (⟹ hDa)
    (nbDa : ℕ → Set ℝ) (hnbDa : ∀ m, nbDa m ∈ 𝓝 u)
    (hFmeasDa : ∀ (m : ℕ) (a : ℝ), AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFintDa : ∀ m, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'measDa : ∀ m, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundDa : ℕ → ℝ → ℝ) (hbddDa : ∀ m, IntervalIntegrable (boundDa m) volume 0 (u - epsSeq m))
    (hboundDa : ∀ m, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nbDa m,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ boundDa m s)
    (hdiffDa : ∀ m, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nbDa m,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a)
    -- Δ-integrand reduction (⟹ hLap) + untruncated limit (⟹ hLapFull)
    (hpdpdH_slice : ∀ (i : Fin n) (s : ℝ) (z : Point n),
        pd (fun y => pd (fun x => H (u - s) x z) i y) i 0 = pdpdH i (u - s) z)
    (hpdpdZ : ∀ (s : ℝ) (i : Fin n), Integrable (fun z => pdpdH i (u - s) z * F s z 0) volume)
    (hLHSlim : Tendsto
        (fun m => laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0)
        atTop (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0)))
    -- INTEGRABILITY
    (hII_lo : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume 0 (u - epsSeq m))
    (hII_hi : ∀ (m : ℕ) (i : Fin n),
        IntervalIntegrable (fun s => ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
          volume (u - epsSeq m) u)
    (hLapZ : ∀ s, Integrable
        (fun z => laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0) volume)
    (hEZ : ∀ s, Integrable (fun z => heatOp g gi H (u - s) 0 z * F s z 0) volume)
    (hLapS : ∀ m, IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi (fun x => H (u - s) x z) 0 * F s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ m, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ (z : Point n), heatOp g gi H (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- GEOMETRIC-MODULI
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ),
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        H τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    -- AMPLITUDE
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    -- DOMINATION
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q| ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    -- F2-REGULARITY
    (hderiv : ∀ᶠ m in atTop, ∀ w ∈ U,
        HasDerivAt (fun v => heatConvFrozen H F v (v - epsSeq m) 0 0)
          (DaTrunc H F m w + BoundaryTrunc H F m w) w)
    (D : ℝ → ℝ)
    (hDerivLU : TendstoLocallyUniformlyOn
        (fun m w => DaTrunc H F m w + BoundaryTrunc H F m w) D atTop U)
    (hfg : ∀ w ∈ U, Tendsto (fun m => heatConvFrozen H F w (w - epsSeq m) 0 0) atTop
        (𝓝 (heatConv H F w 0 0)))
    -- MEASURABILITY
    (hBcont : ContinuousOn (fun x : ℝ × Point n => F x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume) :
    heatOp g gi (fun v p q => heatConv H F v p q) u 0 0
      = F u 0 0 + heatConv (heatOp g gi H) F u 0 0 := by
  -- build hInterchange (T-family: second-order engine)
  have hInterchange := hInterchange_discharge H dH dHH F u pdpdH hpdpdH V hVopen hV0 hQ1I
    snbI hsnbI hFmeasI hFintI hF'measI boundI hbddI hboundI hdiffI
  -- build hDa (T1a)
  have hDa := hDa_threaded H F u nbDa hnbDa hFmeasDa hFintDa hF'measDa boundDa hbddDa hboundDa hdiffDa
  -- build hLap (T1b)
  have hLap := hLap_threaded g gi H F u hgi hΓ pdpdH hInterchange hpdpdH_slice hpdpdZ hII_lo
  -- build the sliver bound (from hbnd), then hLapFull (T2)
  obtain ⟨B, hSliver, hBlim⟩ := sliver_sum_bound
    (fun i m => ∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0)
    D0 D1 hD0 hD1 hbnd
  have hLapFull := hLapFull_of_lims g gi H F u hgi hΓ pdpdH hInterchange hII_lo hII_hi
    B hSliver hBlim hLHSlim
  -- thread everything into the one-theorem residue
  exact hDuhamel_semifinal g gi H F u T hT U hUopen htU hUpos hUT hgi hΓ pdpdH
    hInterchange hLapFull hDa hLap hII_lo hII_hi hLapZ hEZ hLapS hES hmeas
    D0 D1 hD0 hD1 hbnd r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ hA₀ hA₁ E₀ E₁ hE₀ hE₁ C_L hC_L hAdom hEdom hEzero hBdom
    hderiv D hDerivLU hfg hBcont hAmeas hBmeas hu₀meas hu₁meas

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.hDa_threaded
#print axioms QIQTH.HeatResidualBound.hLap_threaded
#print axioms QIQTH.HeatResidualBound.hEcomb_discharged
#print axioms QIQTH.HeatResidualBound.hLapFull_of_lims
#print axioms QIQTH.HeatResidualBound.hDuhamel_penultimate
