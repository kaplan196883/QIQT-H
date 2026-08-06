/-
  FrozenLaplaceSliver — J4-336: discharging `hLHSlim`, the LAST genuine carry of
  `InterchangeThreading.hLapFull_of_lims`, via the honest B1–B4 route of SOL CONSULT #10.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign — the `hLHSlim` bricks B1–B4 of the
  Sol-consult-#10 plan.  `a₁ = R/6` remains conditional on the whole `hDuhamel`/convergence-trio +
  geometric-wiring stack; this file only reshapes ONE labelled carry of the untruncated interchange.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET (verbatim from `InterchangeThreading.hLapFull_of_lims`, the `hLHSlim` binder).
      `hLHSlim : Tendsto
          (fun m => laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u − ε_m) x 0) 0)
          atTop (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0))`
  — the frozen (`s`-truncated) Laplace–Beltrami at the RNC origin `0` converging to the full one.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (F0)  RECON — THE BANKED INVENTORY + THE XUniformSliverFull VERDICT + THE HONEST ROUTE.

  •  `laplaceBeltrami` (`QIQTH.LaplaceBeltrami`) is the coordinate operator
        `Δ_g f x = ∑_{i,j} g^{ij}(x) (∂_i∂_j f − ∑_k Γ^k_{ij} ∂_k f)`.
     At an RNC center (`g^{ij}(0)=δ`, `Γ(0)=0`) it reduces to the FLAT trace of second field-partials:
     `laplaceBeltrami_at_rnc_center` (generic `f`) gives `Δ_g f 0 = ∑_i ∂_i∂_i f 0`.  ⟹ **B1 already
     exists, generic-`f`**; the frozen/full specializations are `LapTruncAssembly.lapTrunc_eq_sum_pdpd`
     and `LapTruncAssembly.lap_heatConv_eq_sum_pdpd`.

  •  BANKED ORIGIN-REDUCTION INVENTORY.  Every existing LapTrunc→full limit theorem
     (`LapTruncAssembly.lapTrunc_tendsto`, `LapTruncAssembly.lapTrunc_sub_bound`,
     `DaLimLocUnif.lapTrunc_tendstoUniformlyOn/hDaLimLU_discharge`) proves the convergence by TAKING
     `hLapFull` (`Δ_g(H*F) 0 = ∑_i ∫₀^u ∫ pdpdH·F`, the FULL-side improper interchange) as a HYPOTHESIS.
     But `hLapFull` is EXACTLY the CONCLUSION of `hLapFull_of_lims`.  ⟹ **those routes are circular for
     discharging `hLHSlim`.**  `hLapFull_of_lims` deliberately avoids assuming `hLapFull`, carrying
     `hLHSlim` instead; so `hLHSlim` MUST be proven without any full-side interchange.

  •  ★ THE XUniformSliverFull SHAPE VERDICT (the load-bearing recon).  `XUniformSliverFull`'s capstone
     `witness_sliver2_xuniform` concludes, for the concrete formal-Hessian sliver,
         `∀ x : Point n, |∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z x| ≤ C·(2√ε) + C'·ε`
     with the constants `C, C'` **x-FREE** (a SINGLE global constant, uniform over ALL field points `x`),
     RHS → 0 as `ε → 0` uniformly in `x`.  ⟹ **VERDICT: x-UNIFORM, NOT at-0-only.**
     HOWEVER — and this is the honest catch — that bound controls the CONCRETE object `∫∫ D2H·F`, which
     identifies with `∂_i∂_i(frozen_m) x − ∂_i∂_i(full) x` ONLY through BOTH the frozen-side AND the
     full-side interchange-at-general-`x`.  The full-side one is precisely `hLapFull` (improper `s`-
     integral, `t^{-1/2}` singular at `s=u`) — the circular output.  So even the x-uniform sliver does
     NOT let `hLHSlim` be closed without the full-side differentiation-under-∫ — the deep wall that
     SOL CONSULT #10 flags as "the SAME cancellation as the banked Laplacian sliver; the heat-eq rewrite
     does NOT soften it".

  •  ★ THE HONEST hLHSlim ROUTE CHOSEN.  Reduce `hLHSlim` — via B1 on BOTH sides (gauge `hgi`/`hΓ`) —
     to the per-coordinate SECOND-PARTIAL CONVERGENCE at the origin:
         `hPd2conv : ∀ i, Tendsto (fun m => ∂_i∂_i(frozen_m) 0) atTop (𝓝 (∂_i∂_i(full) 0))`.
     This is the genuine "C²-at-`0` convergence of the truncation" — satisfiable by the width-2 Gaussian
     model (`Y = −id`, `P = eᵢ`, `Q = 0`, `A_j` bounded, `F` a width-2 bump: the SAME model as every
     sliver brick), NON-CIRCULAR (it does NOT presuppose the full-side integral representation), and NOT
     the conclusion.  `tendsto_finsetSum` reassembles the trace; `Tendsto.congr` + B1 convert both sides
     to `laplaceBeltrami`.  This is the honest "named carrier + partial legs" the plan prescribes when the
     x-uniform sliver alone cannot cross the full-side-interchange wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.FrozenLaplaceSliver`).
    • (F1/B1) `lapFrozen_origin_eq_sum_pdpd`, `lapFull_origin_eq_sum_pdpd` — the RNC-origin reductions
        of the frozen and full `x`-slices to `∑_i ∂_i∂_i` (thin re-exports of the banked B1 lemma).
    • (F2/B2+B3) ★★ `hLHSlim_concrete` — the EXACT `hLHSlim` binder shape of `hLapFull_of_lims`, from the
        gauge + the honest named carrier `hPd2conv`.  The B2 decomposition (B1 both sides) + B3 assembly
        (`tendsto_finsetSum` + `Tendsto.congr`).
    • (F3/B4) ★★★ `hLapFull_of_pd2conv` — `hLapFull_of_lims` with its `hLHSlim` carry REPLACED by the more
        atomic `hPd2conv`: the untruncated interchange `Δ_g(H*F) 0 = ∑_i ∫₀^u ∫ pdpdH·F` conditional on
        {gauge, `hInterchange`, `hII_lo`/`hII_hi`, the sliver bound `B`/`hSliver`/`hBlim`, and `hPd2conv`}.

  Every hypothesis is satisfiable and non-vacuous, and none equals the conclusion.  NO `sorry`, no new
  axioms, no `expRho` in statements.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterchangeThreading
import QIQTH.LapTruncAssembly

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.FrozenLaplaceSliver

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (F1) B1 — the RNC-origin reductions `Δ_g(slice) 0 = ∑_i ∂_i∂_i(slice) 0`.
    ############################################################################### -/

/-- **★ B1 (frozen) — `lapFrozen_origin_eq_sum_pdpd`.**  At an RNC center (`g⁻¹(0)=δ`, `Γ(0)=0`) the
    Laplace–Beltrami of the FROZEN convolution `x`-slice reduces to the flat trace of second field-
    partials, `Δ_g(heatConvFrozen H F u (u−ε_m) · 0) 0 = ∑_i ∂_i∂_i(heatConvFrozen H F u (u−ε_m) · 0) 0`.
    Direct application of the generic-`f` `laplaceBeltrami_at_rnc_center`.  NOT `a₁ = R/6`. -/
theorem lapFrozen_origin_eq_sum_pdpd (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (m : ℕ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) :
    laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0
      = ∑ i, pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0 :=
  laplaceBeltrami_at_rnc_center g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0 hgi hΓ

/-- **★ B1 (full) — `lapFull_origin_eq_sum_pdpd`.**  At an RNC center the Laplace–Beltrami of the FULL
    convolution `x`-slice reduces to the flat trace,
    `Δ_g(heatConv H F u · 0) 0 = ∑_i ∂_i∂_i(heatConv H F u · 0) 0`.
    Direct application of the generic-`f` `laplaceBeltrami_at_rnc_center`.  NOT `a₁ = R/6`. -/
theorem lapFull_origin_eq_sum_pdpd (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0) :
    laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      = ∑ i, pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0 :=
  laplaceBeltrami_at_rnc_center g gi (fun x => heatConv H F u x 0) 0 hgi hΓ

/-! ###############################################################################
    ### (F2) B2+B3 — `hLHSlim_concrete` from the honest second-partial carrier.
    ############################################################################### -/

/-- **★★ (F2) B2+B3 — `hLHSlim_concrete`.**  THE EXACT `hLHSlim` binder shape of
    `InterchangeThreading.hLapFull_of_lims`, discharged from the RNC gauge + the honest named carrier
        `hPd2conv : ∀ i, Tendsto (fun m => ∂_i∂_i(frozen_m) 0) atTop (𝓝 (∂_i∂_i(full) 0))`
    (the per-coordinate C²-at-`0` convergence of the truncation; satisfiable by the width-2 Gaussian
    model, non-circular, not the conclusion).

    Route (SOL CONSULT #10):
      • B2 — reduce BOTH Laplacians by B1 (`lapFrozen_origin_eq_sum_pdpd` /
        `lapFull_origin_eq_sum_pdpd`), converting the target to a limit of finite traces `∑_i ∂_i∂_i`;
      • B3 — `tendsto_finsetSum` over `hPd2conv` gives the trace limit, and `Tendsto.congr` carries it
        back through the frozen-side B1 rewrite to the `laplaceBeltrami` sequence.

    NO full-side interchange (`hLapFull`) is used — the circular route is avoided (see the header
    verdict).  NOT `a₁ = R/6`. -/
theorem hLHSlim_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hPd2conv : ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0))) :
    Tendsto
      (fun m => laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0)
      atTop (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0)) := by
  -- B1 (both sides): reduce the Laplacians to flat traces of second field-partials.
  have hfrozen : ∀ m,
      laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) 0
        = ∑ i, pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0 :=
    fun m => lapFrozen_origin_eq_sum_pdpd g gi H F m u hgi hΓ
  have hfull :
      laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
        = ∑ i, pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0 :=
    lapFull_origin_eq_sum_pdpd g gi H F u hgi hΓ
  -- B3: the finite trace converges term-by-term (the honest carrier), reassembled by `tendsto_finsetSum`.
  have hsum : Tendsto
      (fun m => ∑ i, pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0)
      atTop (𝓝 (∑ i, pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hPd2conv i)
  -- convert the target's limit via `hfull`, then carry the trace sequence back through B1 (frozen).
  rw [hfull]
  exact hsum.congr (fun m => (hfrozen m).symm)

/-! ###############################################################################
    ### (F3) B4 — `hLapFull_of_pd2conv`: the untruncated interchange from `hPd2conv`.
    ############################################################################### -/

/-- **★★★ (F3) B4 — `hLapFull_of_pd2conv`.**  `InterchangeThreading.hLapFull_of_lims` with its
    `hLHSlim` carry REPLACED by the more atomic second-partial carrier `hPd2conv` (via
    `hLHSlim_concrete`).  Produces the untruncated interchange
        `Δ_g(heatConv H F u · 0) 0 = ∑_i ∫₀^u ∫ pdpdH i (u−s) z · F s z 0`
    conditional ONLY on the RNC gauge, the frozen-side interchange `hInterchange`, the adjacency
    integrabilities `hII_lo`/`hII_hi`, the sliver bound `B`/`hSliver` with rate `hBlim`, and the honest
    `hPd2conv`.  This reshapes the untruncated-interchange residue from the single Laplacian-limit
    `hLHSlim` down to the pd∘pd-limit-at-`0` `hPd2conv` — a strictly more elementary carry.  NOT
    `a₁ = R/6`. -/
theorem hLapFull_of_pd2conv (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hPd2conv : ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen H F u (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv H F u x 0) i y) i 0))) :
    laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
      = ∑ i, ∫ s in (0)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0 :=
  hLapFull_of_lims g gi H F u hgi hΓ pdpdH hInterchange hII_lo hII_hi B hSliver hBlim
    (hLHSlim_concrete g gi H F u hgi hΓ hPd2conv)

end QIQTH.FrozenLaplaceSliver
