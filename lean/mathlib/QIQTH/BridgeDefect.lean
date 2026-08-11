/-
  BridgeDefect — J4-618: the FrozenTransportBridge REDUCTION — the bridge compares ONLY the
  k ≥ 2 tails, so it does NOT need a frozen-vs-transport difference estimate at all: it reduces
  to an O(s) tail bound for the TRANSPORT defect, which this brick derives GENERICALLY from
  hAdom-family Gaussian dominations (uniform O(1) width-2 + α = −1/2 + per-step integrability).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE ACCOUNTING VERDICT (V1, certified by the definitions read, not re-derived):
  `leviSeries E = ∑'_m (−1)^(m+1)·iterE E (m+1)` (TrueHeatKernel), whose m = 0 term is `−E`
  (`iterE_one`).  Hence `leviSeries E + E` is EXACTLY the k ≥ 2 signed tail, and the owed
  bridge Prop `FrozenTransportBridge E F` (CoInstSmoke §3) compares ONLY the two k ≥ 2 tails.
  Since the FROZEN tail already has the banked O(s) bound (`frozenColumn_tail_O_s`, J4-616),
  the TRIANGLE INEQUALITY discharges the bridge from a single new input:

      (owed)  |leviSeries E_transport (s,p,0) + E_transport (s,p,0)| ≤ C·s·G_{8s}(p)   (0 < s ≤ 1)

  — NO difference/comparison estimate between the two parametrices is needed.  The k = 1
  difference −E_frozen vs −E_transport cancels out of the bridge entirely (it lives in the
  separate `K1TransportBudget` thread, untouched here).

  ★ THE GENERIC O(s) TRANSPORT-TAIL MECHANISM (V2, the new mathematics of this brick):
  the frozen O(s) tail needed the J4-616 structured two-term outer bound because the frozen
  defect's generic-column bound is only `(C/√τ)·G_{2τ}` (α = −1/2).  But for a defect kernel
  with a UNIFORM O(1) Gaussian domination `|E(τ,p,q)| ≤ C_U·G_{2τ}(p−q)` — the hAdom-family
  shape the curved capstone ALREADY carries at the row column (`hAdomHeat`), here demanded at
  ALL rows — the k = 2 term is O(s) DIRECTLY: the Beta step at exponents (0,0) is
      ∫₀ˢ (s−σ)⁰·σ⁰ dσ = s·B(1,1) = s,   G_{2(s−σ)} ∗ G_{2σ} = G_{2s}  (exact, banked),
  so `|iterE E 2 (s,p,0)| ≤ C_U²·s·G_{2s}(p)` (`bridgeGenericK2_O_s`) — no moment ledger, no
  structured coefficient supplier.  The k ≥ 3 sub-tail is O(s) by the GENERIC banked ladder
  (`leviSeries_column_k3_bound`, J4-613 — generic in E).  Gluing + one width widening
  `G_{2s} → 2ⁿ·G_{8s}` gives the generic O(s) tail (`bridgeGeneric_tail_O_s`).

  WHAT LANDS.
    ▸ ★ `bridgeGenericK2_O_s` — k = 2 is O(s) under the uniform O(1) domination (all s > 0).
    ▸ ★ `bridgeGeneric_tail_O_s` — the FULL k ≥ 2 tail is O(s)·G_{8s} under
      {α = −1/2 bound, uniform O(1) bound, per-step integrability} — ALL generic in E.
    ▸ `frozenTransportBridge_of_tail_O_s` — tail O(s) for E ⟹ the bridge vs the banked frozen
      side, by triangle (NO difference estimate).
    ▸ ★★ `frozenTransportBridge_of_dominations` — THE REDUCTION: the owed bridge Prop holds
      under the three hAdom-family dominations of E — the bridge is no longer a comparison
      wall; it is an APPLICATION of the generic ladder under Gaussian-domination carries.
    ▸ ★★ `transport_bridge_of_dominations` / `transport_corrHigher_of_dominations` — the
      TRANSPORT-PINNED instantiations at the capstone's own defect kernel
      `capstoneDefect = heatOp g^κ gi^κ (vanVleckGatedWitness …)`: the bridge, and (chained
      through the certified `smoke_bridge_verdict` transfer) the full bounded-cRem O(t²)
      corrHigher API for the capstone's k ≥ 2 tail — all under CARRIED, LABELLED dominations.
    ▸ NON-VACUITY: `bridgeWitnessKernel` (time-gated flat Gaussian) — a genuinely NONZERO
      kernel (`bridgeWitnessKernel_ne_zero`) satisfying ALL three domination hypotheses with
      PROOFS (C = C_U = 1), yielding `frozenTransportBridge_witness`: an unconditionally
      PROVED `FrozenTransportBridge` instance at genuinely curved frozen data (κ = −1,
      r = 1/2).  The hypothesis pile of the reduction is jointly inhabited — no vacuous
      conditional.

  ⚠ HONEST SCOPE — what the reduction does and does NOT do.  The three domination hypotheses
  on the TRANSPORT defect are CARRIED, not proved: `hEuni` (uniform O(1) at ALL rows) is the
  hAdom-family shape but STRICTLY STRONGER than the capstone's carried `hAdomHeat` (row 0
  only, general width wA vs width 2 here); `hEbound`/`hInt` are the J4-610/612 supplier
  shapes at the transport kernel (proved for the FROZEN kernel, owed for the transport one).
  So `FrozenTransportBridge` is NOT discharged — it is REDUCED to the all-rows Gaussian
  domination pile for `heatOp g^κ gi^κ (vanVleckGatedWitness …)` (+ per-step integrability),
  i.e. from a Levi-comparison wall to a (large but standard) domination-supplier wall.
  `a₁ = R/6` remains CONDITIONAL: flat tower non-vacuous and closed; the curved side owes
  these transport dominations, the k = 1 `K1TransportBudget`, the per-q producer re-assembly,
  the fat-K carrier piles (incl. the capstone's own hAdom/hFdomW/measurability piles), the
  full capstone co-instantiation, and the prior piles.  No axioms, no sorry, no `:= True`.
-/
import Mathlib
import QIQTH.CoInstSmoke

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.FrozenK2Sharp QIQTH.CoInstSmoke
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixAnsatz

namespace QIQTH.BridgeDefect

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. ★ The generic k = 2 O(s) bound — the (0,0) Beta step under a UNIFORM domination. -/

/-- **★ `bridgeGenericK2_O_s` — the k = 2 term is O(s) under a UNIFORM O(1) Gaussian
    domination.**  If `|E(τ,p,q)| ≤ C_U·G_{2τ}(p−q)` for ALL rows and columns (τ > 0) — the
    hAdom-family shape with NO `τ^{−1/2}` singularity — then
        `|iterE E 2 (s,p,0)| ≤ C_U²·s·G_{2s}(p−0)`   (ALL s > 0):
    the Beta step at exponents `(0,0)` gives `∫₀ˢ dσ = s` and the exact Chapman–Kolmogorov
    `G_{2(s−σ)} ∗ G_{2σ} = G_{2s}` — the factor `s` comes for FREE from the time integral,
    with no moment ledger and no structured coefficient supplier (contrast J4-616, which had
    to fight the frozen kernel's irreducible `τ^{−1/2}` generic-column singularity). -/
theorem bridgeGenericK2_O_s (E : ℝ → Point n → Point n → ℝ) (C C_U : ℝ)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → |E τ p q| ≤ C_U * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∀ (s : ℝ), 0 < s → ∀ p : Point n,
      |iterE E 2 s p 0| ≤ C_U ^ 2 * (s * gaussDdim (2 * s) (p - 0)) := by
  intro s hs p
  obtain ⟨hI1, hI2, hIf, -, -⟩ := hInt 1 le_rfl s hs p 0
  -- the uniform bound in the α = 0 `baseKernelW` shape
  have huniW : ∀ τ (p' q' : Point n), 0 < τ →
      |E τ p' q'| ≤ C_U * baseKernelW (2 : ℝ) (0 : ℝ) τ p' q' := by
    intro τ p' q' hτ
    have hbw : baseKernelW (2 : ℝ) (0 : ℝ) τ p' q' = gaussDdim (2 * τ) (p' - q') := by
      simp only [baseKernelW, Real.rpow_zero, one_mul]
    rw [hbw]
    exact hEuni τ p' q' hτ
  have hB : ∀ (τ : ℝ) (z : Point n), 0 < τ →
      |iterE E 1 τ z 0| ≤ C_U * baseKernelW (2 : ℝ) (0 : ℝ) τ z 0 := by
    intro τ z hτ
    rw [iterE_one]
    exact huniW τ z 0 hτ
  have hIg : ∀ σ, Integrable (fun z => C_U * baseKernelW (2 : ℝ) (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z 0)) :=
    fun σ => mixedColZ_integrable (0 : ℝ) (0 : ℝ) C_U C_U s σ p 0
  have hIsg : IntervalIntegrable (fun σ => ∫ z, C_U * baseKernelW (2 : ℝ) (0 : ℝ) (s - σ) p z
      * (C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z 0)) volume 0 s :=
    mixedColS_intervalIntegrable (0 : ℝ) (0 : ℝ) C_U C_U (by norm_num) (by norm_num) s hs p 0
  rw [show (2 : ℕ) = 1 + 1 from rfl, iterE_succ E le_rfl]
  simp only [heatConvK_apply]
  have hdom := heatConv_le_of_abs_le_pos_right E (iterE E 1)
    (fun τ p' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) τ p' q')
    (fun σ z' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z' q')
    s p 0 hs (fun τ p' q' hτ => huniW τ p' q' hτ) (fun τ z' hτ => hB τ z' hτ)
    hI1 hI2 hIf hIg hIsg
  have hRHS : heatConv (fun τ p' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) τ p' q')
      (fun σ z' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z' q') s p 0
      = C_U ^ 2 * (s * gaussDdim (2 * s) (p - 0)) := by
    rw [heatConv_smul_left C_U (baseKernelW (2 : ℝ) (0 : ℝ))
          (fun σ z' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z' q') s p 0,
        heatConv_smul_right C_U (baseKernelW (2 : ℝ) (0 : ℝ))
          (baseKernelW (2 : ℝ) (0 : ℝ)) s p 0]
    unfold baseKernelW
    rw [gaussTimePow_conv_beta_scaled 2 0 0 (by norm_num) (by norm_num) (by norm_num) s hs p 0,
        show ((0 : ℝ) + 0 + 1) = (1 : ℝ) from by norm_num,
        show ((0 : ℝ) + 0 + 2) = (2 : ℝ) from by norm_num,
        show ((0 : ℝ) + 1) = (1 : ℝ) from by norm_num,
        Real.rpow_one, Real.Gamma_one, Real.Gamma_two]
    ring
  calc |heatConv E (iterE E 1) s p 0|
      ≤ heatConv (fun τ p' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) τ p' q')
          (fun σ z' q' => C_U * baseKernelW (2 : ℝ) (0 : ℝ) σ z' q') s p 0 := hdom
    _ = C_U ^ 2 * (s * gaussDdim (2 * s) (p - 0)) := hRHS

/-! ### 2. ★ The generic O(s) k ≥ 2 tail — k = 2 (above) + banked generic k ≥ 3 ladder. -/

/-- **★ `bridgeGeneric_tail_O_s` — the FULL k ≥ 2 tail is O(s)·G_{8s}, GENERICALLY in `E`.**
    Under the three hAdom-family dominations —
      * `hEbound` : the α = −1/2 generic bound `|E| ≤ C·τ^{−1/2}·G_{2τ}` (J4-610 shape),
      * `hEuni`   : the UNIFORM O(1) bound `|E| ≤ C_U·G_{2τ}` at ALL rows (hAdomHeat shape),
      * `hInt`    : the per-step integrability pack (J4-612 producer shape) —
    the k ≥ 2 Levi tail on the center column is `O(s)·G_{8s}` on `(0,1]`:
    k = 2 by `bridgeGenericK2_O_s`, k ≥ 3 by the banked GENERIC ladder
    (`leviSeries_column_k3_bound`, J4-613), one width widening `G_{2s} ≤ 2ⁿ·G_{8s}`.
    This is the transport-side replay of J4-616 with the structured-coefficient wall REPLACED
    by the uniform-domination hypothesis.  ⚠ NOT `a₁ = R/6`. -/
theorem bridgeGeneric_tail_O_s (E : ℝ → Point n → Point n → ℝ) (C C_U : ℝ)
    (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ →
      |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → |E τ p q| ≤ C_U * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C_os * (s * gaussDdim (8 * s) (p - 0)) := by
  have hEcol : ∀ (τ : ℝ) (p : Point n), 0 < τ →
      |E τ p 0| ≤ C_U * gaussDdim (2 * τ) (p - 0) := fun τ p hτ => hEuni τ p 0 hτ
  have hk3 := leviSeries_column_k3_bound E C C_U hC hCU hEbound hEcol hInt
  have hk2 := bridgeGenericK2_O_s E C C_U hEuni hInt
  have hsum_nn : 0 ≤ (∑' m : ℕ, colC C C_U (m + 2)) :=
    tsum_nonneg (fun m => colC_nonneg C C_U hC hCU (m + 2))
  refine ⟨((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2) * 2 ^ n, by positivity,
    fun s p hs hs1 => ?_⟩
  have hG8 : 0 ≤ gaussDdim (8 * s) (p - 0) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hwide : gaussDdim (2 * s) (p - 0) ≤ 2 ^ n * gaussDdim (8 * s) (p - 0) :=
    gaussDdim_widen_le (2 * s) (8 * s) (by linarith) (by linarith) (by linarith) _
  calc |leviSeries E s p 0 + E s p 0|
      = |(leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0) + iterE E 2 s p 0| := by ring_nf
    _ ≤ |leviSeries E s p 0 + E s p 0 - iterE E 2 s p 0| + |iterE E 2 s p 0| := abs_add_le _ _
    _ ≤ (∑' m : ℕ, colC C C_U (m + 2)) * (s * gaussDdim (2 * s) (p - 0))
          + C_U ^ 2 * (s * gaussDdim (2 * s) (p - 0)) :=
        add_le_add (hk3 s hs hs1 p) (hk2 s hs p)
    _ = ((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2) * (s * gaussDdim (2 * s) (p - 0)) := by
        ring
    _ ≤ ((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2)
          * (s * (2 ^ n * gaussDdim (8 * s) (p - 0))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwide hs.le)
          (by positivity)
    _ = (((∑' m : ℕ, colC C C_U (m + 2)) + C_U ^ 2) * 2 ^ n)
          * (s * gaussDdim (8 * s) (p - 0)) := by ring

/-! ### 3. The bridge by TRIANGLE — no difference estimate needed. -/

/-- **`frozenTransportBridge_of_tail_O_s` — tail O(s) ⟹ the bridge, by triangle.**  The
    bridge Prop compares only the two k ≥ 2 tails (`leviSeries E + E` — the k = 1 terms `−E`
    cancel out of the sum, see `leviSeries_split`); the frozen tail is banked O(s)
    (`frozenColumn_tail_O_s`, J4-616), so ANY O(s) bound on the other tail closes the bridge
    with `C_B = C_os + C_frozen` — NO frozen-vs-transport difference/comparison estimate. -/
theorem frozenTransportBridge_of_tail_O_s (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r)
    (E : ℝ → Point n → Point n → ℝ) (C_os : ℝ) (hCos : 0 ≤ C_os)
    (htail : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C_os * (s * gaussDdim (8 * s) (p - 0))) :
    FrozenTransportBridge E (frozenDefectKernel K r) := by
  obtain ⟨C_f, hCf, hf⟩ := frozenColumn_tail_O_s (n := n) K r hK hr
  refine ⟨C_os + C_f, add_nonneg hCos hCf, fun s p hs hs1 => ?_⟩
  calc |(leviSeries E s p 0 + E s p 0)
          - (leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0)|
      ≤ |leviSeries E s p 0 + E s p 0|
          + |leviSeries (frozenDefectKernel K r) s p 0 + frozenDefectKernel K r s p 0| := by
        rw [sub_eq_add_neg]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_neg]
    _ ≤ C_os * (s * gaussDdim (8 * s) (p - 0)) + C_f * (s * gaussDdim (8 * s) (p - 0)) :=
        add_le_add (htail s p hs hs1) (hf s p hs hs1)
    _ = (C_os + C_f) * (s * gaussDdim (8 * s) (p - 0)) := by ring

/-- **★★ `frozenTransportBridge_of_dominations` — THE REDUCTION.**  The owed bridge Prop
    (CoInstSmoke V2) holds for ANY defect kernel `E` under the three hAdom-family Gaussian
    dominations — the bridge is no longer a Levi-COMPARISON wall: it is an application of the
    generic ladder + triangle under domination carries.  ⚠ CONDITIONAL on the carried
    dominations of `E` (labelled in the transport instantiation below); NOT `a₁ = R/6`. -/
theorem frozenTransportBridge_of_dominations (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r)
    (E : ℝ → Point n → Point n → ℝ) (C C_U : ℝ) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ →
      |E τ p q| ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ → |E τ p q| ≤ C_U * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW E (2 : ℝ) (-(1 / 2) : ℝ) C) :
    FrozenTransportBridge E (frozenDefectKernel K r) := by
  obtain ⟨C_os, hCos, htail⟩ := bridgeGeneric_tail_O_s E C C_U hC hCU hEbound hEuni hInt
  exact frozenTransportBridge_of_tail_O_s K r hK hr E C_os hCos htail

/-! ### 4. ★★ The TRANSPORT-PINNED instantiations — at the capstone's own defect kernel. -/

/-- **★★ `transport_bridge_of_dominations` — the bridge at the capstone's OWN defect.**  For
    `E := capstoneDefect P.κ … = heatOp g^κ gi^κ (vanVleckGatedWitness …)` (the kernel the
    curved capstone `curved_a1_R6_fully_wired_center` actually convolves), the owed
    `FrozenTransportBridge` holds under the CARRIED, LABELLED transport dominations:
      * `hEbound` — α = −1/2 generic Gaussian domination (J4-610 supplier shape),
      * `hEuni`   — UNIFORM O(1) width-2 domination at ALL rows: the hAdom-family shape
        (the capstone's own `hAdomHeat` is EXACTLY this at row 0, width `wA`); ⚠ STRICTLY
        STRONGER than `hAdomHeat` (all rows, width pinned to 2) — honest labelled carry,
      * `hInt`    — per-step integrability (J4-612 producer shape).
    ⚠ These are the transport-side analytic pile (owed); the REDUCTION is the content. -/
theorem transport_bridge_of_dominations (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (S : Point n → Set (Point n)) (a b : ℝ)
    (C C_U : ℝ) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    -- ⚠ CARRIED (labelled): the transport-defect domination pile — see docstring.
    (hEbound : ∀ τ (p q : Point n), 0 < τ →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ →
      |capstoneDefect P.κ hChr hKc S a b τ p q| ≤ C_U * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW (capstoneDefect P.κ hChr hKc S a b)
      (2 : ℝ) (-(1 / 2) : ℝ) C) :
    FrozenTransportBridge (capstoneDefect P.κ hChr hKc S a b)
      (frozenDefectKernel P.κ P.rS) :=
  frozenTransportBridge_of_dominations P.κ P.rS P.hκ.le P.hrS.le
    (capstoneDefect P.κ hChr hKc S a b) C C_U hC hCU hEbound hEuni hInt

/-- **★★ `transport_corrHigher_of_dominations` — the capstone-shaped bounded-cRem O(t²) API
    for the TRANSPORT k ≥ 2 tail, under the carried dominations.**  Chains the bridge above
    through the certified transfer `smoke_bridge_verdict` (J4-617): under the same carried
    transport dominations, the capstone's own `leviSeries E + E` slot (with
    `E = capstoneDefect …`) gets the full `hCorrHigher` equality shape + O(t²) assembly +
    BOUNDED cRem — the J4-609→616 frozen chain fully transferred to the transport side.
    Together with `leviSeries_split`, the capstone's `leviSeries E` slot is covered modulo
    exactly `K1TransportBudget` (the k = 1 thread, untouched).  ⚠ NOT `a₁ = R/6`. -/
theorem transport_corrHigher_of_dominations (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (S : Point n → Set (Point n)) (a b : ℝ)
    (C C_U : ℝ) (hC : 0 ≤ C) (hCU : 0 ≤ C_U)
    (hEbound : ∀ τ (p q : Point n), 0 < τ →
      |capstoneDefect P.κ hChr hKc S a b τ p q|
        ≤ C * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q)
    (hEuni : ∀ τ (p q : Point n), 0 < τ →
      |capstoneDefect P.κ hChr hKc S a b τ p q| ≤ C_U * gaussDdim (2 * τ) (p - q))
    (hInt : IterConvIntegrableW (capstoneDefect P.κ hChr hKc S a b)
      (2 : ℝ) (-(1 / 2) : ℝ) C) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a' : ℝ) (ζ : Point n), 0 < a' →
          |H a' 0 ζ| ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                      + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0
                    / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries (capstoneDefect P.κ hChr hKc S a b) σ p q
                + capstoneDefect P.κ hChr hKc S a b σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| :=
  smoke_bridge_verdict P (capstoneDefect P.κ hChr hKc S a b)
    (transport_bridge_of_dominations P hChr hKc S a b C C_U hC hCU hEbound hEuni hInt)

/-! ### 5. NON-VACUITY — the domination pile is jointly inhabited at a NONZERO kernel. -/

/-- **`bridgeWitnessKernel` — the time-gated flat Gaussian.**  A genuinely nonzero kernel
    satisfying ALL THREE domination hypotheses of the reduction with PROOFS (C = C_U = 1) —
    the joint-inhabitation witness for the reduction's antecedent pile. -/
noncomputable def bridgeWitnessKernel : ℝ → Point n → Point n → ℝ :=
  fun τ p q => if 0 < τ ∧ τ ≤ 1 then gaussDdim (2 * τ) (p - q) else 0

/-- The uniform O(1) domination, at `C_U = 1`. -/
theorem bridgeWitnessKernel_uni : ∀ τ (p q : Point n), 0 < τ →
    |bridgeWitnessKernel τ p q| ≤ 1 * gaussDdim (2 * τ) (p - q) := by
  intro τ p q hτ
  rw [one_mul]
  unfold bridgeWitnessKernel
  by_cases h1 : τ ≤ 1
  · rw [if_pos ⟨hτ, h1⟩, abs_of_nonneg (QIQTH.ResidueBound.gaussDdim_nonneg _ _)]
  · rw [if_neg (fun h => h1 h.2), abs_zero]
    exact QIQTH.ResidueBound.gaussDdim_nonneg _ _

/-- The α = −1/2 generic domination, at `C = 1` (on the gate `τ ≤ 1` one has `√τ ≤ 1`). -/
theorem bridgeWitnessKernel_bound : ∀ τ (p q : Point n), 0 < τ →
    |bridgeWitnessKernel τ p q| ≤ 1 * baseKernelW (2 : ℝ) (-(1 / 2) : ℝ) τ p q := by
  intro τ p q hτ
  rw [one_mul, baseKernelW_negHalf_apply τ hτ]
  have hG : 0 ≤ gaussDdim (2 * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  unfold bridgeWitnessKernel
  by_cases h1 : τ ≤ 1
  · rw [if_pos ⟨hτ, h1⟩, abs_of_nonneg hG, le_div_iff₀ hst]
    calc gaussDdim (2 * τ) (p - q) * Real.sqrt τ
        ≤ gaussDdim (2 * τ) (p - q) * 1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr h1) hG
      _ = gaussDdim (2 * τ) (p - q) := mul_one _
  · rw [if_neg (fun h => h1 h.2), abs_zero]
    positivity

/-- Vanishing at nonpositive time (the producer's gate hypothesis). -/
theorem bridgeWitnessKernel_zero (τ : ℝ) (hτ : τ ≤ 0) (p q : Point n) :
    bridgeWitnessKernel τ p q = 0 := by
  unfold bridgeWitnessKernel
  rw [if_neg]
  rintro ⟨h1, -⟩
  linarith

/-- Joint strong measurability (for the J4-612 integrability producer). -/
theorem bridgeWitnessKernel_stronglyMeasurable :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      bridgeWitnessKernel w.1 w.2.1 w.2.2) := by
  have hset : MeasurableSet {w : ℝ × Point n × Point n | 0 < w.1 ∧ w.1 ≤ 1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hsub : Measurable (fun w : ℝ × Point n × Point n => w.2.1 - w.2.2) :=
    measurable_pi_lambda _ (fun k =>
      ((measurable_pi_apply k).comp (measurable_fst.comp measurable_snd)).sub
        ((measurable_pi_apply k).comp (measurable_snd.comp measurable_snd)))
  have hmg : Measurable (fun w : ℝ × Point n × Point n =>
      gaussDdim (2 * w.1) (w.2.1 - w.2.2)) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp
      ((measurable_fst.const_mul 2).prodMk hsub)
  have : Measurable (fun w : ℝ × Point n × Point n =>
      bridgeWitnessKernel w.1 w.2.1 w.2.2) := by
    unfold bridgeWitnessKernel
    exact Measurable.ite hset hmg measurable_const
  exact this.stronglyMeasurable

/-- The per-step integrability pack, DISCHARGED via the banked J4-612 producer. -/
theorem bridgeWitnessKernel_iterConvIntegrable :
    IterConvIntegrableW (bridgeWitnessKernel (n := n)) (2 : ℝ) (-(1 / 2) : ℝ) 1 :=
  iterConvIntegrableW_of_bound_baseMeas_alpha _ (-(1 / 2) : ℝ) 1 (by norm_num)
    bridgeWitnessKernel_bound
    (fun τ hτ p q => bridgeWitnessKernel_zero τ hτ p q)
    bridgeWitnessKernel_stronglyMeasurable

/-- The witness is genuinely NONZERO — the domination class is not the zero-kernel class. -/
theorem bridgeWitnessKernel_ne_zero :
    bridgeWitnessKernel (n := n) (1 / 2) 0 0 ≠ 0 := by
  unfold bridgeWitnessKernel
  rw [if_pos ⟨by norm_num, by norm_num⟩, sub_zero,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num]
  exact (gaussDdim_pos 1 one_pos 0).ne'

/-- **★ `frozenTransportBridge_witness` — an unconditionally PROVED bridge instance.**  At the
    genuinely curved frozen data `κ = −1 < 0`, `r = 1/2 > 0` (the `fatFrozenPackage_inhabited`
    gate data), `FrozenTransportBridge bridgeWitnessKernel (frozenDefectKernel (−1) (1/2))`
    HOLDS with all antecedents discharged — the reduction's hypothesis pile is JOINTLY
    inhabited at a nonzero kernel, so the conditional theorems above are not vacuous.
    (⚠ The witness is NOT the transport defect; the transport instantiation stays conditional
    on its carried dominations — this is the anti-vacuity gate, not the discharge.) -/
theorem frozenTransportBridge_witness :
    FrozenTransportBridge (bridgeWitnessKernel (n := n))
      (frozenDefectKernel (-1) (1 / 2)) :=
  frozenTransportBridge_of_dominations (-1) (1 / 2) (by norm_num) (by norm_num)
    (bridgeWitnessKernel (n := n)) 1 1 zero_le_one zero_le_one
    bridgeWitnessKernel_bound bridgeWitnessKernel_uni
    bridgeWitnessKernel_iterConvIntegrable

end QIQTH.BridgeDefect

section AxiomChecks
open QIQTH.BridgeDefect
#print axioms bridgeGenericK2_O_s
#print axioms bridgeGeneric_tail_O_s
#print axioms frozenTransportBridge_of_tail_O_s
#print axioms frozenTransportBridge_of_dominations
#print axioms transport_bridge_of_dominations
#print axioms transport_corrHigher_of_dominations
#print axioms bridgeWitnessKernel_iterConvIntegrable
#print axioms bridgeWitnessKernel_ne_zero
#print axioms frozenTransportBridge_witness
end AxiomChecks
