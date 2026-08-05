/-
  SecondOrderMajorants — J4-255 (wide-route brick 9): THE UNIFORM-IN-`u` MAJORANT FAMILY for the
  second-order interchange engine on the TRUNCATED WINDOW.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  The second-order interchange engine `SecondOrderInterchange.pd_pd_heatConvFrozen_-
  interchange` (threaded to the concrete witness by `EngineInstantiation.witness_secondOrder_-
  interchange`, and to the ∀`m` shape by `SecondOrderInterchange.hInterchange_discharge`) consumes,
  for each gap `b := u − epsSeq m`, a `bound`/`hbdd`/`hbound` slot:
      `bound : ℝ → ℝ`,  `hbdd : IntervalIntegrable bound volume 0 b`,
      `hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
                   ‖∫ z, dHH (u−s) (update 0 i w) z · F s z 0‖ ≤ bound s`.

  ⚠ THE SINGULARITY.  The raw second-derivative kernel carries a `(u−s)⁻¹` factor (the clean shape of
  `FixedGateDichotomy.second_global_of_package`), whose endpoint `s → u` is NOT integrable.  The
  ENGINE MEMBERS, however, live at the TRUNCATIONS `b = u − epsSeq m`: there `s ≤ u − epsSeq m` forces
      `u − s ≥ epsSeq m > 0`   ⟹   `(u − s)⁻¹ ≤ (epsSeq m)⁻¹`.
  ON THE TRUNCATED WINDOW THE SINGULAR ENDPOINT IS BOUNDED (`window_inv_le`) — this is the key
  observation that makes the truncated-window engine instantiation NON-singular.  The `ε → 0` limit is
  handled downstream by the banked sliver / `DaLim` machinery, NOT here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file, ns `QIQTH.SecondOrderMajorants`).

    • `window_inv_le` — ★ THE NON-SINGULARITY OBSERVATION.  On `0 < s ≤ u − epsSeq m`,
      `epsSeq m ≤ u − s`, `0 < u − s`, and `(u − s)⁻¹ ≤ (epsSeq m)⁻¹` — the inner-time floor.

    • `secondBoundConst` — the u-uniform (constant-in-`s`) majorant of the family:
      `Csec · (epsSeq m)⁻¹ · C_L · gaussDdim (α·epsSeq m) 0`, with `secondBoundConst_nonneg`.
      The `(epsSeq m)⁻¹` factor is exactly the tamed singular endpoint; the diagonal-peak
      `gaussDdim (α·epsSeq m) 0` is the width-`α·epsSeq m` floor of the width-added convolution
      `α(u−s) + 2s ≥ α·epsSeq m` (`gaussDdim_zero_antitone`).

    • `secondBoundConst_intervalIntegrable` — the `hbdd` slot: a constant is interval-integrable.

    • ★★ `secondOrder_inner_bound_slot` — THE `hbound` SLOT (u-uniform, w-uniform).  From the
      second-order Gaussian domination `hD2` (the `(u−s)⁻¹·gaussDdim(α(u−s))` shape of
      `second_global_of_package`, uniform over the coordinate-line nbhd `snb`) and the source
      Gaussian bound `hF` (`C_L·gaussDdim(2s)`), the inner `z`-pairing is bounded on the truncated
      window by the constant `secondBoundConst`, UNIFORMLY in `s ∈ uIoc 0 (u − epsSeq m)` and
      `w ∈ snb`.  Route: `‖∫‖ ≤ ∫‖·‖ ≤ ∫ (const·two-Gaussian) = const·gaussDdim(α(u−s)+2s) 0`
      (`gaussDdim_selfmul_integral`, widths ADD), then `(u−s)⁻¹ ≤ (epsSeq m)⁻¹` +
      `gaussDdim_zero_antitone` collapse to the single u-uniform constant.  Same architecture as
      `ConvCarriesDischarge.heatConvInner_intervalIntegrable_gaussianDom`, lifted to second order and
      the truncated window.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL.  `hD2`/`hF` are genuine pointwise Gaussian dominations (the shapes delivered by
  `second_global_of_package` / `EngineInstantiation.witnessFieldDeriv_gate_abs_le` and the Levi
  source bound), NONE the conclusion, none vacuous.  The DOMINATION content of the `bound`/`hbdd`/
  `hbound` slots is fully discharged u-uniformly; the singular endpoint is tamed by the truncation.
  NO `sorry`, no new axioms, no `:= True`, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConvCarriesDischarge
import QIQTH.InnerSliceBounds

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Interval Topology

namespace QIQTH.SecondOrderMajorants

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The non-singularity observation on the truncated window.
    ############################################################################### -/

/-- **★ `window_inv_le` — THE NON-SINGULARITY OBSERVATION.**  On the truncated window
    `0 < s ≤ u − epsSeq m`, the inner time is floored: `epsSeq m ≤ u − s`, `0 < u − s`, and the
    singular endpoint is BOUNDED: `(u − s)⁻¹ ≤ (epsSeq m)⁻¹`.  This is exactly why the interchange
    members (which live at the truncations `b = u − epsSeq m`) escape the raw `(u−s)⁻¹` singularity;
    the `ε → 0` limit is handled downstream by the banked sliver / `DaLim` machinery.  NOT
    `a₁ = R/6`. -/
theorem window_inv_le (u : ℝ) (m : ℕ) {s : ℝ}
    (hs : 0 < s) (hsb : s ≤ u - epsSeq m) :
    epsSeq m ≤ u - s ∧ 0 < u - s ∧ (u - s)⁻¹ ≤ (epsSeq m)⁻¹ := by
  have hεm : 0 < epsSeq m := epsSeq_pos m
  have hτε : epsSeq m ≤ u - s := by linarith
  have hτ : 0 < u - s := lt_of_lt_of_le hεm hτε
  have hinv : (u - s)⁻¹ ≤ (epsSeq m)⁻¹ := by
    have := one_div_le_one_div_of_le hεm hτε
    simpa [one_div] using this
  exact ⟨hτε, hτ, hinv⟩

/-! ###############################################################################
    ### The u-uniform majorant of the family.
    ############################################################################### -/

/-- **`secondBoundConst` — THE u-UNIFORM (constant-in-`s`) MAJORANT.**  The single constant that
    dominates the whole truncated-window family:
      `secondBoundConst n Csec C_L α m = Csec · (epsSeq m)⁻¹ · C_L · gaussDdim (α·epsSeq m) 0`.
    The `(epsSeq m)⁻¹` factor is the tamed singular endpoint (`window_inv_le`); the diagonal-peak
    `gaussDdim (α·epsSeq m) 0` is the width-`α·epsSeq m` floor of the added convolution width
    `α(u−s) + 2s ≥ α·epsSeq m`. -/
noncomputable def secondBoundConst (n : ℕ) (Csec C_L α : ℝ) (m : ℕ) : ℝ :=
  Csec * (epsSeq m)⁻¹ * C_L * gaussDdim (α * epsSeq m) (0 : Point n)

/-- `secondBoundConst ≥ 0` (all factors nonnegative: `Csec, C_L ≥ 0`, `(epsSeq m)⁻¹ ≥ 0`, Gaussian
    peak `≥ 0`). -/
theorem secondBoundConst_nonneg (Csec C_L α : ℝ) (m : ℕ)
    (hCsec : 0 ≤ Csec) (hC_L : 0 ≤ C_L) :
    0 ≤ secondBoundConst n Csec C_L α m := by
  unfold secondBoundConst
  have hεm : 0 < epsSeq m := epsSeq_pos m
  exact mul_nonneg (mul_nonneg (mul_nonneg hCsec (inv_nonneg.mpr hεm.le)) hC_L)
    (gaussDdim_nonneg _ _)

/-- **THE `hbdd` SLOT.**  A constant is interval-integrable on `[0, u − epsSeq m]`. -/
theorem secondBoundConst_intervalIntegrable (Csec C_L α : ℝ) (m : ℕ) (u : ℝ) :
    IntervalIntegrable (fun _ : ℝ => secondBoundConst n Csec C_L α m) volume 0 (u - epsSeq m) :=
  intervalIntegrable_const

/-! ###############################################################################
    ### ★★ The `hbound` slot: the truncated-window inner `z`-pairing bound.
    ############################################################################### -/

/-- **★★ `secondOrder_inner_bound_slot` — THE `hbound` SLOT (u-uniform, w-uniform).**  For the
    second-order kernel `D2` (role of `dHH (u−s) (update 0 i w) z`) and the source `F`, from
      • the second-order Gaussian domination `hD2` — the `(u−s)⁻¹·gaussDdim(α(u−s))` shape of
        `second_global_of_package`, UNIFORM over the coordinate-line nbhd `snb`;
      • the source Gaussian bound `hF` — `C_L·gaussDdim(2s)` (the Levi-series envelope),
    the inner `z`-pairing is bounded on the TRUNCATED window `s ∈ uIoc 0 (u − epsSeq m)` by the
    single u-uniform constant `secondBoundConst`, uniformly in `w ∈ snb`:
      `‖∫ z, D2 (u−s) w z · F s z 0‖ ≤ secondBoundConst n Csec C_L α m`.
    ROUTE (mirrors `ConvCarriesDischarge.heatConvInner_intervalIntegrable_gaussianDom`, lifted to
    second order + truncation): `‖∫‖ ≤ ∫‖·‖ ≤ ∫ (c·gaussDdim(α(u−s))·gaussDdim(2s))
    = c·gaussDdim(α(u−s)+2s) 0` (widths ADD, `gaussDdim_selfmul_integral`), then the window floor
    `(u−s)⁻¹ ≤ (epsSeq m)⁻¹` (`window_inv_le`) and the diagonal-peak antitonicity
    `gaussDdim(α(u−s)+2s) 0 ≤ gaussDdim(α·epsSeq m) 0` (`gaussDdim_zero_antitone`) collapse to the
    constant.  `hD2`/`hF` are genuine dominations, NEITHER the conclusion; the singular endpoint is
    tamed by the truncation.  NOT `a₁ = R/6`. -/
theorem secondOrder_inner_bound_slot
    (D2 : ℝ → ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u T α Csec C_L : ℝ) (m : ℕ) (snb : Set ℝ)
    (hu : 0 < u) (huT : u ≤ T) (hα : 0 < α) (hεu : epsSeq m ≤ u)
    (hCsec : 0 ≤ Csec) (hC_L : 0 ≤ C_L)
    (hD2 : ∀ (s : ℝ) (w : ℝ) (z : Point n), 0 < u - s → s ≤ T → w ∈ snb →
        |D2 (u - s) w z| ≤ Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z)
    (hF : ∀ (s : ℝ) (z : Point n), 0 < s → s ≤ T →
        |F s z 0| ≤ C_L * gaussDdim (2 * s) z) :
    ∀ s ∈ Set.uIoc 0 (u - epsSeq m), ∀ w ∈ snb,
      ‖∫ z, D2 (u - s) w z * F s z 0‖ ≤ secondBoundConst n Csec C_L α m := by
  have hεm : 0 < epsSeq m := epsSeq_pos m
  have hb0 : (0 : ℝ) ≤ u - epsSeq m := by linarith
  intro s hsmem w hw
  rw [Set.uIoc_of_le hb0, Set.mem_Ioc] at hsmem
  obtain ⟨hs0, hsb⟩ := hsmem
  obtain ⟨hτε, hτ, hginv⟩ := window_inv_le u m hs0 hsb
  have hsT : s ≤ T := by linarith
  have ha : 0 < α * (u - s) := mul_pos hα hτ
  have hbp : 0 < 2 * s := by linarith
  have hg : Integrable
      (fun z : Point n => gaussDdim (α * (u - s)) z * gaussDdim (2 * s) z) volume :=
    gaussDdim_selfmul_integrable _ _
  have hdomg : Integrable
      (fun z : Point n =>
        Csec * (u - s)⁻¹ * C_L * (gaussDdim (α * (u - s)) z * gaussDdim (2 * s) z)) volume :=
    hg.const_mul _
  -- pointwise: |D2·F| ≤ (Csec·(u−s)⁻¹·C_L)·(gaussDdim(α(u−s))·gaussDdim(2s)).
  have hle : (fun z : Point n => |D2 (u - s) w z * F s z 0|) ≤ᵐ[volume]
      (fun z : Point n =>
        Csec * (u - s)⁻¹ * C_L * (gaussDdim (α * (u - s)) z * gaussDdim (2 * s) z)) := by
    refine ae_of_all _ (fun z => ?_)
    have hD := hD2 s w z hτ hsT hw
    have hFb := hF s z hs0 hsT
    simp only [abs_mul]
    calc |D2 (u - s) w z| * |F s z 0|
        ≤ (Csec * (u - s)⁻¹ * gaussDdim (α * (u - s)) z) * (C_L * gaussDdim (2 * s) z) :=
          mul_le_mul hD hFb (abs_nonneg _)
            (mul_nonneg (mul_nonneg hCsec (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _))
      _ = Csec * (u - s)⁻¹ * C_L * (gaussDdim (α * (u - s)) z * gaussDdim (2 * s) z) := by ring
  have hnn : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[volume]
      (fun z : Point n => |D2 (u - s) w z * F s z 0|) :=
    ae_of_all _ (fun z => abs_nonneg _)
  -- the width-floor collapse to the single u-uniform constant.
  have hgauss : gaussDdim (α * (u - s) + 2 * s) (0 : Point n)
      ≤ gaussDdim (α * epsSeq m) (0 : Point n) := by
    refine gaussDdim_zero_antitone (mul_pos hα hεm) ?_
    have h1 : α * epsSeq m ≤ α * (u - s) := mul_le_mul_of_nonneg_left hτε hα.le
    have h2 : (0 : ℝ) ≤ 2 * s := by linarith
    linarith
  have hcbd : Csec * (u - s)⁻¹ * C_L * gaussDdim (α * (u - s) + 2 * s) (0 : Point n)
      ≤ secondBoundConst n Csec C_L α m := by
    unfold secondBoundConst
    have hcle : Csec * (u - s)⁻¹ * C_L ≤ Csec * (epsSeq m)⁻¹ * C_L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hginv hCsec) hC_L
    have hbnn : 0 ≤ Csec * (epsSeq m)⁻¹ * C_L :=
      mul_nonneg (mul_nonneg hCsec (inv_nonneg.mpr hεm.le)) hC_L
    exact mul_le_mul hcle hgauss (gaussDdim_nonneg _ _) hbnn
  -- assemble.
  calc ‖∫ z, D2 (u - s) w z * F s z 0‖
      ≤ ∫ z, ‖D2 (u - s) w z * F s z 0‖ := norm_integral_le_integral_norm _
    _ = ∫ z, |D2 (u - s) w z * F s z 0| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ z, Csec * (u - s)⁻¹ * C_L * (gaussDdim (α * (u - s)) z * gaussDdim (2 * s) z) :=
          integral_mono_of_nonneg hnn hdomg hle
    _ = Csec * (u - s)⁻¹ * C_L * gaussDdim (α * (u - s) + 2 * s) (0 : Point n) := by
        rw [integral_const_mul, gaussDdim_selfmul_integral (α * (u - s)) (2 * s) ha hbp]
    _ ≤ secondBoundConst n Csec C_L α m := hcbd

end QIQTH.SecondOrderMajorants

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SecondOrderMajorants.window_inv_le
#print axioms QIQTH.SecondOrderMajorants.secondBoundConst_nonneg
#print axioms QIQTH.SecondOrderMajorants.secondBoundConst_intervalIntegrable
#print axioms QIQTH.SecondOrderMajorants.secondOrder_inner_bound_slot
