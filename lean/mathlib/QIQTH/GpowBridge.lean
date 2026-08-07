/-
  QIQTH / HeatResidualBound — GpowBridge.lean   (J4-401, Sol #17 A1+A2: the hGpow bridge)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  A-brick pair (Sol consult #17) that bridges the matched-sliver bank into the `MemAdjHi` `hGpow` carry
  of `QIQTH.MemAdjHiSliver.hII_hi_from_sliver`: the pointwise `τ^{-1/2}` bound on the SIGNED `z`-integral
  of the second-`x`-derivative pairing.  No `sorry`/`admit`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SOL #17 VERDICT (followed).  Do NOT start a new second-order moment-cancellation development —
  the matched-sliver bank (`SliverTailMatched` / `SliverOffCollarMatched` / `SliverAssemblyMatched`) IS
  the mechanism.  The raw `‖∂²G_τ‖₁` gives `τ⁻¹`; the CENTER-SUBTRACTION (the Lipschitz factor `|z|`)
  improves to `τ^{-1/2}` — exactly the `SliverBoundOnCollar` `B/√τ` shape.  The banked
  `DaLimEasyTranche` `B√εₘ` is integrated-in-`τ` and CANNOT be inverted to a pointwise bound; we use
  `SliverAssemblyMatched` (per-`τ`) directly.

  ## THE TWO BRICKS.

  ### (A1) `leviSecondPairing_eq_matchedAssembly` — the target-identification bridge (EQUALITY).
  For fixed `τ = u−s > 0`, the full-space signed pairing integral EQUALS the matched-sliver assembly's
  global pairing: the term-1 collar/off-collar matched pair `(∫_{C_τ} H·qz) + (∫_{O_τ} Ichart)` plus the
  gradient term `∫ f₂` plus the mass term `∫ f₃`.  This is the SLOT-CONVERSION / rewriting brick: all
  the chart identifications and the collar/off-collar decomposition happen HERE, with NO estimates.  The
  pointwise integrand identities `hon` (on-collar: the witness = `H·qz + f₂ + f₃`) and `hoff` (off-collar:
  the witness = the chart-native `Ichart + f₂ + f₃`) are the NAMED identification carries — exactly the
  transport normal form / `OnGateGlue` slice identities that the sliver machinery decomposes (and per the
  J4-356 / `DataAmpAssembly` honesty note the off-collar identification is a genuine surviving analytic
  fact, so carrying it is honest and non-vacuous).  Assembled from pure `integral_add` / `integral_add_
  compl` on top of the split helpers `leviPairing_integral_split3` and `matchedTerm1_collar_split`.

  ### (A2) `leviSecondPairing_le_invSqrt` — the pointwise matched bound (ESTIMATE) + m-uniformity.
  Two layers:
    • `leviSecondPairing_inner_bound` — the per-`τ` inner bound: instantiating
      `SliverAssemblyMatched.sliver_term1_full_matched` (term 1, the matched pair) + the terms-2/3
      absolute carries through `SliverAssemblyMatched.sliver_inner_matched_bound` on top of the A1
      identity yields `|∫_z witness·F| ≤ K₁·τ^{-1/2} + K₀` with `K₁ = 2L·(15n/2) + B_comp + Q`,
      `K₀ = S`.
    • `invSqrt_absorb` + `leviSecondPairing_le_invSqrt` — the `m`-uniform absorption to the EXACT `hGpow`
      shape `|·| ≤ Cpair·(u−s)^{-1/2}`.  ⚠ THE QUANTIFIER TRAP: the additive `K₀` is absorbed via
      `K₀ = K₀·√τ·τ^{-1/2} ≤ K₀·√ε*·τ^{-1/2}` using ONLY the FIXED upper endpoint `τ ≤ ε* := epsSeq 0`
      (`epsSeq_antitone`, `epsSeq m ≤ epsSeq 0`).  NEVER a lower bound `τ ≥ εₘ` — that would make `Cpair`
      depend on `m`.  Hence `Cpair := K₁ + K₀·√(epsSeq 0)` is `m`-uniform (chosen BEFORE the `m, s`
      binders).  ⚠ NOT `a₁ = R/6`.

  ## WHAT REMAINS (the A3 = J4-402 handoff).  Instantiating the per-`τ` `hGpow` hypothesis of the
  `m`-uniform capstone with the CONCRETE witness (feeding `DataAmpAssembly`'s `concrete_hqLip_of_carries`
  + `hD2HexpandOn_concrete` into the `qz`/`qc`/`Ichart`/`f₂`/`f₃` slots and the terms-2/3 dominators),
  and closing the single `τ = 0` (`s = u`) measure-zero endpoint of `Set.uIoc`, then packaging into
  `MemAdjHiSliver.hII_hi_from_sliver`.  Documented in `hGpow_bridge_handoff`.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverAssemblyMatched
import QIQTH.ConvApproximants
import QIQTH.GeometricModuliThreading

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.SliverTailMatched QIQTH.SliverOffCollarMatched
open QIQTH.SliverAssemblyMatched
open scoped Interval Topology

namespace QIQTH.GpowBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A1 — the target-identification bridge (the split-equality brick).
    ############################################################################### -/

/-- **★ A1a — `leviPairing_integral_split3`.**  Pure additivity: a full-space integrand that splits
    pointwise as `Wpair = f₁ + f₂ + f₃` (three integrable pieces) has its integral split as the sum of
    the three integrals.  This is the innermost slot-conversion step of the matched assembly; it carries
    NO estimate.  ⚠ NOT `a₁ = R/6`. -/
theorem leviPairing_integral_split3 (Wpair f₁ f₂ f₃ : Point n → ℝ)
    (hpt : ∀ z, Wpair z = f₁ z + f₂ z + f₃ z)
    (h1 : Integrable f₁ volume) (h2 : Integrable f₂ volume) (h3 : Integrable f₃ volume) :
    ∫ z, Wpair z = (∫ z, f₁ z) + (∫ z, f₂ z) + (∫ z, f₃ z) := by
  calc ∫ z, Wpair z
      = ∫ z, (f₁ z + f₂ z + f₃ z) := integral_congr_ae (ae_of_all _ hpt)
    _ = (∫ z, f₁ z + f₂ z) + ∫ z, f₃ z := integral_add (h1.add h2) h3
    _ = (∫ z, f₁ z) + (∫ z, f₂ z) + ∫ z, f₃ z := by rw [integral_add h1 h2]

/-- **★ A1b — `matchedTerm1_collar_split`.**  The term-1 collar/off-collar decomposition (the matched
    pair): a full-space integrand `f₁` that agrees with `Hqz` on the collar `C_R = {‖z‖ ≤ R}` and with
    the chart-native `Ichart` off the collar has its integral split as `(∫_{C_R} Hqz) + (∫_{C_Rᶜ} Ichart)`.
    Pure `integral_add_compl` + `setIntegral_congr_fun`; NO estimate.  This is where the on/off-collar
    slice identities are consumed.  ⚠ NOT `a₁ = R/6`. -/
theorem matchedTerm1_collar_split (R : ℝ) (f₁ Hqz Ichart : Point n → ℝ)
    (hon : ∀ z ∈ collar R, f₁ z = Hqz z)
    (hoff : ∀ z ∈ (collar R)ᶜ, f₁ z = Ichart z)
    (h1 : Integrable f₁ volume) :
    ∫ z, f₁ z = (∫ z in collar R, Hqz z) + (∫ z in (collar R)ᶜ, Ichart z) := by
  rw [← integral_add_compl (collar_measurableSet R) h1]
  congr 1
  · exact setIntegral_congr_fun (collar_measurableSet R) hon
  · exact setIntegral_congr_fun (collar_measurableSet R).compl hoff

/-- **★★★ A1 — `leviSecondPairing_eq_matchedAssembly`.**  THE TARGET-IDENTIFICATION BRIDGE.  For fixed
    `τ > 0`, the full-space signed second-derivative pairing integral `∫_z Wpair` EQUALS the matched-
    sliver assembly's global pairing:
        ∫_z Wpair
          = ((∫_{C_R} H_{τ,i}·qz) + (∫_{C_Rᶜ} Ichart))   -- the matched term-1 pair
            + (∫_z f₂)                                     -- the gradient term
            + (∫_z f₃),                                    -- the mass term
    given the on-collar identity `hon` (witness = `H·qz + f₂ + f₃`) and the off-collar chart-native
    identity `hoff` (witness = `Ichart + f₂ + f₃`).  Route: name `f₁ := Wpair − f₂ − f₃` (integrable),
    which equals `H·qz` on the collar and `Ichart` off it; then `leviPairing_integral_split3` +
    `matchedTerm1_collar_split`.  This is the EQUALITY/rewriting brick — all slot conversions and chart
    identifications live in `hon`/`hoff` (the NAMED, satisfiable transport-normal-form carries), and there
    are NO estimates here.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSecondPairing_eq_matchedAssembly (τ : ℝ) (i : Fin n) (R : ℝ)
    (Wpair qz Ichart f₂ f₃ : Point n → ℝ)
    (hon : ∀ z ∈ collar R, Wpair z = hessGaussFactor i τ z * qz z + f₂ z + f₃ z)
    (hoff : ∀ z ∈ (collar R)ᶜ, Wpair z = Ichart z + f₂ z + f₃ z)
    (hWint : Integrable Wpair volume)
    (hf2 : Integrable f₂ volume) (hf3 : Integrable f₃ volume) :
    ∫ z, Wpair z
      = ((∫ z in collar R, hessGaussFactor i τ z * qz z)
          + (∫ z in (collar R)ᶜ, Ichart z))
        + (∫ z, f₂ z) + (∫ z, f₃ z) := by
  set f₁ : Point n → ℝ := fun z => Wpair z - f₂ z - f₃ z with hf1def
  have hf1int : Integrable f₁ volume := (hWint.sub hf2).sub hf3
  have hpt : ∀ z, Wpair z = f₁ z + f₂ z + f₃ z := by
    intro z; simp only [hf1def]; ring
  have hon1 : ∀ z ∈ collar R, f₁ z = hessGaussFactor i τ z * qz z := by
    intro z hz; simp only [hf1def]; rw [hon z hz]; ring
  have hoff1 : ∀ z ∈ (collar R)ᶜ, f₁ z = Ichart z := by
    intro z hz; simp only [hf1def]; rw [hoff z hz]; ring
  rw [leviPairing_integral_split3 Wpair f₁ f₂ f₃ hpt hf1int hf2 hf3,
    matchedTerm1_collar_split R f₁ (fun z => hessGaussFactor i τ z * qz z) Ichart hon1 hoff1 hf1int]

/-! ###############################################################################
    ### §A2 — the per-`τ` matched inner bound + the `m`-uniform `τ^{-1/2}` absorption.
    ############################################################################### -/

/-- **★★ A2 (inner) — `leviSecondPairing_inner_bound`.**  THE PER-`τ` MATCHED INNER BOUND.  Assembling
    the matched term-1 estimate `SliverAssemblyMatched.sliver_term1_full_matched` (bound
    `|(∫_{C_R} H·qz) + (∫_{C_Rᶜ} Ichart)| ≤ (2L·(15n/2)+B_comp)/√τ`, the `A₀·T_τ`-cancelling matched
    pair) and the terms-2/3 absolute carries (`|∫f₂| ≤ Q/√τ`, `|∫f₃| ≤ S`) through
    `sliver_inner_matched_bound` on top of the A1 identity `leviSecondPairing_eq_matchedAssembly` gives
        |∫_z Wpair| ≤ (2L·(15n/2) + B_comp + Q)·τ^{-1/2} + S.
    This is the `K₁·τ^{-1/2} + K₀` shape consumed by the `m`-uniform absorption.  ⚠ NOT `a₁ = R/6`. -/
theorem leviSecondPairing_inner_bound (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (R : ℝ)
    (Wpair qz qc Ichart f₂ f₃ : Point n → ℝ)
    (L Bcomp Q S : ℝ) (hL : 0 ≤ L)
    (hon : ∀ z ∈ collar R, Wpair z = hessGaussFactor i τ z * qz z + f₂ z + f₃ z)
    (hoff : ∀ z ∈ (collar R)ᶜ, Wpair z = Ichart z + f₂ z + f₃ z)
    (hWint : Integrable Wpair volume) (hf2 : Integrable f₂ volume) (hf3 : Integrable f₃ volume)
    (hqz : ∀ z w, |qz z - qz w| ≤ L * dist z w) (hqzmeas : AEStronglyMeasurable qz volume)
    (hqc : ∀ z w, |qc z - qc w| ≤ L * dist z w) (hqcmeas : AEStronglyMeasurable qc volume)
    (h0 : qz 0 = qc 0)
    (hIchart_int : IntegrableOn Ichart (collar R)ᶜ volume)
    (hcomp : ‖∫ z in (collar R)ᶜ, (Ichart z - hessGaussFactor i τ z * qc z)‖
              ≤ Bcomp / Real.sqrt τ)
    (hf2bound : |∫ z, f₂ z| ≤ Q / Real.sqrt τ) (hf3bound : |∫ z, f₃ z| ≤ S) :
    |∫ z, Wpair z|
      ≤ (2 * L * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + S := by
  have hsplit := leviSecondPairing_eq_matchedAssembly τ i R Wpair qz Ichart f₂ f₃
    hon hoff hWint hf2 hf3
  have hA := sliver_term1_full_matched τ hτ i qz qc Ichart R L Bcomp hL hqz hqzmeas hqc hqcmeas
    h0 hIchart_int hcomp
  refine sliver_inner_matched_bound τ hτ (∫ z, Wpair z)
    ((∫ z in collar R, hessGaussFactor i τ z * qz z) + (∫ z in (collar R)ᶜ, Ichart z))
    (∫ z, f₂ z) (∫ z, f₃ z)
    (2 * L * (15 / 2 * (n : ℝ)) + Bcomp) Q S
    hsplit ?_ hf2bound hf3bound
  rw [← Real.norm_eq_abs]
  exact hA

/-- **★ A2 (absorb) — `invSqrt_absorb`.**  THE ADDITIVE-CONSTANT ABSORPTION.  For `0 < τ ≤ ε*` and a
    signed quantity `val` with `|val| ≤ K₁·τ^{-1/2} + K₀` (`K₀ ≥ 0`), the additive `K₀` is absorbed into
    the leading power using ONLY the FIXED upper endpoint `ε*`:
        K₀ = K₀·(√τ·τ^{-1/2}) = (K₀·√τ)·τ^{-1/2} ≤ (K₀·√ε*)·τ^{-1/2}   (since `√τ ≤ √ε*`),
    so `|val| ≤ (K₁ + K₀·√ε*)·τ^{-1/2}`.  ⚠ THE QUANTIFIER TRAP: this uses `τ ≤ ε*` (upper) and NEVER
    `τ ≥ εₘ` (lower) — so `K₁ + K₀·√ε*` does NOT depend on any per-`m` lower cutoff.  ⚠ NOT `a₁ = R/6`. -/
theorem invSqrt_absorb (τ εstar K₁ K₀ : ℝ) (hτ : 0 < τ) (hτε : τ ≤ εstar)
    (hK₀ : 0 ≤ K₀) (val : ℝ)
    (hval : |val| ≤ K₁ * τ ^ (-(1 : ℝ) / 2) + K₀) :
    |val| ≤ (K₁ + K₀ * Real.sqrt εstar) * τ ^ (-(1 : ℝ) / 2) := by
  have hrpow_nonneg : 0 ≤ τ ^ (-(1 : ℝ) / 2) := (Real.rpow_pos_of_pos hτ _).le
  have hsqrtτ_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hcancel : Real.sqrt τ * τ ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← inv_sqrt_eq_rpow τ hτ]
    exact mul_inv_cancel₀ (ne_of_gt hsqrtτ_pos)
  have hK0eq : K₀ = (K₀ * Real.sqrt τ) * τ ^ (-(1 : ℝ) / 2) := by
    rw [mul_assoc, hcancel, mul_one]
  have hsqle : Real.sqrt τ ≤ Real.sqrt εstar := Real.sqrt_le_sqrt hτε
  have hstep : (K₀ * Real.sqrt τ) * τ ^ (-(1 : ℝ) / 2)
      ≤ (K₀ * Real.sqrt εstar) * τ ^ (-(1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqle hK₀) hrpow_nonneg
  calc |val| ≤ K₁ * τ ^ (-(1 : ℝ) / 2) + K₀ := hval
    _ = K₁ * τ ^ (-(1 : ℝ) / 2) + (K₀ * Real.sqrt τ) * τ ^ (-(1 : ℝ) / 2) := by rw [← hK0eq]
    _ ≤ K₁ * τ ^ (-(1 : ℝ) / 2) + (K₀ * Real.sqrt εstar) * τ ^ (-(1 : ℝ) / 2) := by linarith
    _ = (K₁ + K₀ * Real.sqrt εstar) * τ ^ (-(1 : ℝ) / 2) := by ring

/-- **A2 (window) — `window_tau_pos_lt`.**  On the OPEN Hi window `s ∈ Ioo (u − εₘ) u` the pairing time
    `τ = u − s` is strictly positive and bounded ABOVE by the FIXED `ε* := epsSeq 0` (via
    `epsSeq_antitone : epsSeq m ≤ epsSeq 0`).  The `m`-independence of the upper bound is what makes the
    absorbed constant `m`-uniform.  ⚠ NOT `a₁ = R/6`. -/
theorem window_tau_pos_lt (m : ℕ) (u s : ℝ) (hs : s ∈ Set.Ioo (u - epsSeq m) u) :
    0 < u - s ∧ u - s ≤ epsSeq 0 := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨by linarith, ?_⟩
  have hmono : epsSeq m ≤ epsSeq 0 := epsSeq_antitone (Nat.zero_le m)
  linarith

/-- **★★★ A2 — `leviSecondPairing_le_invSqrt`.**  THE POINTWISE MATCHED BOUND, `m`-UNIFORM.  Given the
    per-`τ` inner bound in the `K₁·(u−s)^{-1/2} + K₀` shape (`K₀, K₁ ≥ 0`, `m`-uniform — supplied
    pointwise by `leviSecondPairing_inner_bound`, and concretely instantiated in A3), there is a SINGLE
    `m`-uniform `Cpair ≥ 0` with
        |Inner m i u s| ≤ Cpair·(u−s)^{-1/2}   on every OPEN Hi window `s ∈ Ioo (u − epsSeq m) u`.
    `Cpair := K₁ + K₀·√(epsSeq 0)` is chosen BEFORE the `m, s` binders (no `εₘ⁻¹` leakage; the
    absorption uses only the fixed upper endpoint `epsSeq 0`).  This is the EXACT `hGpow` carry shape of
    `MemAdjHiSliver.hII_hi_from_sliver` on the open window (the single `τ = 0` endpoint of `uIoc` is the
    A3 residual — see `hGpow_bridge_handoff`).  ⚠ NOT `a₁ = R/6`. -/
theorem leviSecondPairing_le_invSqrt
    (U : Set ℝ) (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (Inner : ℕ → Fin n → ℝ → ℝ → ℝ)
    (hinner : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |Inner m i u s| ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |Inner m i u s| ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  refine ⟨K₁ + K₀ * Real.sqrt (epsSeq 0),
    add_nonneg hK₁ (mul_nonneg hK₀ (Real.sqrt_nonneg _)), ?_⟩
  intro m i u hu s hs
  obtain ⟨hτpos, hτle⟩ := window_tau_pos_lt m u s hs
  exact invSqrt_absorb (u - s) (epsSeq 0) K₁ K₀ hτpos hτle hK₀ (Inner m i u s)
    (hinner m i u hu s hs)

/-! ###############################################################################
    ### §A3 handoff — the census of what J4-402 (A3) must still supply.
    ############################################################################### -/

/-- **`hGpow_bridge_handoff`.**  THE A3 (= J4-402) HANDOFF CENSUS.  A genuine conjunction (non-vacuous
    plumbing witness) enumerating what the concrete-witness closure of `MemAdjHiSliver`'s `hGpow` still
    consumes AFTER this A1+A2 bridge:
      1. `hconcrete`  — instantiating the `qz`/`qc`/`Ichart`/`f₂`/`f₃` slots of
         `leviSecondPairing_inner_bound` with the CONCRETE van-Vleck witness pairing at every
         `τ = u − s`, feeding `DataAmpAssembly.concrete_hqLip_of_carries` +
         `SliverBoundOnCollar.sliverIntegrand_on_collar` (`hD2HexpandOn_concrete`) into `hon`/`hoff` and
         the term-2/3 Gaussian-moment dominators into `hf2bound`/`hf3bound`;
      2. `hKnonneg`   — the leading/mass constants `K₁ = 2L·(15n/2)+B_comp+Q ≥ 0` and `K₀ = S ≥ 0`
         (all constituents nonneg), so `leviSecondPairing_le_invSqrt` applies with an `m`-uniform `Cpair`;
      3. `hendpoint`  — the single `τ = 0` (`s = u`) endpoint of `Set.uIoc (u−εₘ) u`: since `hGpow` is
         stated pointwise on `uIoc` (which includes `s = u`, measure zero), the concrete pairing at
         `τ = 0` must be shown to satisfy `|·| ≤ Cpair·0^{-1/2} = 0` (the witness's `τ = 0` value), OR
         the `MemAdjHi` domination re-routed through the a.e.-on-`uIoc` `intervalIntegrable_of_aesm_le`
         (the endpoint is irrelevant to integrability — see `MemAdjHiSliver`'s `τ = 0` endpoint verdict).
    Each conjunct is SATISFIABLE and none is the conclusion.  ⚠ NOT `a₁ = R/6`; the closure is
    CONDITIONAL on exactly this census. -/
def hGpow_bridge_handoff (hconcrete hKnonneg hendpoint : Prop) : Prop :=
  hconcrete ∧ hKnonneg ∧ hendpoint

/-- The A3-handoff census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_bridge_handoff_intro {hconcrete hKnonneg hendpoint : Prop}
    (h1 : hconcrete) (h2 : hKnonneg) (h3 : hendpoint) :
    hGpow_bridge_handoff hconcrete hKnonneg hendpoint :=
  ⟨h1, h2, h3⟩

end QIQTH.GpowBridge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.GpowBridge.leviPairing_integral_split3
#print axioms QIQTH.GpowBridge.matchedTerm1_collar_split
#print axioms QIQTH.GpowBridge.leviSecondPairing_eq_matchedAssembly
#print axioms QIQTH.GpowBridge.leviSecondPairing_inner_bound
#print axioms QIQTH.GpowBridge.invSqrt_absorb
#print axioms QIQTH.GpowBridge.window_tau_pos_lt
#print axioms QIQTH.GpowBridge.leviSecondPairing_le_invSqrt
#print axioms QIQTH.GpowBridge.hGpow_bridge_handoff_intro
