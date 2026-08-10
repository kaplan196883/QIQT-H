/-
  CurvedRNCPhaseTransfer — J4-533: the Gaussian-phase transfer `hPhase` for the curved witness `g^K`.

  ## What this discharges

  The assembly `curvedRNC_baseWitness_dom` (`CurvedRNCBaseWitnessDom.lean`) carries, as its LAST
  genuinely-geometric hypothesis, the **Gaussian-phase transfer**

      `hPhase : ∀ z τ, 0 < τ → τ ≤ τmax →
          gaussDdim τ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
            ≤ Cφ · gaussDdim (lam · τ) z` .

  This file proves that transfer for `g^K = curvedRNCMetric K` (`K < 0`, genuinely curved) with the
  EXPLICIT, satisfiable constants `Cφ = (√2)ⁿ`, `lam = 2`, on the reachable collar `z ∈ Kset`,
  `‖z‖ < r` (the residual reach window — see "Honest scope").

  ## The math (and how the Gaussian-phase trap is avoided)

  `gaussDdim t x = (√(4πt))⁻ⁿ · exp(−‖x‖²/(4t))` (closed form `gaussDdim_eq_exp`; `‖x‖² = rncRadialSq x`).
  The transfer needs, after logs, `‖W₀z‖² ≳ ‖z‖²/lam` for the chart image `W₀z = uniformInverseChart …`.
  The trap (Sol #22): `exp(−‖W₀z‖²/4τ) ≤ C·exp(−‖z‖²/4τ)` does NOT follow from `DW(0) = I` alone — it
  needs the EXACT banked radial-distance squeeze.  We use `chartW0_radialSq_half_lower` (itself the
  banked TWO-SIDED near-isometry `chartW0_rncRadialSq_error` on a shrunk ball) which gives the genuine
  curved lower squeeze

      `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)` ,

  i.e. `c²·‖z‖² ≤ ‖W₀z‖²` with `c = √(1/2)`.  Feeding this into the banked exp-free comparison
  `gaussDdim_le_of_norm_ge` (near-isometry ⟹ widened Gaussian, prefactor `c⁻ⁿ = (√2)ⁿ` bookkept
  exactly) gives `gaussDdim τ (W₀z) ≤ (√2)ⁿ · gaussDdim (2τ) z` with NO hand-waved phase.

  ## Honest scope

  `K < 0` is genuinely curved (`Ric(0) = (n−1)K·δ ≠ 0`); the squeeze `(1/2)·r² ≤ r²(W₀z)` TOLERATES a
  genuine radial contraction (`phase_domination_curved_satisfiable`: `W z = (4/5)z` inhabits it), so this
  is NOT secretly the flat statement `W₀z = z`.  The reach window `‖z‖ < r` is the honest residual: it is
  SATISFIABLE (any `z` near `0 ∈ Kset` with `‖z‖ < r`, `r > 0`), reducing `hPhase` to a smaller reachable
  input — the J4-529/531 pattern.  This completes only base-witness domination #1 of ~30–40, and the full
  `a₁ = R/6` additionally needs the entire heatOp/Levi domination pile + the Duhamel assembly.  `a₁ = R/6`
  remains CONDITIONAL and effectively FLAT-ONLY; this does NOT derive the coefficient.
-/
import Mathlib
import QIQTH.CurvedRNCBaseWitnessDom
import QIQTH.GaussCompare
import QIQTH.LayerBChangeVars

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.HeatResidualBound QIQTH.LayerBChangeVars
open scoped BigOperators

namespace QIQTH.CurvedRNCPhaseTransfer

variable {n : ℕ}

/-- **★★ J4-533 — `curvedRNC_phase_transfer`.**  THE CURVED GAUSSIAN-PHASE TRANSFER.  For the
    genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`) there are explicit constants
    `Cφ = (√2)ⁿ > 0`, `lam = 2 > 0` and a reach radius `r > 0` such that, for every base point
    `z ∈ Kset` on the collar `‖z‖ < r` and every `τ` in the window `0 < τ ≤ τmax`, the chart-image
    Gaussian is dominated:

        `gaussDdim τ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
            ≤ Cφ · gaussDdim (lam·τ) z` .

    This is EXACTLY the `hPhase` binder of `curvedRNC_baseWitness_dom`, discharged on the reachable
    window `‖z‖ < r` (the honest residual).  Route: `chartW0_radialSq_half_lower` (the banked two-sided
    near-isometry `chartW0_rncRadialSq_error`) gives the curved radial squeeze `(1/2)·r²(z) ≤ r²(W₀z)`,
    i.e. `(√(1/2))²·r²(z) ≤ r²(W₀z)`; `gaussDdim_le_of_norm_ge` then converts it to the widened Gaussian
    with the exact prefactor `(√(1/2))⁻ⁿ = (√2)ⁿ` — the Gaussian-phase trap is closed by the EXACT
    squeeze, never hand-waved.  NOT `a₁ = R/6` (CONDITIONAL, effectively FLAT-ONLY). -/
theorem curvedRNC_phase_transfer (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (τmax : ℝ) :
    ∃ r > (0 : ℝ), ∃ Cφ > (0 : ℝ), ∃ lam > (0 : ℝ),
      ∀ z ∈ Kset, ‖z‖ < r → ∀ τ : ℝ, 0 < τ → τ ≤ τmax →
        gaussDdim τ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0)
          ≤ Cφ * gaussDdim (lam * τ) z := by
  obtain ⟨r, hr, hhalf⟩ :=
    chartW0_radialSq_half_lower (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
  refine ⟨r, hr, (Real.sqrt 2) ^ n, pow_pos (Real.sqrt_pos.mpr (by norm_num)) n,
    2, by norm_num, ?_⟩
  intro z hz hzr τ hτ _hτmax
  set w := uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z 0 with hwdef
  -- the exact curved radial squeeze `(√(1/2))²·r²(z) ≤ r²(W₀z)` — the banked near-isometry.
  have hc2 : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hcpos : (0 : ℝ) < Real.sqrt (1 / 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hτ2 : (0 : ℝ) < τ / 2 := by positivity
  have hnorm : (Real.sqrt (1 / 2 : ℝ)) ^ 2 * rncRadialSq z ≤ rncRadialSq w := by
    rw [hc2]; exact hhalf z hz hzr
  -- feed the squeeze to the exp-free widened-Gaussian comparison (prefactor `c⁻ⁿ = (√2)ⁿ`).
  have hraw := gaussDdim_le_of_norm_ge (n := n) (c := Real.sqrt (1 / 2 : ℝ)) (τ := τ / 2)
    hcpos hτ2 hnorm
  -- normalize widths `2·(τ/2) → τ`, `2·(τ/2)/(√(1/2))² → 2τ`, and prefactor `(√(1/2))⁻ⁿ → (√2)ⁿ`.
  have hpre : ((Real.sqrt (1 / 2 : ℝ)) ^ n)⁻¹ = (Real.sqrt 2) ^ n := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.sqrt_inv, inv_pow, inv_inv]
  rw [show (2 * (τ / 2)) = τ from by ring, hc2,
      show (τ / (1 / 2 : ℝ)) = 2 * τ from by ring, hpre] at hraw
  exact hraw

/-- **★ J4-533 (satisfiability GATE) — THE TRANSFER DOES NOT FORCE AN ISOMETRY.**  The core radial
    squeeze underlying the transfer, `(1/2)·rncRadialSq z ≤ rncRadialSq (W z)`, is inhabited by a
    GENUINELY radially-distorting map `W z = c·z` with `c = 4/5 ≠ ±1` (`c² = 16/25 ≥ 1/2`) for every
    `z`.  This certifies the phase transfer tolerates the real curved-normal-coordinate radial
    contraction and is NOT secretly the flat `W z = ±z`.  Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curvedRNC_phase_transfer_satisfiable :
    ∃ c : ℝ, c ≠ 1 ∧ c ≠ -1 ∧ ∀ z : Point n,
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (fun i => c * z i) :=
  QIQTH.LayerBChangeVars.phase_domination_curved_satisfiable

end QIQTH.CurvedRNCPhaseTransfer

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedRNCPhaseTransfer

#print axioms curvedRNC_phase_transfer
#print axioms curvedRNC_phase_transfer_satisfiable

end AxiomChecks
