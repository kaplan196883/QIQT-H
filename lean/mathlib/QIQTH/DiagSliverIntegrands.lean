/-
  DiagSliverIntegrands — J4-811: the FIVE diagonal-sliver integrand integrabilities in ON-GATE
  measurability form — the diagonal (`i = j`) analogue of `MixedSliverIntegrandMeas.integrable_*_onGate`
  (J4-806) at the exact integrand shapes carried by `XUniformSliverFull.witness_sliver2_xuniform`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It discharges the
  five per-slice integrability hypotheses `hIntT1`/`hIntT2`/`hIntT3`/`hInt1`/`hInt2` of the diagonal sliver
  rate `XUniformSliverFull.witness_sliver2_xuniform`, reduced to PURELY ON-GATE data via the shape-agnostic
  gate-compact-support engine `MixedSliverIntegrandMeas.integrable_of_onGate` (J4-806, built on the J4-800
  finite-support engine `integrable_of_finiteSupport_bounded`).

  ## THE MECHANISM (identical to the mixed J4-806; the diagonal shapes differ only in the Hessian bracket
  — a SQUARE `(∑ Y·P)²` and a single Gaussian argument `Y` rather than the mixed PRODUCT `(∑V·Pi)(∑V·Pj)`,
  and the mass moment `(zᵢ² − 2(u−s))` rather than the parity moment `zᵢ zⱼ`).  Each integrand carries the
  amplitude `A0`/`A1`/`A2` `(u−s)` as a LITERAL factor, so off the finite measurable gate `S` — where the
  gated amplitude is `0` — the whole integrand vanishes (`hsupp`, by `ring` after the amplitude support
  hypothesis).  With the on-gate AE-strong-measurability and the on-gate sup-bound carried as hypotheses
  (both chart-continuity-supplied, exactly as in the mixed leg), `integrable_of_onGate` closes each to the
  global `Integrable … volume` shape the sliver rate consumes.

  ## WHAT LANDS (all std-3; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `integrable_hIntT1_onGate` — the E1 Gaussian-replacement Hessian bracket integrand;
    * `integrable_hIntT2_onGate` — the plain-Gaussian Hessian bracket minus the mass moment;
    * `integrable_hIntT3_onGate` — the isolated mass-moment integrand;
    * `integrable_hInt1_onGate`  — `sTerm1 Y P A1 (u−s) z · F`;
    * `integrable_hInt2_onGate`  — `sTerm2 Y A2 (u−s) z · F`.

  Every hypothesis is satisfiable and non-vacuous (`Y=P=Q=0`, `A0=A1=A2=F=0` on `S`, `M=0` gives the
  constant-0 integrand, trivially integrable), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverIntegrandMeas

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.MixedSliverIntegrandMeas
open scoped BigOperators ENNReal

namespace QIQTH.DiagSliverIntegrands

variable {n : ℕ}

/-- **★★ `integrable_hIntT1_onGate`.**  The diagonal `hIntT1` integrand (E1 Gaussian-replacement Hessian
    bracket, in the EXACT shape carried by `witness_sliver2_xuniform`) is integrable from purely on-gate
    data.  NOT `a₁ = R/6`. -/
theorem integrable_hIntT1_onGate
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |(gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
        * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
      * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
          - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hIntT2_onGate`.**  The diagonal `hIntT2` integrand (plain-Gaussian Hessian bracket
    minus the mass moment `(zᵢ² − 2(u−s))/(4(u−s)²)`).  NOT `a₁ = R/6`. -/
theorem integrable_hIntT2_onGate
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, gaussDdim (u - s) z
      * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
          - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
          - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hIntT3_onGate`.**  The diagonal `hIntT3` integrand (the isolated mass-moment
    `((zᵢ² − 2(u−s))/(4(u−s)²))·G_{u−s}(z)·A0·F`).  NOT `a₁ = R/6`. -/
theorem integrable_hIntT3_onGate
    (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt1_onGate`.**  `sTerm1 Y P A1 (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt1_onGate
    (Y P : Point n → Point n) (A1 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => sTerm1 Y P A1 (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |sTerm1 Y P A1 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => sTerm1 Y P A1 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, sTerm1 Y P A1 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [sTerm1]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt2_onGate`.**  `sTerm2 Y A2 (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt2_onGate
    (Y : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A2 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => sTerm2 Y A2 (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |sTerm2 Y A2 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => sTerm2 Y A2 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, sTerm2 Y A2 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [sTerm2]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

end QIQTH.DiagSliverIntegrands

/-! ## Axiom checks — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DiagSliverIntegrands
#print axioms integrable_hIntT1_onGate
#print axioms integrable_hIntT2_onGate
#print axioms integrable_hIntT3_onGate
#print axioms integrable_hInt1_onGate
#print axioms integrable_hInt2_onGate
end AxiomChecks
