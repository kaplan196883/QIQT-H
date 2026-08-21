/-
  FlatChartBridgeAudit — a machine-checked STATEMENT-SHAPE audit of the geodesic-pullback bridge
  `hpull` carried by `RadialGaugeInterface.abstract_centerIdentities_of_gaussPullback` and
  `CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY / SCOPE FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, proves NOTHING new about `R/6`, and
  DISCHARGES NEITHER `hpull` NOR any member of `{hDuhamel, hDConv, hCConv}`.  It is a *regression /
  countermodel* audit: it converts a previously-symbolic (sympy) finding into a machine-checked Lean
  fact about the SHAPE of the `hpull` statement, in a CONCRETE flat model.

  It EXPLICITLY does **not**:
    • identify the concrete affine chart `Wf z := (· - z)` with the opaque `.choose`-built
      `uniformInverseChart` (that identification is exactly the unproven z-slot germ, blocker J3);
    • solve J3, the Gauss lemma, or any Riemannian-geometry infrastructure;
    • validate the r-corrected bridge in the CURVED case (the flat metric is constant, so it cannot
      distinguish `g(z)` from `g(r)`, and `g = gi`, `Q = 0` degenerate the `VQ` leg to `0 = 0`).

  ## WHAT IT DOES (all machine-checked, all with the ACTUAL grounded jets of the affine chart).
  The real `hpull` (base `z`, index `i`; `W z` = geodesic inverse chart `exp_z⁻¹`; `P = ∂ᵢ W z`,
  `Q = ∂ᵢ² W z`, both at argument `0`) has three legs whose intended conclusions are:
      `hpullVP  : ∑ₖ (W z 0)ₖ · Pₖ = ∑ⱼ g_{ij}(z)·zʲ`   ⇒ conclusion `= zᵢ`
      `hpullPsq : ∑ₖ Pₖ² = g_{ii}(0)`                    ⇒ conclusion `= 1`
      `hpullVQ  : ∑ₖ (W z 0)ₖ · Qₖ = (∑ⱼ g_{ij}(z)·zʲ) − (∑ⱼ gi_{ij}(z)·zʲ)`  ⇒ conclusion `= 0`.

  In the FLAT model the geodesics are straight lines, so `exp_z(v) = z + v` and the flat geodesic
  inverse chart is the affine map `W_z(x) = x − z`.  We define exactly this chart, GROUND its jets as
  its ACTUAL Fréchet derivatives (`flatFirstJet` from `fderiv`, `flatSecondJet` from the second
  `fderiv`), and machine-check:

    (A) `flat_VP_lhs` — the chart-side contraction is `∑ₖ (W z 0)ₖ · Pₖ = (W z 0)ᵢ`, and
        `Wf_center_apply` gives `(W z 0)ᵢ = −zᵢ`.  So the NATURAL right-hand side of `hpullVP` is
        `(W z 0)ᵢ = −zᵢ`, i.e. the RADIAL VECTOR `r := W z 0`, NOT `+zᵢ`.

    (B) `current_hpullVP_fails` — ★ the CURRENT-shape `hpullVP` (RHS `∑ⱼ g_{ij}(z)·zʲ = zᵢ`) is
        REFUTED for the actual affine jets at the concrete instance `n = 1`, `z = (1)`, `i = 0`:
        LHS `= −1`, RHS `= +1`, `−1 ≠ 1`.  Hence the current bridge is NOT uniformly valid for the
        genuine flat geodesic-inverse jets — it is mis-signed (it holds only where `zᵢ = 0`, e.g. the
        centre `z = 0`), NOT merely "unproven".

    (C) `flat_corrected_bridge` + `flat_center_identities` — the `r`-CORRECTED shape (RHS contracts
        the metric AT `r := W z 0`, the `VP` conclusion reading `= (W z 0)ᵢ`) holds for ALL `n z i`
        with the actual grounded jets: it PASSES the flat-affine consistency test and is realized by
        genuine derivatives (non-vacuous), whereas the current shape is not.

  ## PRECISE STATUS.  This file establishes the sign/vector DEFECT in the current `hpull` statement as
  a machine-checked fact of the flat model, and shows the `r`-corrected shape is self-consistent there.
  It does not prove the corrected bridge in general and does not touch the opaque chart.
  ⚠  a₁ = R/6 remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`; any route through the
  center-identity implication lemmas additionally retains their `hpull` hypothesis, UNCHANGED.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Curvature

open Finset
open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.FlatChartBridgeAudit

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the CONCRETE flat model: affine chart, its grounded jets, and `δ` metric.
    ############################################################################### -/

/-- **The flat geodesic inverse chart** `W_z(x) = x − z`.  In the flat model geodesics are straight
    lines (`exp_z(v) = z + v`), so `exp_z⁻¹(x) = x − z`.  This is the CONCRETE stand-in for the opaque
    `uniformInverseChart`; the file does NOT claim they are equal (that is blocker J3). -/
def Wf (z : Point n) : Point n → Point n := fun x => x - z

/-- **The grounded first jet** `P = ∂ᵢ W_z` at argument `0`: the `k`-component of the Fréchet
    derivative of `Wf z` at `0` applied to the `i`-th basis direction. -/
noncomputable def flatFirstJet (z : Point n) (i : Fin n) : Fin n → ℝ :=
  fun k => (fderiv ℝ (fun x : Point n => x - z) 0) (Pi.single i (1 : ℝ)) k

/-- **The grounded second jet** `Q = ∂ᵢ² W_z` at argument `0`: the `k`-component of the second
    Fréchet derivative of `Wf z` in the `i`-th direction. -/
noncomputable def flatSecondJet (z : Point n) (i : Fin n) : Fin n → ℝ :=
  fun k => (fderiv ℝ
      (fun x : Point n => (fderiv ℝ (fun x' : Point n => x' - z) x) (Pi.single i (1 : ℝ))) 0)
      (Pi.single i (1 : ℝ)) k

/-- **The flat metric / inverse metric** `δ_{ij}` (constant, `g = gi`). -/
def flatMetric (_ : Point n) (i j : Fin n) : ℝ := if i = j then 1 else 0

/-! ###############################################################################
    ### §2 — grounding lemmas: the actual chart value and jets of the affine model.
    ############################################################################### -/

/-- The Fréchet derivative of the affine chart `Wf z = (· - z)` is the identity at every point. -/
theorem Wf_hasFDeriv (z : Point n) (x : Point n) :
    HasFDerivAt (fun x' : Point n => x' - z) (ContinuousLinearMap.id ℝ (Point n)) x := by
  simpa using (hasFDerivAt_id (𝕜 := ℝ) x).sub_const z

/-- **Chart value at the ambient origin**: `W_z(0) = −z` (componentwise `(W z 0)ᵢ = −zᵢ`). -/
theorem Wf_center_apply (z : Point n) (i : Fin n) : (Wf z 0) i = - z i := by
  simp [Wf]

/-- **First jet is the Kronecker delta**: `P₀ₖ = δ_{ki}` (grounded in the actual `fderiv`). -/
theorem flatFirstJet_eq (z : Point n) (i k : Fin n) :
    flatFirstJet z i k = if k = i then 1 else 0 := by
  unfold flatFirstJet
  rw [(Wf_hasFDeriv z 0).fderiv, ContinuousLinearMap.id_apply, Pi.single_apply]

/-- **Second jet vanishes**: `Qₖ = 0` (grounded — the second `fderiv` of an affine map is `0`). -/
theorem flatSecondJet_eq (z : Point n) (i k : Fin n) : flatSecondJet z i k = 0 := by
  have hconst : (fun x : Point n => (fderiv ℝ (fun x' : Point n => x' - z) x) (Pi.single i 1))
      = (fun _ : Point n => (Pi.single i (1 : ℝ))) := by
    funext x
    rw [(Wf_hasFDeriv z x).fderiv, ContinuousLinearMap.id_apply]
  unfold flatSecondJet
  rw [hconst]
  simp

/-! ###############################################################################
    ### §3 — the metric contraction and the chart-side `VP` contraction.
    ############################################################################### -/

/-- **Metric radial contraction (flat)**: `∑ⱼ δ_{ij}·wʲ = wᵢ` for any vector `w`.  Instantiated at
    `w = z` this is the CURRENT `hpullVP` RHS (`= zᵢ`); at `w = W z 0 = r` it is the r-CORRECTED RHS
    (`= rᵢ`). -/
theorem flat_metricContract (w : Point n) (i : Fin n) :
    (∑ j, flatMetric w i j * w j) = w i := by
  simp only [flatMetric, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **★ Chart-side `VP` contraction**: `∑ₖ (W z 0)ₖ · P₀ₖ = (W z 0)ᵢ`.  The NATURAL right-hand side is
    the radial vector component `(W z 0)ᵢ`, which by `Wf_center_apply` equals `−zᵢ` — NOT `+zᵢ`.  This
    is the crux of the sign audit. -/
theorem flat_VP_lhs (z : Point n) (i : Fin n) :
    (∑ k, (Wf z 0) k * flatFirstJet z i k) = (Wf z 0) i := by
  simp only [flatFirstJet_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-! ###############################################################################
    ### §4 — ★ the CURRENT-shape `hpullVP` is REFUTED for the actual affine jets.
    ############################################################################### -/

/-- **★ `current_hpullVP_fails`.**  The CURRENT-shape `hpullVP` — `∑ₖ (W z 0)ₖ · P₀ₖ = ∑ⱼ g_{ij}(z)·zʲ`
    — is FALSE for the actual flat geodesic-inverse jets at the concrete instance `n = 1`,
    `z = (fun _ => 1)`, `i = 0`: the LHS is `(W z 0)₀ = −1` while the RHS is `z₀ = +1`.  So the current
    bridge statement is mis-signed (holds only where `zᵢ = 0`), NOT merely unproven.  This is the
    machine-checked form of the sympy sign finding.  ⚠ NOT `a₁ = R/6`; does not touch the opaque
    chart. -/
theorem current_hpullVP_fails :
    ¬ ((∑ k, (Wf (fun _ => 1 : Point 1) 0) k * flatFirstJet (fun _ => 1 : Point 1) 0 k)
        = (∑ j, flatMetric (fun _ => 1 : Point 1) 0 j * (fun _ => 1 : Point 1) j)) := by
  rw [flat_VP_lhs, flat_metricContract, Wf_center_apply]
  norm_num

/-! ###############################################################################
    ### §5 — ★ the r-CORRECTED shape is self-consistent for the actual affine jets.
    ############################################################################### -/

/-- **★ `flat_corrected_bridge`.**  The `r`-CORRECTED bridge legs (RHS contracting the metric AT the
    radial vector `r := W z 0`) hold for the actual affine jets, ALL `n z i`:
      • `VP`  : `∑ₖ (W z 0)ₖ · P₀ₖ = ∑ⱼ g_{ij}(r)·rʲ`   (both sides `= (W z 0)ᵢ`);
      • `Psq` : `∑ₖ P₀ₖ² = g_{ii}(0)`                    (both sides `= 1`);
      • `VQ`  : `∑ₖ (W z 0)ₖ · Qₖ = (∑ⱼ g_{ij}(r)·rʲ) − (∑ⱼ gi_{ij}(r)·rʲ)`  (both sides `= 0`).
    Concrete equalities with genuine derivatives — non-vacuous; the corrected shape PASSES the
    flat-affine consistency test.  ⚠ NOT a general/curved proof (flat `g` is constant, `g = gi`). -/
theorem flat_corrected_bridge (z : Point n) (i : Fin n) :
    ((∑ k, (Wf z 0) k * flatFirstJet z i k)
        = ∑ j, flatMetric (Wf z 0) i j * (Wf z 0) j) ∧
    ((∑ k, flatFirstJet z i k ^ 2) = flatMetric (0 : Point n) i i) ∧
    ((∑ k, (Wf z 0) k * flatSecondJet z i k)
        = (∑ j, flatMetric (Wf z 0) i j * (Wf z 0) j)
            - (∑ j, flatMetric (Wf z 0) i j * (Wf z 0) j)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [flat_VP_lhs, flat_metricContract]
  · simp only [flatFirstJet_eq, flatMetric]
    have hsq : ∀ k : Fin n, (if k = i then (1 : ℝ) else 0) ^ 2 = if k = i then (1 : ℝ) else 0 := by
      intro k; by_cases h : k = i <;> simp [h]
    rw [Finset.sum_congr rfl (fun k _ => hsq k)]
    simp [Finset.sum_ite_eq']
  · rw [sub_self]
    simp only [flatSecondJet_eq, mul_zero, Finset.sum_const_zero]

/-- **★ `flat_center_identities`.**  The three CENTER IDENTITIES (conclusions of the bridge lemmas), in
    the r-CORRECTED `VP` form, hold for the actual affine jets, ALL `n z i`:
      • `∑ₖ (W z 0)ₖ · P₀ₖ = (W z 0)ᵢ`   (the corrected conclusion — `= rᵢ = −zᵢ`, NOT `+zᵢ`);
      • `∑ₖ P₀ₖ² = 1`;
      • `∑ₖ (W z 0)ₖ · Qₖ = 0`.
    Non-vacuous (genuine derivatives).  ⚠ NOT `a₁ = R/6`. -/
theorem flat_center_identities (z : Point n) (i : Fin n) :
    (∑ k, (Wf z 0) k * flatFirstJet z i k = (Wf z 0) i) ∧
    (∑ k, flatFirstJet z i k ^ 2 = 1) ∧
    (∑ k, (Wf z 0) k * flatSecondJet z i k = 0) := by
  refine ⟨flat_VP_lhs z i, ?_, ?_⟩
  · simp only [flatFirstJet_eq]
    have hsq : ∀ k : Fin n, (if k = i then (1 : ℝ) else 0) ^ 2 = if k = i then (1 : ℝ) else 0 := by
      intro k; by_cases h : k = i <;> simp [h]
    rw [Finset.sum_congr rfl (fun k _ => hsq k)]
    simp [Finset.sum_ite_eq']
  · simp only [flatSecondJet_eq, mul_zero, Finset.sum_const_zero]

end QIQTH.FlatChartBridgeAudit

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.FlatChartBridgeAudit.Wf_center_apply
#print axioms QIQTH.FlatChartBridgeAudit.flatFirstJet_eq
#print axioms QIQTH.FlatChartBridgeAudit.flatSecondJet_eq
#print axioms QIQTH.FlatChartBridgeAudit.flat_VP_lhs
#print axioms QIQTH.FlatChartBridgeAudit.current_hpullVP_fails
#print axioms QIQTH.FlatChartBridgeAudit.flat_corrected_bridge
#print axioms QIQTH.FlatChartBridgeAudit.flat_center_identities
