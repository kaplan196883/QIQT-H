/-
  WhiteFlowTruncNearWired — J4-736: DISCHARGING the hvLip width wall of
  `QIQTH.WhiteFlowTruncNearClauses.white_flowTruncNear_contr_clause_of_windowLip` (clause (i), the
  contraction leg) by wiring the SHARP σ-interior supplier
  `QIQTH.ExpMap.baseDisplacement_windowed_lipschitz_fixedRadius`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis.  The
  banked `WhiteFlowTruncNearClauses.lean` is NOT edited — this is a strict extension.

  ── WHAT THIS DISCHARGES (the two residues named in `WhiteFlowTruncNearClauses.lean`).
    The banked clause (i), `white_flowTruncNear_contr_clause_of_windowLip`, is assembled modulo an
    abstract window-Lipschitz `hg` with a contraction constant `M < 1`.  Its header records TWO residues
    against supplying `hg` from the concrete bank:
      (a) WIDTH WALL — the σ-interior support `∀ u ∈ closedBall z₀ r, ∀ δ, ‖δ‖ ≤ σ → u+δ ∈ Kset`.
      (b) SMALLNESS — the concrete constant `Dc = M₂·C₀·‖v‖` hidden behind an opaque per-`v` existential,
          so `M < 1` (the `‖v‖→0` vanishing) is not exposed.
    BOTH are dischargeable from the SHARP fixed-radius supplier
    `baseDisplacement_windowed_lipschitz_fixedRadius`, which
      • TAKES the σ-interior support `hKσ` as an explicit hypothesis — so residue (a) is pure wiring; and
      • EXPOSES the constant as `((M₂fix·C₀·‖v‖)·e^{Kc})` with `M₂fix, Kc` **v-independent** — so on the
        sphere `‖v‖ = c` the constant is the SAME for every direction and manifestly `= (B·c).toNNReal`
        with `B := M₂fix·C₀·e^{Kc} ≥ 0`, making the smallness a TRANSPARENT `B·c < 1` (satisfiable as
        `c → 0`), discharging residue (b).

  ── WHAT IS PROVEN HERE (no residual, std-3 axioms).
    * `white_flowTruncNear_contr_clause_wired` — for the concrete curved gate, from the σ-interior
      window support `hKσ` alone, EXPOSES the uniform contraction budget `B ≥ 0` such that:
        - (UNCONDITIONAL) the base-displacement `u ↦ φ_u v − u` is `LipschitzOnWith (B·c).toNNReal` on the
          truncation window `closedBall z₀ r`, for every sphere direction `v ∈ sphere 0 c` — this is
          exactly the `hg` the banked clause needed (residue (a) closed); and
        - (GUARDED BY THE TRANSPARENT SMALLNESS `B·c < 1`) the clamp-centred truncated solver map is
          `ContractingWith (B·c).toNNReal` — clause (i) delivered (residue (b) closed).
      FULLY PROVEN.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteFlowTruncNearClauses
import QIQTH.BaseFlowHderFamilyFixedRadius

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.CurvedA1CenterAmp
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.BaseFlowGlobalContraction
open QIQTH.BaseFlowTruncationWindow
open QIQTH.WhiteFlowTruncNearClauses
open scoped Topology NNReal

namespace QIQTH.WhiteFlowTruncNearWired

variable {n : ℕ}

/-- **★★★ J4-736 — clause (i) at the concrete gate, WIRED (both residues discharged).**
For the concrete curved flow
`φ_q := uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q`, given ONLY the
σ-interior window support `hKσ` (the honest WIDTH-WALL geometric hypothesis) and the reach bound
`c ≤ uniformFlowRadius …`, there is a uniform contraction budget `B ≥ 0` (`B = M₂fix·C₀·e^{Kc}`,
v-independent) such that:

* for EVERY sphere direction `v ∈ sphere 0 c`, the base-displacement `u ↦ φ_u v − u` is
  `LipschitzOnWith (B·c).toNNReal` on the truncation window `closedBall z₀ r` — the once-abstract `hg`,
  now SUPPLIED (residue (a), the width wall, closed by threading `hKσ`); and

* under the TRANSPARENT smallness `B·c < 1` (manifestly true for `c` small — residue (b) closed by the
  exposed linear-in-`‖v‖` constant), for every `v ∈ sphere 0 c` the clamp-centred truncated solver map is
  `ContractingWith (B·c).toNNReal` — exactly the `hflowTruncNear` clause (i).

Proof: instantiate the SHARP `baseDisplacement_windowed_lipschitz_fixedRadius` at the concrete gate; on
the sphere `‖v‖ = c` fold `(M₂fix·C₀·‖v‖)·e^{Kc}` into `(B·c)`; feed the resulting window-Lipschitz into
the banked assembly `white_flowTruncNear_contr_clause_of_windowLip`.  FULLY PROVEN.  ⚠ NOT `a₁ = R/6`. -/
theorem white_flowTruncNear_contr_clause_wired (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (z₀ : Point n) (r c σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hcρ : c ≤ uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc)
    (hKσ : ∀ u ∈ Metric.closedBall z₀ r, ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ Kset) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ v ∈ Metric.sphere (0 : Point n) c,
        LipschitzOnWith (B * c).toNNReal
          (fun u => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc u v - u)
          (Metric.closedBall z₀ r)) ∧
      (B * c < 1 → ∀ v ∈ Metric.sphere (0 : Point n) c,
        ContractingWith (B * c).toNNReal
          (fun w => z₀ -
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w)) := by
  -- the SHARP fixed-radius supplier: v-independent `M₂fix, Kc`, constant linear in `‖v‖`.
  obtain ⟨M₂fix, Kc, hM₂0, hKc0, hfam⟩ :=
    baseDisplacement_windowed_lipschitz_fixedRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc z₀ r σ hr hσ hKσ
  set C₀ : ℝ := uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc with hC₀
  have hC₀0 : 0 ≤ C₀ :=
    uniformFlowConst_nonneg (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  -- the EXPOSED uniform budget `B = M₂fix·C₀·e^{Kc} ≥ 0`.
  have hB0 : 0 ≤ M₂fix * C₀ * Real.exp Kc :=
    mul_nonneg (mul_nonneg hM₂0 hC₀0) (Real.exp_pos Kc).le
  -- the window-Lipschitz `hg`, folded to `(B·c).toNNReal` on the sphere `‖v‖ = c`.
  have hg : ∀ v ∈ Metric.sphere (0 : Point n) c,
      LipschitzOnWith ((M₂fix * C₀ * Real.exp Kc) * c).toNNReal
        (fun u => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc u v - u)
        (Metric.closedBall z₀ r) := by
    intro v hv
    rw [Metric.mem_sphere, dist_zero_right] at hv
    have hvρ : ‖v‖ ≤ uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc := by
      rw [hv]; exact hcρ
    have hL := hfam v hvρ
    have hconst : M₂fix * C₀ * ‖v‖ * Real.exp Kc = (M₂fix * C₀ * Real.exp Kc) * c := by
      rw [hv]; ring
    rwa [hconst] at hL
  refine ⟨M₂fix * C₀ * Real.exp Kc, hB0, hg, ?_⟩
  intro hBc1 v hv
  -- the smallness, now on the EXPOSED constant, converts to `M < 1` in `ℝ≥0`.
  have hM1 : ((M₂fix * C₀ * Real.exp Kc) * c).toNNReal < 1 := by
    have hlt : (((M₂fix * C₀ * Real.exp Kc) * c).toNNReal : ℝ) < 1 := by
      rw [Real.coe_toNNReal']; exact max_lt hBc1 one_pos
    exact_mod_cast hlt
  -- feed the supplied window-Lipschitz into the banked contraction assembly.
  exact white_flowTruncNear_contr_clause_of_windowLip κ hκ hKc z₀ r c hr
    ((M₂fix * C₀ * Real.exp Kc) * c).toNNReal hM1 hg v hv

end QIQTH.WhiteFlowTruncNearWired

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteFlowTruncNearWired
#check @white_flowTruncNear_contr_clause_wired
#print axioms white_flowTruncNear_contr_clause_wired
end AxiomChecks
