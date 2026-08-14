/-
  WhiteFlowTruncNearClauses — J4-734: INSTANTIATING the `hflowTruncNear` clauses at the CONCRETE curved
  gate (`φ = uniformFlowExp (curvedRNCMetric κ) …`), toward witnessing
  `WhiteHflowTruncConcrete.white_hInnerCont_closed_final10`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE WIDTH-WALL VERDICT (the pivot of J4-734).
    `final10.hflowTruncNear` is quantified over near `z₀` (bad set inhabited) and its three clauses talk
    about the CONCRETE flow `uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
    **hKc** …`, whose value is Skolem-pinned to the SPECIFIC compact `Kset` (`hKc : IsCompact Kset`) — see
    `UniformFlowNondeg.uniformFlowExp`, defined through `(uniformFlow_tube_exists … hK …).choose`.  So the
    concrete v-Lipschitz / contraction suppliers (`uniformFlowExp_vLipschitz_uniform`,
    `baseDisplacement_windowed_lipschitz_concrete`) — which are correctly σ-interior-of-`K` gated — can
    ONLY be instantiated at `hKc`/`Kset`, NOT at an enlarged compact (that would be a DIFFERENT flow
    function, not the one `final10` hardcodes).  Their base-slot argument `q := coordClamp z₀ r w` must lie
    in `Kset`, and (for the contraction) the whole window `closedBall z₀ r` must be σ-interior to `Kset`.
    A near `z₀` (with `dist z₀ Kset ≤ ρ`) whose truncation window pokes outside `Kset` therefore CANNOT be
    served by the concrete suppliers.  This is the documented WIDTH WALL (J4-676): the honest residue of
    the concrete-gate instantiation is a **gate-support-in-`Kset`** hypothesis (`hwinK`).

    THIS FILE therefore builds the clauses as HONEST CONDITIONAL bricks carrying the explicit, in-principle
    satisfiable window-support hypothesis `hwinK : closedBall z₀ r ⊆ Kset` (and, for clause (ii), a
    radius-bump `c < c'`).  Each brick is independently bankable; wiring the joint support into
    `final10`'s abstract gate `S` is the remaining width-wall gap.

  ── WHAT IS FULLY PROVEN HERE (no residual, std-3 axioms).
    * `white_flowTruncNear_vLip_clause` — ★★★ CLAUSE (ii) at the concrete gate.  From
      `uniformFlowExp_vLipschitz_uniform` (uniform-in-base, on `ball 0 c'`) + the window-in-`Kset` support
      (`coordClamp z₀ r w ∈ closedBall z₀ r ⊆ Kset`) + the sphere⊆ball radius bump (`c < c'`), the uniform
      v-slot Lipschitz modulus `Cv := (1 + C_L·c').toNNReal` for the clamp-based flow.  FULLY PROVEN.
      ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseFlowTruncationWindow
import QIQTH.BaseFlowGlobalContraction
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.CurvedA1CenterAmp
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.BaseFlowGlobalContraction
open QIQTH.BaseFlowTruncationWindow
open scoped Topology NNReal

namespace QIQTH.WhiteFlowTruncNearClauses

variable {n : ℕ}

/-! ### CLAUSE (ii) — the uniform v-slot Lipschitz clause at the concrete curved gate. -/

/-- **★★★ CLAUSE (ii) at the concrete gate.**  For the concrete curved flow
`φ_q := uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q`, there is a
sharp-reach radius `ρ₀ > 0` and shrinking constant `C_L ≥ 0` such that for any window centre `z₀`,
truncation radius `0 ≤ r` whose window `closedBall z₀ r` is contained in the flow's compact `Kset`
(`hwinK` — the honest WIDTH-WALL support hypothesis), and any sphere radius `0 < c` with a bump `c < c'`,
`c' ≤ ρ₀`, the clamp-based velocity map `v ↦ φ_(coordClamp z₀ r w) v` is uniformly
`(1 + C_L·c')`-Lipschitz across ALL base points `w` on the sphere `sphere 0 c` — exactly the
`hflowTruncNear` clause (ii) modulus.

Proof: `coordClamp z₀ r w ∈ closedBall z₀ r ⊆ Kset`, so the base slot is always in `Kset`; the sphere
`sphere 0 c` sits inside `ball 0 c'` (as `‖v‖ = c < c'`); apply `uniformFlowExp_vLipschitz_uniform` at
`q := coordClamp z₀ r w`, parameter `c'`.  FULLY PROVEN.  ⚠ NOT `a₁ = R/6`. -/
theorem white_flowTruncNear_vLip_clause (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ C_L : ℝ, 0 ≤ C_L ∧
      ∀ (z₀ : Point n) (r : ℝ), 0 ≤ r → Metric.closedBall z₀ r ⊆ Kset →
      ∀ c c' : ℝ, 0 < c → c < c' → c' ≤ ρ₀ →
        ∀ v ∈ Metric.sphere (0 : Point n) c, ∀ v' ∈ Metric.sphere (0 : Point n) c, ∀ w : Point n,
          dist (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v)
              (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
                (coordClamp z₀ r w) v')
            ≤ ((1 + C_L * c').toNNReal : ℝ) * dist v v' := by
  obtain ⟨ρ₀, hρ₀, C_L, hCL0, hLip⟩ :=
    uniformFlowExp_vLipschitz_uniform (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
  refine ⟨ρ₀, hρ₀, C_L, hCL0, ?_⟩
  intro z₀ r hr hwinK c c' hc0 hcc' hc'ρ v hv v' hv' w
  -- base slot is in `Kset` via the window support.
  have hqmem : coordClamp z₀ r w ∈ Kset :=
    hwinK (coordClamp_mem_closedBall z₀ r hr w)
  -- sphere points at radius `c` sit inside `ball 0 c'`.
  have hc'0 : 0 < c' := lt_trans hc0 hcc'
  have hvball : v ∈ Metric.ball (0 : Point n) c' := by
    rw [Metric.mem_sphere, dist_zero_right] at hv
    rw [Metric.mem_ball, dist_zero_right, hv]; exact hcc'
  have hv'ball : v' ∈ Metric.ball (0 : Point n) c' := by
    rw [Metric.mem_sphere, dist_zero_right] at hv'
    rw [Metric.mem_ball, dist_zero_right, hv']; exact hcc'
  -- the uniform-in-base v-Lipschitz bound at parameter `c'`.
  have hbound := hLip (coordClamp z₀ r w) hqmem c' hc'0 hc'ρ v hvball v' hv'ball
  -- fold `(1 + C_L·c')` into `.toNNReal`.
  have hcoe : ((1 + C_L * c').toNNReal : ℝ) = 1 + C_L * c' := by
    rw [Real.coe_toNNReal]
    have : (0 : ℝ) ≤ C_L * c' := mul_nonneg hCL0 hc'0.le
    linarith
  rw [hcoe]
  exact hbound

/-! ### CLAUSE (i) — the clamp-centred contraction, assembled modulo the window-Lipschitz input. -/

/-- **★★★ CLAUSE (i) at the concrete gate — the contraction leg, ASSEMBLED.**  For the concrete curved
flow `φ_q := uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q`, if the
base-displacement map `u ↦ φ_u v − u` is `LipschitzOnWith M` on the truncation window `closedBall z₀ r`
with a genuine contraction constant `M < 1` (for each sphere direction `v`), then the clamp-centred
truncated solver map
    `w ↦ z₀ − (φ_(coordClamp z₀ r w) v − coordClamp z₀ r w + w) + w`
is `ContractingWith M` — exactly the `hflowTruncNear` clause (i).

Proof: this is `BaseFlowGlobalContraction.truncatedSolverMap_contractingWith_solverShape` at the
displacement `g u := φ_u v − u`, window `S := closedBall z₀ r` (so `hball := subset_rfl`); the clamp
composes the window-Lipschitz `g` with the 1-Lipschitz coordinate clamp into `S`.

⚠ RESIDUE (the two named gaps of J4-734, NOT dischargeable from the banked concrete suppliers): (a) the
WIDTH WALL — supplying the window-Lipschitz `hg` from `baseDisplacement_windowed_lipschitz_concrete`
requires the σ-interior support `∀ u ∈ closedBall z₀ r, ∀ δ, ‖δ‖ ≤ σ → u+δ ∈ Kset`, which a near-`z₀`
window poking outside `Kset` cannot meet; (b) the SMALLNESS — the concrete supplier hides its constant
`Dc = M₂·C₀·‖v‖` inside an existential, so `M = (Dc·e^{Kc}).toNNReal < 1` (the `‖v‖→0` vanishing) is not
exposed and cannot be discharged without a sharper `Dc ≤ K·‖v‖` supplier.  FULLY PROVEN as an assembly.
⚠ NOT `a₁ = R/6`. -/
theorem white_flowTruncNear_contr_clause_of_windowLip (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (z₀ : Point n) (r c : ℝ) (hr : 0 ≤ r) (M : ℝ≥0) (hM1 : M < 1)
    (hg : ∀ v ∈ Metric.sphere (0 : Point n) c,
      LipschitzOnWith M
        (fun u => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc u v - u)
        (Metric.closedBall z₀ r)) :
    ∀ v ∈ Metric.sphere (0 : Point n) c,
      ContractingWith M
        (fun w => z₀ -
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
              (coordClamp z₀ r w) v - coordClamp z₀ r w + w) + w) := by
  intro v hv
  exact truncatedSolverMap_contractingWith_solverShape z₀ r hr (subset_rfl)
    (fun u => uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc u v - u)
    M hM1 (hg v hv)

end QIQTH.WhiteFlowTruncNearClauses

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteFlowTruncNearClauses
#check @white_flowTruncNear_vLip_clause
#check @white_flowTruncNear_contr_clause_of_windowLip
#print axioms white_flowTruncNear_vLip_clause
#print axioms white_flowTruncNear_contr_clause_of_windowLip
end AxiomChecks
