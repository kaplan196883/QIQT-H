/-
  AmpFieldGeneralPointBoundLipschitz — J4-1025: the concrete on-gate amplitude `chartFieldAmp` is
  BOUNDED and (genuinely, with an explicit constant) LIPSCHITZ on a ball around a GENERAL FIXED field
  point `x` — the exact composable piece `cp911` flagged as missing (item (1) of the two-item scope map
  for closing `nb`'s term1, `hsMixed·A` with `A = chartFieldAmp`, at the literal amplitude).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ## WHAT WAS MISSING (cp911).
  `AmplitudeFamilyDischarge.amp_bound_general` / `amp_deriv_bound_general` give BOUNDS only, and only on
  a ball around the FIELD CENTRE `0` (the `bound_of_continuousAt` helper there is hard-coded to
  `Metric.closedBall 0 r`).  `OnGateJets.ampField_contDiffAt` gives `ContDiffAt ℝ 2` of `chartFieldAmp`
  at a GENUINELY GENERAL field point `p`, but nothing downstream turned that into a bound+Lipschitz pair
  AT that general `p`.  Nothing of this exact shape existed.

  ## WHAT LANDS.
  `chartFieldAmp_bound_lipschitz_generalPoint` — ★★★ for a GENERAL FIXED field point `p`, given the
  SAME two honest carries `OnGateJets.ampField_contDiffAt` already needs (`hWz : ContDiffAt ℝ 2 (W z) p`,
  `hdetz : 0 < det g (W z p)`), there is a ball `ball p r` on which `chartFieldAmp … z` is:
    • pairwise LIPSCHITZ with an explicit nonnegative constant `L`
      (`∀ x y ∈ ball p r, |A x - A y| ≤ L * dist x y`), and
    • BOUNDED by an explicit constant `M` (`∀ x ∈ ball p r, |A x| ≤ M`), with `M` built directly from
      the Lipschitz fact (`M := |A p| + L * r`, via the triangle inequality — no separate continuity
      argument needed).

  Route: EXACTLY the port cp911 called for — `ampField_contDiffAt` (`C²` at `p`) `.of_le` gives
  `ContDiffAt ℝ 1 (chartFieldAmp … z) p`; feed the ALREADY-GENERAL-BASEPOINT convex-MVT Lipschitz helper
  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge.contDiffAt_one_lipschitzOn_ball_atPoint`
  (banked by J4-1024 for the UNRELATED V/Jacobian mechanism, but stated for an abstract `f : E → F` at an
  abstract basepoint `p` — it composes here VERBATIM, no re-derivation needed). Boundedness on the same
  ball is then a two-line corollary of the Lipschitz bound (no need to re-derive `bound_of_continuousAt`
  at a shifted centre). This is a MECHANICAL COMPOSITION of two already-banked, already-general-basepoint
  facts — confirmed by `gpt-5.6-sol` (high) before writing any Lean: no genuinely new mathematical content,
  only assembly.

  ## HONEST SCOPE — WHAT THIS DOES **NOT** DO.
  This is LOCAL (a ball `ball p r` with `r` depending on `p`), matching cp911's item (1) exactly. It does
  NOT supply the GLOBAL (all of `Point n`) bound+Lipschitz fact that `nb`'s term1 literal closure needs —
  that is cp911's SEPARATE item (2), a ball→global truncation argument (analogous to, but distinct from,
  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s own §D truncation of the V/Jacobian ratio),
  left to a FUTURE dispatch. `Bfac`'s other three summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) and the
  `Levi(s,z)` prefactor remain entirely untouched. `fb` (far carry) remains separately open. `a₁ = R/6`
  remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.

  NO `sorry`, NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, none equal to the
  conclusion. NEW FILE — no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.OnGateJets
import QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.OnGateJets QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
open scoped Topology BigOperators ContDiff

namespace QIQTH.AmpFieldGeneralPointBoundLipschitz

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `chartFieldAmp_bound_lipschitz_generalPoint`.**  The concrete on-gate amplitude
    `chartFieldAmp` is BOUNDED and (genuinely, with an explicit nonnegative constant) LIPSCHITZ on a
    ball around a GENERAL FIXED field point `p`, given the same two honest carries
    `OnGateJets.ampField_contDiffAt` needs. Route: `C² ⟹ C¹` at `p`, then the general-basepoint
    convex-MVT Lipschitz helper; boundedness follows from the Lipschitz bound by the triangle
    inequality. NOT `a₁ = R/6`. -/
theorem chartFieldAmp_bound_lipschitz_generalPoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) p)
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z p))) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∃ M : ℝ,
      (∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
        |chartFieldAmp g gi hChr hK a b τ z x - chartFieldAmp g gi hChr hK a b τ z y|
          ≤ L * dist x y) ∧
      (∀ x ∈ Metric.ball p r, |chartFieldAmp g gi hChr hK a b τ z x| ≤ M) := by
  have hC2 : ContDiffAt ℝ 2 (chartFieldAmp g gi hChr hK a b τ z) p :=
    ampField_contDiffAt g gi hChr hK a b τ z p hg hu hWz hdetz
  have hC1 : ContDiffAt ℝ 1 (chartFieldAmp g gi hChr hK a b τ z) p := hC2.of_le (by norm_num)
  obtain ⟨r, hr, L, hL, hlip⟩ :=
    contDiffAt_one_lipschitzOn_ball_atPoint (chartFieldAmp g gi hChr hK a b τ z) p hC1
  refine ⟨r, hr, L, hL, |chartFieldAmp g gi hChr hK a b τ z p| + L * r, ?_, ?_⟩
  · intro x hx y hy
    have h := hlip x hx y hy
    simpa [Real.norm_eq_abs] using h
  · intro x hx
    have hxp : dist x p < r := Metric.mem_ball.mp hx
    have hlipxp : |chartFieldAmp g gi hChr hK a b τ z x - chartFieldAmp g gi hChr hK a b τ z p|
        ≤ L * dist x p := by
      have h := hlip x hx p (Metric.mem_ball_self hr)
      simpa [Real.norm_eq_abs] using h
    have hkey := abs_sub_abs_le_abs_sub
      (chartFieldAmp g gi hChr hK a b τ z x) (chartFieldAmp g gi hChr hK a b τ z p)
    have htri : |chartFieldAmp g gi hChr hK a b τ z x|
        ≤ |chartFieldAmp g gi hChr hK a b τ z p|
          + |chartFieldAmp g gi hChr hK a b τ z x - chartFieldAmp g gi hChr hK a b τ z p| := by
      linarith
    have hLr : L * dist x p ≤ L * r := by
      apply mul_le_mul_of_nonneg_left (le_of_lt hxp) hL
    linarith

end QIQTH.AmpFieldGeneralPointBoundLipschitz

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AmpFieldGeneralPointBoundLipschitz
#print axioms chartFieldAmp_bound_lipschitz_generalPoint
end AxiomChecks
