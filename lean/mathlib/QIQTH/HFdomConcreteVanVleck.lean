/-
  HFdomConcreteVanVleck — J4-1106: the concrete wiring flagged (but not attempted) by J4-1105 —
  matching `vanVleckGatedWitness` to the `hEmeas`-gated `leviSeries_gatedWitnessN1_dominated` (J4-114
  (B)) instantiation, producing `hDConv_AT_GATE`'s (`HDConvGateThreading.lean`) `hFdom` antecedent in
  its LITERAL binder shape at the SAME concrete `a, b, S` the banked existential internally selects.

  WHY / CORRECTIVE.  J4-1105 reduced `hFdom` to an ABSTRACT wrapper (`HFdomOfLeviSeriesDominated.
  hFdom_of_leviSeries_dominatedW`) carrying two obligations `{hEbound, hInt}` for an abstract residual
  `E`, and flagged: "the concrete wiring (matching `vanVleckGatedWitness` to the `hEmeas`-gated N1
  instantiation), not attempted this round." On inspection this is UNNECESSARY detour: the ALREADY-
  BANKED `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated` does not merely supply `hEbound`+
  `hInt` separately — it ALREADY bundles them internally (via `iterConvIntegrableW_of_locally_bound_
  baseMeas` + `leviSeries_dominatedW_le`, see its proof) and returns the FULL Levi-series domination
  `|leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q` directly, conditional ONLY on `hEmeas` (M1).
  Its kernel expression `gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff
  (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))` is — argument-for-argument —
  the UNFOLDING of `vanVleckGatedWitness g gi hC hK S a b` (`ConvApproximants.lean`); no separate
  "kernel-identity bridge" is needed, only `simp only [vanVleckGatedWitness]` to unfold the `def`.

  So the only remaining step is REPACKAGING: obtain the existential `⟨a, b, C, S, hbound, hL⟩` from
  `leviSeries_gatedWitnessN1_dominated`, unfold `vanVleckGatedWitness` on both the bound and the
  measurability antecedent, and convert `baseKernelW 2 0` to `gaussDdim (2·s) (z-y)` via the banked
  `baseKernelW_zero_apply` (`ParametrixHEboundWiring.lean`) — giving `hFdom`'s EXACT literal shape
  (`∀ s, 0 < s → s ≤ T → ∀ z y, |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z
  y| ≤ C_L · gaussDdim (2·s) (z-y)`) at the concrete `a, b, S`, conditional on `hEmeas` for THOSE
  concrete `a, b, S`.

  `gpt-5.6-sol` (high) confirmed (this dispatch's consult, verbatim quote): "(1) genuinely non-vacuous,
  sound, honest concrete wiring — it converts the banked `baseKernelW 2 0` estimate into the literal
  `gaussDdim (2s)(z-y)` shape required by `hFdom`, preserving the SAME chosen `a,b,S`. (2) a plain
  `noncomputable def` remains definitionally unfoldable — `simp only [vanVleckGatedWitness]` is the
  robust route (bare `exact`/`rwa` would likely also work via defeq, but this is clearer/less brittle).
  (3) `hFdom` is no longer a separately open analytic obligation — it has COLLAPSED INTO the M1
  measurability wall (`hEmeas`), the SAME status as `leviSeries_gatedWitnessN1_dominated`'s own second
  conjunct; one qualification: `hDConv_AT_GATE` still needs `hEmeas` supplied for the SAME `a,b,S` this
  lemma returns, before `hFdom` is actually in hand." NO new rate/asymptotic/convergence claim is
  introduced here (pure logical repackaging + `def`-unfolding of already-proven facts), so no fresh
  sympy check is needed per the standing rule's scope.

  ⚠ HONEST SCOPE.  This does NOT discharge `hFdom` unconditionally, and does NOT touch ANY of
  `hDConv_AT_GATE`'s other ~25 census hypotheses (`hEdom`, `hAdom`, `hLapFull`, `hII_lo/hi`, `hFII`
  family, `hQ1`, `hFmeas`, `hbound`/`hdiff` families, etc.) — those remain fully separately open. It
  shows PRECISELY: `hFdom` (for the concrete `N=1` van-Vleck witness, at the `a,b,S` selected by
  `leviSeries_gatedWitnessN1_dominated`) reduces to EXACTLY the M1 wall `hEmeas` — the SAME wall
  already tracked for `leviSeries_gatedWitnessN1_dominated` itself, i.e. `hFdom` is no longer a
  distinct open item; it merges into the existing M1 census entry. `a₁=R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁=R/6`.
-/
import Mathlib
import QIQTH.GatedWitnessPackage
import QIQTH.ParametrixHEboundWiring
import QIQTH.ConvApproximants

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatResidualBound
open scoped BigOperators ContDiff Topology

namespace QIQTH.HFdomConcreteVanVleck

variable {n : ℕ}

/-- **`hFdom` at the concrete `N = 1` van-Vleck gated witness — the missing concrete wiring flagged
    by J4-1105.**  From the SAME geometric/gauge/all-`k`-smoothness inputs as
    `leviSeries_gatedWitnessN1_dominated`, there are cutoff radii `a < b` and a gate `S` such that the
    concrete gated van-Vleck witness `H_G := vanVleckGatedWitness g gi hC hK S a b` obeys the
    `(0,t]`-restricted residual bound, AND — given the SAME single joint strong measurability `hEmeas`
    of `heatOp g gi H_G` (the M1 wall) — `hDConv_AT_GATE`'s `hFdom` antecedent holds LITERALLY for
    `F := leviSeries (heatOp g gi H_G)` at those exact `a, b, S`.  Route: unfold `vanVleckGatedWitness`
    on `leviSeries_gatedWitnessN1_dominated`'s conclusion (its kernel expression IS the unfolding, by
    `simp only [vanVleckGatedWitness]`), then rewrite `baseKernelW 2 0` to `gaussDdim (2·)` via
    `baseKernelW_zero_apply`. -/
theorem hFdom_concrete_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hn : 1 ≤ n) (T : ℝ) (hT : 0 < T) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ (StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) w.1 w.2.1 w.2.2) →
          ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z y|
              ≤ C_L * gaussDdim (2 * s) (z - y)) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hL⟩ :=
    leviSeries_gatedWitnessN1_dominated g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0 hn T hT
  refine ⟨a, b, C, ha, hab, hC0, S, ?_, ?_⟩
  · simpa only [vanVleckGatedWitness] using hbound
  · intro hEmeas
    have hEmeas' : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK))) w.1 w.2.1 w.2.2) := by
      simpa only [vanVleckGatedWitness] using hEmeas
    obtain ⟨C_L, hC_L0, hCL⟩ := hL hEmeas'
    refine ⟨C_L, hC_L0, fun s hs hsT z y => ?_⟩
    have h := hCL s z y hs hsT
    simpa only [vanVleckGatedWitness, baseKernelW_zero_apply] using h

end QIQTH.HFdomConcreteVanVleck
