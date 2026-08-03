/-
  GeomPTransportAssess — J4-173: auditing the two residual L1 carries left by J4-172
  (`QIQTH.ConcreteGateAssembly`) — (A) the general-`p` chart-geometry carry `hGeomP` of
  `hKmeas_concrete_v6`, and (B) the transport-coefficient smoothness carry `hu` — and delivering the
  honest re-thread / assessment of each.  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  audit / regularity-plumbing brick.  It neither strengthens nor weakens the substrate; it makes the
  two standing L1 carries HONEST (removing an unsatisfiable-in-general `∀p` hypothesis) and provable
  where Mathlib reaches.  Never a conclusion; no vacuous or unsatisfiable hypotheses; NO `sorry`;
  NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── PART A — THE `hGeomP` SATISFIABILITY AUDIT + THE `v7` RE-THREAD.

    ★ AUDIT VERDICT.  In `ConcreteGateAssembly.hKmeas_concrete_v6` the hypothesis `hGeomP` is a
      GENUINELY UNRESTRICTED `∀ p : Point n` of the chart triple
        `{ hball : ∀ z∈K, W z p ∈ ball 0 (modulus p),  hnorm : ∀ z∈K, ‖W z p‖ ≤ ρ_K,
           hRI   : ∀ z∈K, φ_z (W z p) = p }`.
      Nothing upstream restricts `p` (the `∀ x₀∈u`/`∀ᶠ x`/`∀ᵐ z` structure of the CONCLUSION quantifies
      the field/base points, not the chart argument `p`, which `hGeomP` binds independently).  The
      third clause `hRI : φ_z (W z p) = p` is the chart RIGHT-inverse at `p`; for a metric with FINITE
      injectivity radius over `K` a field point `p` beyond the chart's uniform reach is NOT the exponential
      image of any velocity `W z p` in the ball, so `φ_z (W z p) = p` genuinely FAILS.  Hence `hGeomP`
      as an unrestricted `∀ p` is **NOT satisfiable in general** — it is exactly the J4-168 far-`p`
      obstruction, re-imported.  (On the chart's uniform reach it IS satisfiable — see the reach-side
      note below — but `v6` demands it EVERYWHERE.)

    ★ THE FIX — `hKmeas_concrete_v7`.  The honest form routes, PER field point `p`, through a
      DISJUNCTION exactly as J4-168's `hVmapMeasK_of_geomOrMeas` / `hKmeas_concrete_v4` do:
        EITHER the geometric triple `{hball, hnorm, hRI}` at `p` (holds where the chart reaches)
        OR the pair `{ MeasurableSet (K ∩ {z | p ∈ S z}),  AEStronglyMeasurable (z ↦ W z p) |_K }`
           (the honest measurability residue for far `p`).
      From the LEFT disjunct BOTH the `K`-relative gate measurability `hSmK`
      (`GateSetMeasurability.flowBallGate_hSmK_of_geom`, with the ball LEFT-inverse `hLI` DERIVED from
      the banked germ via `reachableGate_concrete`) AND the `hChartP` left branch follow; from the RIGHT
      disjunct BOTH follow directly.  So `v7` supplies the two `hKmeas_concrete_v5` inputs (`hSmK`,
      `hChartP`) from ONE per-`p` disjunction, each branch satisfiable and the disjunction total — the
      `∀p` carry is now honest (never unsatisfiable).  `v6`'s unrestricted `hGeomP` is superseded by this
      `v7`.

    ★ WHY THE DISJUNCTION IS NEEDED (and a bare `hChartP` is not enough).  `hKmeas_concrete_v5` needs
      BOTH `hSmK` (an HONEST measurable SET `K ∩ {z|p∈S z}`) and `hChartP`.  The `hChartP` measurability
      branch gives only `AEStronglyMeasurable (z ↦ W z p) |_K`, which — being only ae-equal to a
      measurable map — does NOT by itself force the open-ball preimage set to be measurable.  So the
      far-`p` residue must carry the measurable SET as well; the `v7` disjunction's RIGHT branch pairs
      the two, which is the minimal honest carry.  (This is why `v6` had to keep the full geometry: to
      manufacture `hSmK`.  `v7` isolates the genuine residue instead.)

    ── REACH-SIDE FACTS.  For `p` IN the flow-image of the ball at `z` (the reachable set) the triple
      is NOT a free carry: `reachableGate_concrete` already gives, ON gate points, openness + the ball
      left inverse `hLI` + field-`C²` + reachability, and `ConcreteGateAssembly.flowBallGate_hRI_onGate`
      derives the on-gate right inverse `φ_z (W z p) = p`.  The `v7` LEFT disjunct is therefore
      discharged for every `p` the chart reaches; only the genuine far-`p` complement rides the RIGHT
      (measurability) branch.

  ── PART B — THE `hu` ASSESSMENT (transport-coefficient smoothness).

    ★ WHAT `transportCoeff`/`radialTransportSolve` ARE.  `hu : ∀ k, ContDiff ℝ ⊤ (transportCoeff T k)`
      for `T = transportOp (vanVleck g) g gi`.  `transportCoeff T` is the DeWitt recursion
        `u_0 ≡ 1`,   `u_{k+1} = radialTransportSolve (k+1) (T u_k)`   (`ParametrixFunction`),
      and `radialTransportSolve k f v = ∫ s in 0..1, s^{k-1} · f (s • v)` (`RadialTransport`) is an
      EXPLICIT ray-integral (a clean PARAMETRIC INTEGRAL over the compact interval `[0,1]`) — NOT a
      `.choose` / opaque ODE solve.  So smoothness of `u_k` is differentiation-under-the-integral, an
      analysis fact, plus the source operator `T` preserving smoothness.

    ★ THE PROVEN RUNG — `radialTransportSolve_continuous`.  From `Continuous f` alone,
      `Continuous (radialTransportSolve k f)`, via Mathlib's parametric interval-integral continuity
      `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` applied to the jointly
      continuous integrand `(v,s) ↦ s^{k-1} · f (s•v)`.  Lifted through the recursion by
      `transportCoeff_continuous_of_preserve`: if `T` preserves continuity then EVERY `transportCoeff T k`
      is continuous (the continuity-level analogue of `hu`, fully proved here).

    ★ THE HONEST `hu` REDUCTION — `hu_of_solve_smooth` / `hu_concrete_of_solve_smooth`.  Full `C^∞` under
      the integral for interval integrals is not a single banked Mathlib lemma (only the CONTINUITY
      parametric-integral lemmas exist in this toolchain — the `C^∞`-under-the-integral would be a
      multi-brick differentiation-under-the-integral effort).  So `hu` itself is left reduced, not
      claimed: `hu_of_solve_smooth` makes the induction EXPLICIT — GIVEN (i) the solve operator preserves
      `C^∞` (`hSolve`, the parametric-integral smoothness) and (ii) the transport source `T` preserves
      `C^∞` (`hT`, the geometric DeWitt-operator fact), `∀ k, ContDiff ℝ ⊤ (transportCoeff T k)` follows
      by induction on `k`.  Both premises are genuine operator-level properties, NEITHER the conclusion
      in disguise (they are about `radialTransportSolve` / `T` as operators on ARBITRARY inputs, not about
      the specific `transportCoeff` chain).  `hu_concrete_of_solve_smooth` specializes to the exact `hu`
      shape `T = transportOp (vanVleck g) g gi`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConcreteGateAssembly
import QIQTH.RadialTransport
import QIQTH.ParametrixFunction

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.ChartFieldC2General QIQTH.GateSetMeasurability QIQTH.ChartGeneralPContinuity
open QIQTH.ConcreteGateAssembly
open scoped BigOperators Topology Interval

namespace QIQTH.GeomPTransportAssess

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — the honest `∀p` re-thread `hKmeas_concrete_v7` (per-`p` disjunction).
    ############################################################################### -/

/-- **★★ `hKmeas_concrete_v7` — the honest `∀p` re-thread of `ConcreteGateAssembly.hKmeas_concrete_v6`.**
    The AUDIT (see header): `v6`'s `hGeomP` is a genuinely unrestricted `∀ p : Point n` of the chart
    triple, whose right-inverse clause `φ_z (W z p) = p` FAILS for `p` beyond the chart's finite reach —
    so `hGeomP` is NOT satisfiable in general.  This version replaces it by the HONEST per-`p`
    DISJUNCTION (the J4-168 `geometry-OR-measurability` pattern), carrying for each `p`
      EITHER the geometric triple `{hball, hnorm, hRI}` at `p`
      OR the pair `{ MeasurableSet (K ∩ {z | p ∈ S z}),  AEStronglyMeasurable (z ↦ W z p) |_K }`.
    From the LEFT disjunct BOTH `hKmeas_concrete_v5` inputs follow — `hSmK` via
    `flowBallGate_hSmK_of_geom` (the ball left inverse `hLI` DERIVED from the banked germ, NOT carried)
    and `hChartP` via `Or.inl`; from the RIGHT disjunct BOTH follow directly.  Each branch is satisfiable
    and the disjunction total, so the carry is never unsatisfiable.  Delivers the EXACT `hKmeas` slot of
    `g2_bundle_assembled` for `witnessFieldDeriv`.  Final carries {the per-`p` disjunction, the coverage
    geometry `hMemNear`, `hg`, `hgpos`, `hu`}.  Supersedes `hKmeas_concrete_v6`.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v7 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ p : Point n,
          ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
                ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
            ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
            ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
          ∨ ( MeasurableSet
                (K ∩ {z : Point n |
                  p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c})
              ∧ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
                  ((volume : Measure (Point n)).restrict K) )) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            a b i (t - s) x z)
          (volume : Measure (Point n)) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ hDisj hMemNear
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  -- The ball LEFT inverse, DERIVED from the banked germ (p-independent).
  have hLI : ∀ z ∈ K, ∀ v ∈ Metric.ball (0 : Point n) c,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
    intro z hz v hv
    exact (hreach c hc0 hcδ z hz).2.1 v hv
  -- `hSmK` from the disjunction: geometry ⟹ `flowBallGate_hSmK_of_geom`; measurability branch direct.
  have hSmK : ∀ p : Point n, MeasurableSet (K ∩ {z : Point n | p ∈ S z}) := by
    intro p
    rcases hDisj p with ⟨hball, hnorm, hRI⟩ | ⟨hSm, _hmeas⟩
    · exact flowBallGate_hSmK_of_geom g gi hC hK p c hball hnorm hRI hLI
    · exact hSm
  -- `hChartP` from the disjunction: geometry ⟹ `Or.inl`; measurability branch ⟹ `Or.inr`.
  have hChartP : ∀ p : Point n,
      ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
            ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
        ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
        ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
      ∨ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
          ((volume : Measure (Point n)).restrict K) := by
    intro p
    rcases hDisj p with hgeo | ⟨_hSm, hmeas⟩
    · exact Or.inl hgeo
    · exact Or.inr hmeas
  -- `hGateDiff` from the coverage geometry (identical to `v6`).
  have hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → PdiffAt (fun x' : Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x := by
    apply QIQTH.OnGateFieldRegularity.hGateDiff_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀ i
    filter_upwards [hMemNear x₀ hx₀ i] with s hs
    intro hmem
    filter_upwards [hs hmem] with x hx
    filter_upwards [hx] with z hz
    intro hzK
    have hxSz : x ∈ S z := hz hzK
    obtain ⟨hopen, _hLIz, hxfacts⟩ := hreach c hc0 hcδ z hzK
    exact ⟨hxSz, hopen, (hxfacts x hxSz).2⟩
  exact hKmeas_concrete_v5 g gi hC hK S a b t u hSmK hg hgpos hu hChartP hGateDiff

/-! ###############################################################################
    ### PART B — `radialTransportSolve` continuity + the honest `hu` reduction.
    ############################################################################### -/

/-- **★ The PROVEN Part-B rung — `radialTransportSolve_continuous`.**  `radialTransportSolve k f v =
    ∫ s in 0..1, s^{k-1}·f (s•v)` is a PARAMETRIC interval integral, so from `Continuous f` alone the
    solve is continuous in the base point `v`:  `Continuous (radialTransportSolve k f)`.  Proof:
    Mathlib's `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` on the jointly
    continuous integrand `(v,s) ↦ s^{k-1}·f (s•v)` (`s^{k-1}` continuous in `s`; `f (s•v)` continuous
    by composing `f` with the continuous scalar-multiplication ray).  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_continuous (k : ℕ) (f : Point n → ℝ) (hf : Continuous f) :
    Continuous (radialTransportSolve k f) := by
  have huc : Continuous (Function.uncurry
      (fun (v : Point n) (s : ℝ) => s ^ (k - 1) * f (s • v))) := by
    have he : (Function.uncurry (fun (v : Point n) (s : ℝ) => s ^ (k - 1) * f (s • v)))
        = fun p : Point n × ℝ => p.2 ^ (k - 1) * f (p.2 • p.1) := rfl
    rw [he]
    exact (continuous_snd.pow (k - 1)).mul (hf.comp (continuous_snd.smul continuous_fst))
  show Continuous (fun v => ∫ s in (0:ℝ)..1, s ^ (k - 1) * f (s • v))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huc 0 1

/-- **`transportCoeff_continuous_of_preserve` — the continuity-level analogue of `hu`, fully proved.**
    If the transport source `T` preserves CONTINUITY, then every DeWitt coefficient `transportCoeff T k`
    is continuous, by induction on `k`: the base `u_0 ≡ 1` is constant; the step
    `u_{k+1} = radialTransportSolve (k+1) (T u_k)` is continuous by `radialTransportSolve_continuous`
    applied to the continuous source `T u_k`.  (The `C^∞` analogue needs the stronger
    smoothness-preservation of the solve — see `hu_of_solve_smooth`.)  NOT `a₁ = R/6`. -/
theorem transportCoeff_continuous_of_preserve (T : (Point n → ℝ) → (Point n → ℝ))
    (hT : ∀ f : Point n → ℝ, Continuous f → Continuous (T f)) :
    ∀ k, Continuous (transportCoeff T k) := by
  intro k
  induction k with
  | zero => rw [transportCoeff_zero]; exact continuous_const
  | succ m ih =>
      rw [transportCoeff_succ]
      exact radialTransportSolve_continuous (m + 1) (T (transportCoeff T m)) (hT _ ih)

/-- **★ `hu_of_solve_smooth` — the HONEST reduction making the `hu` induction explicit.**  The full
    `C^∞` `hu : ∀ k, ContDiff ℝ ⊤ (transportCoeff T k)` reduces to two GENUINE operator-level
    properties, NEITHER the conclusion in disguise:
      • `hSolve` — the solve operator preserves `C^∞` (differentiation under the ray integral; the
        Mathlib parametric-integral `C^∞` lemma is not banked in this toolchain, so this is the honest
        residue);
      • `hT` — the transport SOURCE `T` preserves `C^∞` (the geometric DeWitt-operator fact).
    Then `∀ k, ContDiff ℝ ⊤ (transportCoeff T k)` follows by induction on `k`
    (`u_0 ≡ 1` constant; `u_{k+1} = radialTransportSolve (k+1) (T u_k)`).  NOT `a₁ = R/6`. -/
theorem hu_of_solve_smooth (T : (Point n → ℝ) → (Point n → ℝ))
    (hSolve : ∀ (k : ℕ) (f : Point n → ℝ), ContDiff ℝ (⊤ : WithTop ℕ∞) f
        → ContDiff ℝ (⊤ : WithTop ℕ∞) (radialTransportSolve k f))
    (hT : ∀ f : Point n → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) f
        → ContDiff ℝ (⊤ : WithTop ℕ∞) (T f)) :
    ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff T k) := by
  intro k
  induction k with
  | zero => rw [transportCoeff_zero]; exact contDiff_const
  | succ m ih =>
      rw [transportCoeff_succ]
      exact hSolve (m + 1) (T (transportCoeff T m)) (hT _ ih)

/-- **`hu_concrete_of_solve_smooth` — the reduction specialized to the exact `hu` shape.**  The
    `T = transportOp (vanVleck g) g gi` instance of `hu_of_solve_smooth`: from the solve `C^∞`-preservation
    and the concrete transport-operator `C^∞`-preservation, the EXACT `hu` carry standing in every
    `hKmeas`/`hC2fam` slot of the campaign.  NOT `a₁ = R/6`. -/
theorem hu_concrete_of_solve_smooth (g gi : Point n → Fin n → Fin n → ℝ)
    (hSolve : ∀ (k : ℕ) (f : Point n → ℝ), ContDiff ℝ (⊤ : WithTop ℕ∞) f
        → ContDiff ℝ (⊤ : WithTop ℕ∞) (radialTransportSolve k f))
    (hT : ∀ f : Point n → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) f
        → ContDiff ℝ (⊤ : WithTop ℕ∞) (transportOp (vanVleck g) g gi f)) :
    ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k) :=
  hu_of_solve_smooth (transportOp (vanVleck g) g gi) hSolve hT

end QIQTH.GeomPTransportAssess

section AxiomChecks
open QIQTH.GeomPTransportAssess
#print axioms hKmeas_concrete_v7
#print axioms radialTransportSolve_continuous
#print axioms transportCoeff_continuous_of_preserve
#print axioms hu_of_solve_smooth
#print axioms hu_concrete_of_solve_smooth
end AxiomChecks
