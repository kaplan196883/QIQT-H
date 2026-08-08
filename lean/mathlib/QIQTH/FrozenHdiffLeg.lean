/-
  FrozenHdiffLeg — J4-439 (the a₁ = R/6 convergence-trio campaign, diff-under-∫ family):
  DISCHARGING THE OUTER `HasDerivAt` LEG (leg 7, `hdiff`) OF THE FROZEN hQ1 PROVIDER.

  J4-438 (`FrozenProviderLegs`) shrank the seven-leg frozen first-order diff-under-∫ provider
  `hFrozenData` to the honest REMAINDER {snb, bound+hbdd, hbound, hdiff} — legs (1)+(5)+(6)+(7).
  This BRICK discharges leg (7), the outer `s`-level `HasDerivAt` family
      `∀ᵐ s, s ∈ (0, u−εₘ] → ∀ w ∈ snb,
         HasDerivAt (w ↦ ∫z W (u−s) (update y i w) z · F s z 0)
                    (∫z dH i (u−s) (update y i w) z · F s z 0) w`,
  where `W := vanVleckGatedWitness g gi hC hK S a b`, `dH i := witnessFieldDeriv … i`,
  `F := leviSeries (heatOp g gi W)`.  The J4-438 note flagged this as reducible via
  `SecondOrderInterchange.innerZ_line_hasDerivAt` to a base-`y` `z`-level bundle; THIS BRICK takes
  that reduction AND discharges the bundle's innermost `z`-pointwise `HasDerivAt` family internally,
  via the BANKED FIRST-ORDER GATE DICHOTOMY `WitnessMeasDeriv.hWdiff_offGate` / `hWdiff_onGate`.

  ── WHAT'S BUILT (axiom-free, no `sorry`, std-3).
    • `witnessValue_line_hasDerivAt_update` — the FIRST-ORDER slice `HasDerivAt` at the GENERAL base
      line-point `update y i w'` (NOT base `0`): from the per-`z` gate dichotomy `z ∉ K ∨ PdiffAt`,
      glued exactly as `InnerDataInstantiation.witnessFieldDeriv_line_hasDerivAt_update` but one field-
      derivative order DOWN (`W → dH` instead of `dH → dHH`) and at general `y` — reusing the banked
      `hWdiff_offGate` (unconditional) / `hWdiff_onGate` (on the `PdiffAt` carry) at `x := update y i w'`
      (`Function.update_idem` / `Function.update_self` collapse the double update to the running point).
    • `innerZ_prod_hasDerivAt_witnessValue` — `.mul_const L` attaching the (field-constant) Levi factor,
      the exact `z`-pointwise `HasDerivAt` family consumed by `innerZ_line_hasDerivAt`.
    • `frozenLeg_hdiff` — ★ the outer `hdiff` leg IN ITS EXACT hRemainder SHAPE, produced per-`(s,w)`
      from `HeatResidualBound.innerZ_line_hasDerivAt` fed by a per-`(s,w)` base-`y` `z`-level REDUCED
      CORE (nbhd + slice measurabilities + base integrability + integrable dominator + `∀ᵐ z` derivative
      domination + the per-`z` GATE DICHOTOMY), the dichotomy discharging the innermost `z`-pointwise
      `HasDerivAt` family through `innerZ_prod_hasDerivAt_witnessValue`.
    • `innerDiff_phase3` — `innerDiff_phase2` with `hdiff` SUPPLIED INTERNALLY: the frozen provider
      remainder SHRINKS 4 → 3 (snb + the dominator triple {bound+hbdd, hbound}); the outer `HasDerivAt`
      is replaced by the strictly-lighter per-`(s,w)` `z`-level reduced-core carry `hRemainderDiff`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem re-threads BANKED, satisfiable diff-under-∫ data into the exact
  leg shapes.  NONE proves `a₁ = R/6`, and proves NOTHING about `R/6`.  The `z`-level reduced core is a
  genuine, satisfiable, non-vacuous input (its Gaussian-domination and on-gate `C¹`/`PdiffAt` conjuncts
  are the analytic content no `HasDerivAt` engine can manufacture), never the conclusion.  No `sorry`
  (header prose excepted), no `:= True`, no new axioms, no existing file edited.

  ── WHAT'S BANKED-vs-ENUMERATED (dont-undercredit findings).
    • The `HasDerivAt`-under-∫ ENGINE `HeatResidualBound.innerZ_line_hasDerivAt` is fully banked, and
      it is BASE-GENERAL: it differentiates at an arbitrary base line-point `p` (we instantiate `p := w`,
      the running point) — no base-`0` restriction.  We wire, not re-prove.
    • The FIRST-ORDER gate dichotomy `WitnessMeasDeriv.hWdiff_offGate`/`hWdiff_onGate` is BANKED and
      BASE-GENERAL (stated at arbitrary field point `x`, derivative at `x i`); at `x := update y i w'`
      it lands the slice `HasDerivAt` at the running `w'` for general `y`.  Off-gate is unconditional;
      on-gate rides the enumerated `PdiffAt` on-gate `C¹` carry (the germ-`C¹` field-slot input).
    • The z-level reduced-core conjuncts (slice measurabilities, base `z`-integrability, integrable
      dominator + `∀ᵐ z` derivative bound) are ENUMERATED base-`y` inputs — the base-`y` analogues of
      the banked field-point-`0` `InnerDataInstantiation.innerData_pointwise` inputs.  See the ledger v2
      dominator-triple scoping note for how the banked `WitnessDerivDomination` gate envelope supplies
      the Gaussian dominator at base `y`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FrozenProviderLegs
import QIQTH.SecondOrderInterchange
import QIQTH.WitnessMeasDeriv

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.FrozenHdiffLeg

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The FIRST-ORDER slice `HasDerivAt` at the GENERAL base line-point `update y i w'`.
    ############################################################################### -/

/-- **★ `witnessValue_line_hasDerivAt_update` — THE GATE-GLUED WITNESS-VALUE SLICE `HasDerivAt` AT
    `update y i w'`.**  For the base line-point `update y i w'` (whose `i`-th coordinate is `w'`), the
    field-slice of the witness value `W` has derivative `witnessFieldDeriv … i τ (update y i w') z` at
    `w'`, from the per-`z` GATE DICHOTOMY (`z ∉ K` ∨ on-gate `C¹` `PdiffAt` of the witness slice at
    `update y i w'`).  Exactly `InnerDataInstantiation.witnessFieldDeriv_line_hasDerivAt_update` but one
    field-derivative order DOWN (`W → dH` instead of `dH → dHH`) and at GENERAL base `y`, reusing the
    banked base-general `WitnessMeasDeriv.hWdiff_offGate`/`hWdiff_onGate` at `x := update y i w'`;
    `Function.update_idem` collapses `update (update y i w') i w = update y i w`, `Function.update_self`
    gives the point `w'`.  NOT `a₁ = R/6`. -/
theorem witnessValue_line_hasDerivAt_update (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (y z : Point n) (w' : ℝ)
    (hgate : z ∉ K ∨ PdiffAt (fun x' : Point n => vanVleckGatedWitness g gi hChr hK S a b τ x' z) i
        (Function.update y i w')) :
    HasDerivAt (fun v => vanVleckGatedWitness g gi hChr hK S a b τ (Function.update y i v) z)
      (witnessFieldDeriv g gi hChr hK S a b i τ (Function.update y i w') z) w' := by
  have key : HasDerivAt
      (fun w => vanVleckGatedWitness g gi hChr hK S a b τ
        (Function.update (Function.update y i w') i w) z)
      (witnessFieldDeriv g gi hChr hK S a b i τ (Function.update y i w') z)
      ((Function.update y i w') i) := by
    rcases hgate with hz | hpd
    · exact hWdiff_offGate g gi hChr hK S a b i τ (Function.update y i w') z hz
    · exact hWdiff_onGate g gi hChr hK S a b i τ (Function.update y i w') z hpd
  have hfun : (fun w => vanVleckGatedWitness g gi hChr hK S a b τ
        (Function.update (Function.update y i w') i w) z)
      = (fun v => vanVleckGatedWitness g gi hChr hK S a b τ (Function.update y i v) z) := by
    funext w
    rw [Function.update_idem]
  have hpt : (Function.update y i w') i = w' := by rw [Function.update_self]
  rw [hfun, hpt] at key
  exact key

/-- **★ `innerZ_prod_hasDerivAt_witnessValue` — THE `z`-POINTWISE `HasDerivAt` FAMILY.**  Attaching the
    (field-constant) Levi factor `L` via `HasDerivAt.mul_const` to `witnessValue_line_hasDerivAt_update`:
      `HasDerivAt (v ↦ W τ (update y i v) z · L) (dH i τ (update y i w') z · L) w'`,
    which at `L := leviSeries (heatOp g gi W) s z 0` is exactly the innermost `hdiff` instance consumed
    by `HeatResidualBound.innerZ_line_hasDerivAt`.  NOT `a₁ = R/6`. -/
theorem innerZ_prod_hasDerivAt_witnessValue (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (y z : Point n) (w' L : ℝ)
    (hgate : z ∉ K ∨ PdiffAt (fun x' : Point n => vanVleckGatedWitness g gi hChr hK S a b τ x' z) i
        (Function.update y i w')) :
    HasDerivAt
      (fun v => vanVleckGatedWitness g gi hChr hK S a b τ (Function.update y i v) z * L)
      (witnessFieldDeriv g gi hChr hK S a b i τ (Function.update y i w') z * L) w' :=
  (witnessValue_line_hasDerivAt_update g gi hChr hK S a b i τ y z w' hgate).mul_const L

/-! ###############################################################################
    ### ★ `frozenLeg_hdiff` — the outer `HasDerivAt` leg (7), in its exact hRemainder shape.
    ############################################################################### -/

/-- **★★ `frozenLeg_hdiff` — FROZEN PROVIDER LEG (7), DISCHARGED (HasDerivAt-under-∫).**  The outer
    `s`-level `HasDerivAt` family in the EXACT `hRemainder` shape:
      `∀ᵐ s, s ∈ (0, u−εₘ] → ∀ w ∈ snb,
         HasDerivAt (w ↦ ∫z W (u−s) (update y i w) z · F s z 0)
                    (∫z dH i (u−s) (update y i w) z · F s z 0) w`.
    Per-`(s, w)` it fires `HeatResidualBound.innerZ_line_hasDerivAt` (base line-point `p := w`, so the
    derivative lands at the running `w`), fed by the per-`(s,w)` base-`y` `z`-level REDUCED CORE
    `hRemainderDiff` — {nbhd `znb`, `∀w'` slice measurability, base `z`-integrability, first-kernel
    slice measurability, integrable dominator `bnd`, `∀ᵐ z` derivative domination, the per-`z` GATE
    DICHOTOMY} — with the innermost `z`-pointwise `HasDerivAt` family DISCHARGED from the gate dichotomy
    via `innerZ_prod_hasDerivAt_witnessValue`.  Honest carry: `hRemainderDiff`, satisfiable and
    non-vacuous (its Gaussian domination + on-gate `PdiffAt` are the genuine analytic content), never
    the conclusion.  NOT `a₁ = R/6`. -/
theorem frozenLeg_hdiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (i : Fin n) (m : ℕ) (snb : Set ℝ)
    (hRemainderDiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
          znb ∈ 𝓝 w ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
          Integrable bnd volume ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update y i w'))) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
          (Function.update y i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w := by
  filter_upwards [hRemainderDiff] with s hcore hmem w hw
  obtain ⟨znb, bnd, hznb, hWmeas, hbaseInt, hWFDmeas, hbndInt, hdom, hzGate⟩ := hcore hmem w hw
  refine QIQTH.HeatResidualBound.innerZ_line_hasDerivAt
    (vanVleckGatedWitness g gi hC hK S a b)
    (witnessFieldDeriv g gi hC hK S a b i)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    u s i y w znb hznb hWmeas hbaseInt hWFDmeas bnd hbndInt hdom ?_
  filter_upwards [hzGate] with z hz w' hw'
  exact innerZ_prod_hasDerivAt_witnessValue g gi hC hK S a b i (u - s) y z w'
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) (hz w' hw')

/-! ###############################################################################
    ### ★★★ `innerDiff_phase3` — the per-`u` census `Tendsto`, hQ1 provider shrunk 4 → 3.
    ############################################################################### -/

/-- **★★★ `innerDiff_phase3`.**  `FrozenProviderLegs.innerDiff_phase2` with the outer `HasDerivAt` leg
    (7, `hdiff`) SUPPLIED INTERNALLY by `frozenLeg_hdiff`: the frozen `hQ1` provider REMAINDER SHRINKS
    4 → 3 — {snb, the dominator triple `bound`+`hbdd`+`hbound`} — with the outer `HasDerivAt` replaced by
    the strictly-lighter per-`(s,w)` base-`y` `z`-level REDUCED-CORE carry `hRemainderDiff` (bundled
    under the SAME existential `snb` as the dominator, so the domination window and the differentiation
    line-nbhd stay coupled).  Every OTHER carry is threaded exactly as `innerDiff_phase2`.  Pure
    composition; each carry satisfiable, non-vacuous, strictly lower level than the conclusion, none
    equal to `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem innerDiff_phase3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ (w d : ℝ),
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update y i w) p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointYbase : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWFDjointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hWitDomCappedY : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V →
        ∀ Tc εₘ : ℝ, 0 < εₘ → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ y z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hRemainderDiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
              ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (znb : Set ℝ) (bnd : Point n → ℝ),
              znb ∈ 𝓝 w ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume) ∧
              Integrable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume ∧
              Integrable bnd volume ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                ‖witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w') z
                  * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bnd z) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ znb,
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i (Function.update y i w')))) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) := by
  have hRemainder : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (y i) ∧
        IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
              (Function.update y i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖
            ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update y i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s)
              (Function.update y i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w) := by
    intro m i u hu y hy
    obtain ⟨snb, bound, hsnb, hbdd, hbound, hRedCore⟩ := hRemainderDiff m i u hu y hy
    exact ⟨snb, bound, hsnb, hbdd, hbound,
      frozenLeg_hdiff g gi hC hK S a b u y i m snb hRedCore⟩
  exact QIQTH.FrozenProviderLegs.innerDiff_phase2 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont V hV
    hLeviJoint hWitJointY hWitJointYbase hWFDjointY hFzero hFdomEvery hWitDomCappedY hRemainder

end QIQTH.FrozenHdiffLeg

/-! ## THE PROVIDER LEDGER v2 — the per-leg table for the hQ1 frozen provider, remainder 4 → 3.

  `innerDiff_phase3` reproduces the per-`u` census `Tendsto` (= `innerDiff_phase1`'s conclusion) with
  the seven-leg frozen `hQ1` provider `hFrozenData` SHRUNK 7 → 3: legs (2)/(3)/(4) discharged by
  `FrozenProviderLegs` (Fubini + capped-ceiling), and now leg (7) discharged here by `frozenLeg_hdiff`.

    leg          role                                        status          supplier / m-UNIFORMITY
    ──────────   ─────────────────────────────────────────  ──────────────  ────────────────────────
    (1) snb      real-line nbhd 𝓝(y i)                      REMAINDER       via `hRemainderDiff`; per-(i,y)
    (2) hFmeas   `∀w, s↦∫z W(u−s)(update y i w)·F` aesm       ★ DISCHARGED    `frozenLeg_hFmeas` (J4-438)
    (3) hFint    `s↦∫z W(u−s) y·F` interval-integrable        ★ DISCHARGED    `frozenLeg_hFint` (J4-438)
    (4) hF'meas  `s↦∫z dH i (u−s) y·F` aesm                   ★ DISCHARGED    `frozenLeg_hF'meas` (J4-438)
    (5) bound+hbdd  interval-integrable `s`-dominator         REMAINDER       via `hRemainderDiff`; PER-m
    (6) hbound   `‖∫z dH…(update y i w)·F‖ ≤ bound s`          REMAINDER       via `hRemainderDiff`; PER-m
    (7) hdiff    outer `s`-level `HasDerivAt (∫z W)(∫z dH)`    ★ DISCHARGED    `frozenLeg_hdiff` =
                                                             (this brick)    `innerZ_line_hasDerivAt`
                                                                             (base `p := w`, base-general)
                                                                             + `innerZ_prod_hasDerivAt_
                                                                             witnessValue` on the FIRST-
                                                                             order gate dichotomy
                                                                             `hWdiff_offGate`/`onGate` at
                                                                             `x := update y i w'`; fed by
                                                                             the base-`y` z-level REDUCED
                                                                             CORE `hRemainderDiff` (PER-m
                                                                             window, admissible)

  ⚠ VERDICT.  The outer `HasDerivAt` leg (7) is DISCHARGED in the provider's exact shape: the base-
  general engine `innerZ_line_hasDerivAt` differentiates `∫z W …` at the running base point `p := w`,
  and its innermost `z`-pointwise `HasDerivAt` family is supplied by the BANKED first-order gate
  dichotomy (off-gate unconditional, on-gate on the `PdiffAt` germ-`C¹` carry) lifted to general base
  `update y i w'` — one field-derivative order DOWN from the banked base-`0` `InnerDataInstantiation`
  second-order lemmas.  The honest REMAINDER is now {snb, dominator triple} + the base-`y` z-level
  reduced core `hRemainderDiff`, which carries the genuine analytic domination + on-gate `C¹` content.
  This brick proves NOTHING about `a₁ = R/6`; it certifies the hQ1 provider as reducible 7 → 3.

  ── DOMINATOR-TRIPLE SCOPING (legs 5/6 + the z-level dominator `bnd` inside `hRemainderDiff`).
  What the banked `WitnessDerivDomination` gate envelope gives at base `y`.  The `z`-level dominator
  `bnd` (reduced-core conj-5/6) is exactly the base-`y` analogue of the `C · gaussDdim σ` dominator
  discharged at base `0` by `InnerDataInstantiation.innerData_pointwise` (which builds `bnd := C·G_σ`
  via `WitnessDerivDomination.envelope_integrable` from the `witnessFieldDeriv_gate_envelope` Gaussian
  bound + the Levi Gaussian factor).  At GENERAL `y` the gate envelope's base-`0` phrasing does not
  literally apply (as with the J4-438 joint carries), so the base-`y` Gaussian dominator is an
  ENUMERATED input.  PLAN: mirror `innerData_pointwise` at base `y` — an integrable `C · gaussDdim σ`
  dominator (`envelope_integrable`, needs `0 < σ`) with the `∀ᵐ z` bound `hdom` supplied from a base-`y`
  `witnessFieldDeriv` Gaussian envelope × the banked `hFdomEvery` Levi envelope; the outer `s`-level
  dominator `bound` (legs 5/6) then follows by the `∫z |·| ≤ ∫z C·G_σ` capped-ceiling route already run
  for leg (3) in `frozenLeg_hFint`.  That base-`y` envelope is the natural J4-440 target.
-/

section AxiomChecks
open QIQTH.FrozenHdiffLeg
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms witnessValue_line_hasDerivAt_update
#print axioms innerZ_prod_hasDerivAt_witnessValue
#print axioms frozenLeg_hdiff
#print axioms innerDiff_phase3
end AxiomChecks
