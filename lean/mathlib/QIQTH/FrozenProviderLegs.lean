/-
  FrozenProviderLegs — J4-438 (the a₁ = R/6 convergence-trio campaign, diff-under-∫ family):
  DISCHARGING THE MEASURABILITY + INTERVAL-INTEGRABILITY LEGS OF THE hQ1 PROVIDER.

  J4-437 (`InnerDiffFamily`) reduced the census `hQ1` to the SEVEN-leg frozen first-order diff-under-∫
  provider `hFrozenData` (the `F3` carry of `W2Finish.w2_hQ1`), per `(m, i, u∈U, y∈V)`:
      (1) snb ∈ 𝓝 (y i)                          — a real-line nbhd,
      (2) hFmeas   `∀ w, s ↦ ∫z W(u−s)(update y i w) z · F`   is `s`-aesm,
      (3) hFint    `s ↦ ∫z W(u−s) y z · F`        is interval-integrable on `[0, u−εₘ]`,
      (4) hF'meas  `s ↦ ∫z dH i (u−s) y z · F`     is `s`-aesm,
      (5) bound + hbdd  an interval-integrable `s`-dominator,
      (6) hbound   `‖∫z dH i (u−s)(update y i w) z · F‖ ≤ bound s` on the window,
      (7) hdiff    the outer `s`-level `HasDerivAt (∫z W…) (∫z dH…)` family,
  with `W := vanVleckGatedWitness g gi hC hK S a b`, `dH i := witnessFieldDeriv … i`,
  `F := leviSeries (heatOp g gi W)`.  THIS BRICK discharges legs (2)/(3)/(4) — the two `s`-slice
  measurabilities and the witness-value interval-integrability — from strictly-lighter, m-INDEPENDENT
  joint `(s,z)`-measurability carries + m-independent Gaussian-domination carries, via the BANKED
  Fubini engine `InnerMeasFubini.innerIntegral_aesm` and the BANKED capped-ceiling engine
  `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`.  The provider SHRINKS 7 → 4: the
  honest REMAINDER is exactly {snb, bound+hbdd, hbound, hdiff} (leg 1 + the dominator triple + the
  outer HasDerivAt), packaged as `hRemainder`.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING
  about `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio +
  geometric-wiring stack AND on the surviving labelled carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable diff-under-∫ side-condition
  data into the exact `hFrozenData` leg shapes.  NONE proves `a₁ = R/6`.  Each carried hypothesis is
  genuine, satisfiable, non-vacuous, and never the conclusion.  No `sorry` (header prose excepted), no
  `:= True`, no new axioms, no existing file edited.  NOT `a₁ = R/6`.

  ── WHAT'S BANKED-vs-ENUMERATED (dont-undercredit findings).
    • The ENGINES are fully banked: `innerIntegral_aesm` (`InnerMeasFubini`, J4-245),
      `pairing_intervalIntegrable_lowerCapped` / `ESLegWidening.intervalIntegrable_of_deg`
      (`EveryCeilingFamilies`, the F3 template `w2_hFint` runs on).  We wire, not re-prove.
    • The gated joint LEVER `InnerMeasFubini.gatedWitnessShift_joint_aesm` is FIELD-POINT-`0`-ONLY
      (its indicator cylinder is `Prod.snd ⁻¹' (K ∩ {z | 0 ∈ S z})`, `p = 0` fixed), so at GENERAL
      `y ∈ V` it does NOT apply — the joint `(s,z)` carries `hWitJointY`/`hWitJointYbase`/`hWFDjointY`
      are therefore ENUMERATED inputs (the base-`y` analogues of the banked base-`0`
      `hInner`/`hWitDeriv`), each m-INDEPENDENT (phrased `∀ d`, instantiated at `d := u − εₘ`).
    • hdiff (leg 7): the J4-426 gate-dichotomy `InnerDataInstantiation.innerZ_prod_hasDerivAt_witness`
      is the SECOND-order (`dH → dHH`), `z`-POINTWISE, base-`update 0 i w'` shape; the frozen hdiff is
      the FIRST-order (`W → dH`), `∫z`-INTEGRATED, base-`y` `HasDerivAt`.  Shapes DO NOT match, so it
      is NOT wired here — hdiff stays a remainder carry (a deeper reduction to a base-`y` `z`-level
      bundle via `SecondOrderInterchange.innerZ_line_hasDerivAt` exists but only trades one carry for a
      z-level bundle; not taken).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerDiffFamily
import QIQTH.InnerMeasFubini
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.FrozenProviderLegs

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (Leg 2) `frozenLeg_hFmeas` — the `∀ w` witness-value `s`-slice measurability.
    ############################################################################### -/

/-- **★ `frozenLeg_hFmeas` — FROZEN PROVIDER LEG (2), DISCHARGED (Fubini).**  For every `w`, the
    `s`-ae-strong-measurability of the shifted witness-value inner pairing on the truncated window
    `(0, u−εₘ]`:
      `s ↦ ∫ z, vanVleckGatedWitness … (u−s) (update y i w) z · leviSeries (heatOp g gi W) s z 0`.
    Runs the banked Fubini engine `InnerMeasFubini.innerIntegral_aesm` on `.mul` of the enumerated
    base-`y` joint witness carry `hWitJoint` (∀ `w`) and the Levi joint carry `hLeviJoint`.  The
    base-`y` analogue of the banked field-point-`0` `InnerMeasFubini.hFmeas_concrete`.  Honest carries:
    {`hWitJoint`, `hLeviJoint`}, both m-INDEPENDENT once the window `u−εₘ` is fixed.  NOT `a₁ = R/6`. -/
theorem frozenLeg_hFmeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (i : Fin n) (m : ℕ)
    (hWitJoint : ∀ w : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update y i w) p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n)))) :
    ∀ w : ℝ, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update y i w) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro w
  exact QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update y i w) p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
    ((hWitJoint w).mul hLeviJoint)

/-! ###############################################################################
    ### (Leg 4) `frozenLeg_hF'meas` — the field-derivative `s`-slice measurability.
    ############################################################################### -/

/-- **★ `frozenLeg_hF'meas` — FROZEN PROVIDER LEG (4), DISCHARGED (Fubini).**  The
    `s`-ae-strong-measurability of the FIRST field-derivative inner pairing at base `y`:
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) y z · leviSeries (heatOp g gi W) s z 0`.
    Runs `InnerMeasFubini.innerIntegral_aesm` on `.mul` of the enumerated base-`y` joint
    field-derivative carry `hWFDjoint` and the Levi joint carry `hLeviJoint`.  The base-`y` analogue of
    the banked field-point-`0` `InnerMeasFubini.hF'meas_concrete`.  Honest carries: {`hWFDjoint`,
    `hLeviJoint`}, m-INDEPENDENT.  NOT `a₁ = R/6`. -/
theorem frozenLeg_hF'meas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (i : Fin n) (m : ℕ)
    (hWFDjoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n))))
    (hLeviJoint : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 (u - epsSeq m))).prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) y z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) :=
  QIQTH.InnerMeasFubini.innerIntegral_aesm
    (fun p : ℝ × Point n =>
      witnessFieldDeriv g gi hC hK S a b i (u - p.1) y p.2
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
    (hWFDjoint.mul hLeviJoint)

/-! ###############################################################################
    ### (Leg 3) `frozenLeg_hFint` — the witness-value interval-integrability at base `y`.
    ############################################################################### -/

/-- **★ `frozenLeg_hFint` — FROZEN PROVIDER LEG (3), DISCHARGED (capped-ceiling).**  Interval-
    integrability on `[0, u−εₘ]` of the witness-VALUE inner pairing at base `y`:
      `s ↦ ∫ z, vanVleckGatedWitness … (u−s) y z · leviSeries (heatOp g gi W) s z 0`.
    Verbatim the `W2Finish.w2_hFint` route, but with the kernel argument INSTANTIATED to ignore its
    base slot — `A := fun τ _ z => vanVleckGatedWitness … τ y z`, so `A (u−s) 0 z = W (u−s) y z` — which
    hits base `y` instead of base `0`.  CASE 1 (`u−εₘ ≤ 0`) is `ESLegWidening.intervalIntegrable_of_deg`
    (`hFzero`); CASE 2 (`u−εₘ > 0`, `0 < u`) is `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`
    at ceiling `Tc := u`, lower cap `εₘ := epsSeq m` (both endpoints `≤ u−εₘ`, so `τ = u−s ≥ εₘ`).
    Honest carries: {`hFzero`, `hWitDomCappedY` (the base-`y` capped Gaussian bound), `hFdomEvery`,
    `hmeas`} — `hmeas` itself is supplied by the Fubini leg (`innerIntegral_aesm` on `hWitJointYbase`),
    so at the assembly point (3) is fully diff-under-∫-reduced.  NOT `a₁ = R/6`. -/
theorem frozenLeg_hFint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (u : ℝ) (y : Point n) (m : ℕ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWitDomCappedY : ∀ Tc εₘ : ℝ, 0 < εₘ → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ y z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) y z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    IntervalIntegrable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) y z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact QIQTH.ESLegWidening.intervalIntegrable_of_deg
      (fun τ _ z => vanVleckGatedWitness g gi hC hK S a b τ y z)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wA, CA, hwA, hCA, hDom⟩ := hWitDomCappedY u (epsSeq m) hεpos
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact QIQTH.EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped
      (fun τ _ z => vanVleckGatedWitness g gi hC hK S a b τ y z)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
      u u (epsSeq m) wA CA wF CF hu0 le_rfl hεpos hwA hCA hwF hCF hDom hFdom hFzero
      0 (u - epsSeq m) (by linarith) le_rfl hmeas

/-! ###############################################################################
    ### `frozenData_of_remainder` — the full 7-leg `hFrozenData`, shrunk to the remainder.
    ############################################################################### -/

/-- **★★ `frozenData_of_remainder` — THE hQ1 PROVIDER, SHRUNK 7 → 4.**  Produces the EXACT seven-leg
    frozen first-order diff-under-∫ provider `hFrozenData` (the `F3` carry of `W2Finish.w2_hQ1`, and
    the `hFrozenData` hypothesis of `InnerDiffFamily.innerDiff_phase1`) from:
      • the DISCHARGED legs (2)/(3)/(4) — via `frozenLeg_hFmeas`/`frozenLeg_hFint`/`frozenLeg_hF'meas`
        on the m-INDEPENDENT joint carries {`hLeviJoint`, `hWitJointY`, `hWitJointYbase`, `hWFDjointY`}
        (each phrased `∀ d`, instantiated at `d := u − εₘ`) + the base-`y` Gaussian-domination carries
        {`hFzero`, `hWitDomCappedY`, `hFdomEvery`};
      • the honest REMAINDER `hRemainder` — legs (1)+(5)+(6)+(7): the nbhd `snb ∈ 𝓝 (y i)`, the
        interval-integrable dominator `bound`, the `∀ᵐ s` domination `hbound`, and the outer `s`-level
        `HasDerivAt` family `hdiff`.
    m-UNIFORMITY: every joint / Gaussian carry is m-INDEPENDENT; only the window `u−εₘ` and the
    dominator/HasDerivAt remainder are per-`m` — ADMISSIBLE, since `hQ1` is a per-`m` equality with no
    series over `m`.  Every carry is satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem frozenData_of_remainder (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n))
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
    (hRemainder : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
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
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w)) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
                (Function.update y i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) y z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
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
  obtain ⟨snb, bound, hsnb, hbdd, hbound, hdiff⟩ := hRemainder m i u hu y hy
  refine ⟨snb, bound, hsnb, ?_, ?_, ?_, hbdd, hbound, hdiff⟩
  · -- leg (2) hFmeas — Fubini
    exact frozenLeg_hFmeas g gi hC hK S a b u y i m
      (fun w => hWitJointY i u hu y hy w (u - epsSeq m)) (hLeviJoint (u - epsSeq m))
  · -- leg (3) hFint — capped-ceiling, with hmeas from the Fubini engine on the base-`y` joint carry
    exact frozenLeg_hFint g gi hC hK S a b u y m hFzero
      (hWitDomCappedY u hu y hy) hFdomEvery
      (QIQTH.InnerMeasFubini.innerIntegral_aesm
        (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (u - p.1) y p.2
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
        ((hWitJointYbase u hu y hy (u - epsSeq m)).mul (hLeviJoint (u - epsSeq m))))
  · -- leg (4) hF'meas — Fubini
    exact frozenLeg_hF'meas g gi hC hK S a b u y i m
      (hWFDjointY i u hu y hy (u - epsSeq m)) (hLeviJoint (u - epsSeq m))

/-! ###############################################################################
    ### ★★ `innerDiff_phase2` — the per-`u` census `Tendsto`, hQ1 provider shrunk to the remainder.
    ############################################################################### -/

/-- **★★★ `innerDiff_phase2`.**  THE per-`u` census `Tendsto` (= `InnerDiffFamily.innerDiff_phase1`'s
    conclusion, the `PerUCensusInstantiation.perUCensus_phase1` binder), with the frozen `hQ1` provider
    `hFrozenData` DISCHARGED INTERNALLY from `frozenData_of_remainder`: legs (2)/(3)/(4) supplied by
    the Fubini + capped-ceiling engines on the m-INDEPENDENT joint / Gaussian carries, the honest
    remainder being `hRemainder` = {snb, dominator (`bound`+`hbdd`), `hbound`, `hdiff`}.  Every OTHER
    census field is kept as an ENUMERATED CARRY exactly as in `innerDiff_phase1` (domain `U`/`hUpos`,
    nbhd `nb`, the diagonal provider `hProv`, the order-2 data `fderivBulk`/`gderiv`/`C₀`/`C₁`/`C₂`, the
    interval-integrability `hGint`, the bulk differentiation `hbulkderiv`, the `O(√ε)` sliver bound
    `hsliver`, the continuity `hcont`).  Pure composition; each carry is satisfiable, non-vacuous,
    strictly lower level than the conclusion, and none equals `a₁ = R/6`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem innerDiff_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- the shrunk frozen-provider carries (legs 2/3/4 discharged internally)
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
    (hRemainder : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
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
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w)) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.InnerDiffFamily.innerDiff_phase1 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont V hV
    (frozenData_of_remainder g gi hC hK S a b U V hLeviJoint hWitJointY hWitJointYbase
      hWFDjointY hFzero hFdomEvery hWitDomCappedY hRemainder)

end QIQTH.FrozenProviderLegs

/-! ## THE PROVIDER LEDGER — the per-leg table for the hQ1 frozen provider (with m-uniformity).

  `innerDiff_phase2` reproduces the per-`u` census `Tendsto` (= `innerDiff_phase1`'s conclusion) with
  the seven-leg frozen `hQ1` provider `hFrozenData` SHRUNK 7 → 4 by `frozenData_of_remainder`:

    leg          role                                        status          supplier / m-UNIFORMITY
    ──────────   ─────────────────────────────────────────  ──────────────  ────────────────────────
    (1) snb      real-line nbhd 𝓝(y i)                      REMAINDER       via `hRemainder`; per-(i,y)
    (2) hFmeas   `∀w, s↦∫z W(u−s)(update y i w)·F` aesm       ★ DISCHARGED    `frozenLeg_hFmeas` =
                                                             (this brick)    `innerIntegral_aesm` on
                                                                             `hWitJointY`·`hLeviJoint`;
                                                                             joints m-INDEPENDENT (∀d)
    (3) hFint    `s↦∫z W(u−s) y·F` interval-integrable        ★ DISCHARGED    `frozenLeg_hFint` =
                                                             (this brick)    `pairing_intervalIntegrable_
                                                                             lowerCapped` (A:=λτ_z,W τ y z)
                                                                             + Fubini hmeas on
                                                                             `hWitJointYbase`; carries
                                                                             `hFzero`/`hWitDomCappedY`/
                                                                             `hFdomEvery` m-INDEPENDENT
    (4) hF'meas  `s↦∫z dH i (u−s) y·F` aesm                   ★ DISCHARGED    `frozenLeg_hF'meas` =
                                                             (this brick)    `innerIntegral_aesm` on
                                                                             `hWFDjointY`·`hLeviJoint`;
                                                                             joints m-INDEPENDENT (∀d)
    (5) bound+hbdd  interval-integrable `s`-dominator         REMAINDER       via `hRemainder`; PER-m
                                                                             window (admissible — no
                                                                             m-series in hQ1)
    (6) hbound   `‖∫z dH…(update y i w)·F‖ ≤ bound s`          REMAINDER       via `hRemainder`; PER-m
    (7) hdiff    outer `s`-level `HasDerivAt (∫z W)(∫z dH)`    REMAINDER       via `hRemainder`; PER-m.
                                                                             J4-426 `innerZ_prod_
                                                                             hasDerivAt_witness` is 2nd-
                                                                             order/z-pointwise/base-0 —
                                                                             SHAPE MISMATCH, not wired

  ⚠ VERDICT.  The three diff-under-∫ side-condition legs (2)/(3)/(4) are DISCHARGED in the provider's
  exact shape, from m-INDEPENDENT joint `(s,z)` and Gaussian-domination carries, via the banked Fubini
  and capped-ceiling engines.  The honest REMAINDER is {snb, dominator, hbound, hdiff} = the analytic
  domination + pointwise-HasDerivAt content, which no measurability/integrability engine can supply.
  The M-UNIFORMITY TRAP does NOT bite: every discharged-leg carry is m-independent, and the per-`m`
  remainder legs are admissible because `hQ1` carries no series over `m`.  This brick proves NOTHING
  about `a₁ = R/6`; it certifies the hQ1 provider as reducible 7 → 4.  `a₁ = R/6` remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.FrozenProviderLegs
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms frozenLeg_hFmeas
#print axioms frozenLeg_hF'meas
#print axioms frozenLeg_hFint
#print axioms frozenData_of_remainder
#print axioms innerDiff_phase2
end AxiomChecks
