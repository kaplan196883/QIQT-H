/-
  HDuhamelF2LiveWired — J4-908: the F2 inner-`s`-measurability/continuity pile of the LIVE
  order-1 `hDuhamel` capstone census, DISCHARGED to named F2 carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure find-and-wire brick.  It reduces FOUR still-open census binders of the LIVE capstone
  `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` — the inner space-time-pairing measurability/
  continuity slots
      • `hMeasFII`  (:173)  — base-window `s`-slice ae-meas of `∫ z, W(u−s)0z · F s z 0`,
      • `hInnerCont`(:177)  — interior-time continuity of the same on `Ioo 0 u`,
      • `hFmeas_d`  (:181)  — the `∀ c` truncated-window `s`-slice ae-meas,
      • `hF'meas_d` (:187)  — the `∂_r`-witness truncated-window `s`-slice ae-meas,
  where `W := vanVleckGatedWitness g gi hChr hK S a b` and `F = leviSeries (heatOp g gi W)` (the
  capstone's own `hFeq`) — from an OPAQUE assembled-inner-integral form to a THEOREM CONDITIONAL on the
  ALREADY-BANKED, std-3 `ContDomWindow.f2Pack_concrete_v3` (J4-245 / F2CarryDischarge2 / ContDomWindow
  stack).  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MATCH (character-checked, load-bearing).

  `ContDomWindow.f2Pack_concrete_v3` concludes EXACTLY the conjunction of the four propositions above
  with the concrete `leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))` written out in
  place of `F` — verified below by `subst hFeq` (which rewrites the LIVE census's `F` to that very Levi
  series) followed by a single `exact`.  So the four opaque LIVE census binders reduce to the named
  F2 carries of `f2Pack_concrete_v3`:
      {hΘc, hΘne, huc (van-Vleck / transport continuity + non-vanishing), hVmap0 (chart `z`-meas),
       hKSmeas (gate meas), hcar (the `Cfield` HasDerivAt chart-jet + measurability bundle),
       hLeviJoint (Levi joint `(s,z)`-meas on the truncated window), hBcont (Levi strip continuity),
       hUpos, hUT (window bounds), hAdom (width-`3/2` Gaussian dom of `W` — ITSELF a LIVE census binder),
       hBdom (width-`2` Gaussian dom of `leviSeries` — EQUALS the LIVE census binder `hFdom` under
       `hFeq`), hmeas + hcont (interior-slice a.e.-`z` measurability + a.e.-`z` time-continuity)}.
  Of these, `hAdom` / `hFdom (= hBdom)` / `hUT` are ALREADY present in the LIVE census (free); the
  remainder are standard geometric/measurability facts, with only `{hcar, hmeas, hcont}` genuinely-new
  residual — a NET DISCHARGE (opaque assembled ∫-measurability ⟹ primitive continuity/measurability/
  domination carries), NOT a relocation.

  ⚠  STILL NOT `a₁ = R/6`.  This closes four members of the ~60-binder `hDuhamel` census down to named
  satisfiable carries; the census as a whole (and `{hDConv, hCConv}`) is NOT discharged here.
-/
import QIQTH.ContDomWindow
import QIQTH.HDuhamelLiveGateWired

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelF2LiveWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDuhamel_F2_live_wired`.**  The FOUR inner space-time-pairing F2 census binders of the LIVE
    order-1 `hDuhamel` capstone `HDuhamelLiveGateWired.hDuhamel_live_gate_wired` —
    `hMeasFII`, `hInnerCont`, `hFmeas_d`, `hF'meas_d` — reproduced VERBATIM (at `F` with the capstone's
    own `hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))`) and reduced
    from opaque assembled-inner-integral binders to a THEOREM CONDITIONAL on the ALREADY-BANKED
    `ContDomWindow.f2Pack_concrete_v3` and its named F2 carries.  Route: `subst hFeq` rewrites the
    census `F` to the concrete Levi series, matching `f2Pack_concrete_v3`'s conclusion EXACTLY; a single
    `exact` closes it.  NONE of the carries is any of the four conclusions.  ⚠ NOT `a₁ = R/6`. -/
theorem hDuhamel_F2_live_wired (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmap0 : AEMeasurable
      (fun z : Point n => uniformInverseChart g gi hChr hK z (0 : Point n)) volume)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀) :
    -- (hMeasFII) — LIVE census binder, verbatim (with `F`)
    (∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- (hInnerCont) — LIVE census binder, verbatim (with `F`)
    ∧ (∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (Set.Ioo 0 u))
    -- (hFmeas_d) — LIVE census binder, verbatim (with `F`)
    ∧ (∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (hF'meas_d) — LIVE census binder, verbatim (with `F`)
    ∧ (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
          * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) := by
  subst hFeq
  exact QIQTH.ContDomWindow.f2Pack_concrete_v3 hn g gi hChr hK S a b T U hKm hSm0
    hΘc hΘne huc hVmap0 hKSmeas hcar hLeviJoint hBcont hUpos hUT
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hBdom hmeas hcont

end QIQTH.HDuhamelF2LiveWired

section AxiomChecks
open QIQTH.HDuhamelF2LiveWired
#print axioms hDuhamel_F2_live_wired
end AxiomChecks
