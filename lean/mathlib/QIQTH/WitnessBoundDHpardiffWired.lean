/-
  WitnessBoundDHpardiffWired — J4-918: the crude TIME-derivative envelope `witnessTimeDeriv_domination_global`
  (J4-917) WIRED into the LIVE census consumers `boundD` (J4-911) and `hpardiff` (J4-912/916), for the
  CONCRETE gated van-Vleck witness — fully closing `boundD` and driving `hpardiff` to its final named-carry
  state (the zeroth-amplitude sups `hAmp0`/`hCfield` + the measurability piles).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  COMPOSITION / wiring brick — it threads the ALREADY-BANKED discharge of the crude time-derivative
  envelope (`WitnessTimeDerivEnvelope.witnessTimeDeriv_domination_global`, the SOLE remaining carry
  `hAcrude` reduced to the mild zeroth-amplitude sups `{hAmp0, hCfield}`) into:
    •  `DerivDomLowerCapped.derivDom_boundD_of_crude` (J4-911) — the C3ε parameter-derivative dominator
       `boundD`/`hbdd_d`/`hbound_d` triple, at the LIVE census neighborhood `derivDomNb`;
    •  `HZDataFromCrudeEnv.witnessHZslice_of_crudeEnv` (J4-916) → `HpardiffZTimeDeriv.hpardiff_of_zTimeDeriv`
       (J4-912) — the parametric `hpardiff` binder.
  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis
  (satisfiability EXHIBITED below), none equal to (or trivially yielding) the conclusion, no existing file
  edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE τ-CAP ALIGNMENT.  The LIVE census `U` is bounded above by `T` (`hUT : ∀ u ∈ U, u ≤ T`) and the
  per-`(m,u)` derivative-time cap is `u + epsSeq m`.  Since `epsSeq m ≤ epsSeq 0 = 1` (`epsSeq_antitone`)
  and `u ≤ T`, every cap `u + epsSeq m ≤ T + 1`.  So ONE call to `witnessTimeDeriv_domination_global` at
  the GLOBAL cap `T + 1` supplies a single constant `Cwit` and width `4·D.lam` valid on all `(0, T+1]`,
  covering every per-`(m,u)` window — no per-window existential choice needed.  The witness envelope is
  centred `gaussDdim(w) z`; the consumers use `gaussDdim(w)(0−z)`; these agree by evenness
  (`gaussDdim_zero_sub`), rewritten with `← gaussDdim_zero_sub`.

  ## THE `hpardiff` `s ≤ 0` BRANCH.  `hpardiff`'s inner `hZ` family ranges over `s ∈ uIoc 0 (u−εₘ)`, which
  for `u − εₘ ≤ 0` includes `s ≤ 0`.  There the Levi source `F s z 0 = 0` (`hFzero`), so the integrand
  and its `z`-derivative vanish — the inner existential is produced by the trivial `Dz ≡ 0` witness.  For
  `s > 0` the window `[εₘ/2, u+εₘ]` strictly contains `c − s` (`c ∈ ball u (εₘ/2)`, `0 < s ≤ u−εₘ`), so
  `witnessHZslice_of_crudeEnv` fires with the SAME `Cwit`/`4·D.lam` envelope.

  ⚠  STILL NOT `a₁ = R/6`.  The remaining carries `{hAmp0, hCfield}` (zeroth amplitude / slope sups — the
  mild `WideAmplitudeData.hAmp0` class), the widened Levi envelope `{hFdom, hFzero}` (already in the live
  census), and the `z`-slice measurability / base-integrability piles `{hAmeas, hDmeas, hbase}` are named
  geometric / regularity inputs; this brick REDUCES `boundD`/`hpardiff` to them, it does NOT discharge them.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}` — the genuinely-hard residual wall in the
  shared census is `hCross` (mixed 2nd-difference bilinear Lipschitz, W5), untouched here.
-/
import QIQTH.DerivDomLowerCapped
import QIQTH.HZDataFromCrudeEnv
import QIQTH.HpardiffZTimeDerivReduction
import QIQTH.WitnessTimeDerivEnvelope

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.InverseChartNormalJets
open QIQTH.GatedTauDerivRep QIQTH.OnGateJets
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.VanVleck
open QIQTH.DerivDomLowerCapped QIQTH.HZDataFromCrudeEnv QIQTH.HpardiffZTimeDeriv
open QIQTH.WitnessTimeDerivEnvelope
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.WitnessBoundDHpardiffWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- `epsSeq m ≤ 1` (antitone below `epsSeq 0 = 1`). -/
theorem epsSeq_le_one (m : ℕ) : epsSeq m ≤ 1 :=
  le_trans (epsSeq_antitone (Nat.zero_le m)) (by norm_num [epsSeq])

/-! ###############################################################################
    ### §A — `boundD` FULLY WIRED (J4-911 engine + J4-917 envelope), concrete witness.
    ############################################################################### -/

/-- **★★★ J4-918 — `witnessBoundD_wired`.**  THE C3ε PARAMETER-DERIVATIVE DOMINATOR `boundD`, WIRED for the
    concrete gated van-Vleck witness at the LIVE census neighborhood `derivDomNb`.  Feeds
    `derivDom_boundD_of_crude` (J4-911) the crude time-derivative envelope `hAcrude` supplied by
    `witnessTimeDeriv_domination_global` (J4-917) at the global cap `T + 1` (`Ccr := Cwit`, `wL := 4·D.lam`)
    and the widened Levi envelope (`CF := C_L`, `wF := 2`).  Only remaining carries: the zeroth-amplitude
    sups `{hAmp0, hCfield}` + the already-census Levi envelope `{hFdom, hFzero}`.  ⚠ NOT `a₁ = R/6`. -/
theorem witnessBoundD_wired (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (M M' C_L : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hC_L : 0 ≤ C_L)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ boundD : ℕ → ℝ → ℝ → ℝ,
      (∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m)) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
        ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0‖
          ≤ boundD m u s) := by
  obtain ⟨Cwit, hCwitpos, hbound⟩ :=
    witnessTimeDeriv_domination_global hn g gi hC hK S a b D (T + 1) M M'
      (by linarith) hM hM' Cfield hgate hAmp0 hCfield hSupp
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  refine derivDom_boundD_of_crude
      (fun τ _ z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ)
      F U (fun _ _ => Cwit) (fun _ _ => 4 * D.lam) (fun _ _ => C_L) (fun _ _ => 2)
      (fun _ _ _ => hCwitpos.le) (fun _ _ _ => by show (0:ℝ) < 4 * D.lam; linarith)
      (fun _ _ _ => hC_L) (fun _ _ _ => two_pos)
      (fun s hs z => hFzero s hs z 0) ?_ ?_
  · -- hAcrude: the crude time-derivative envelope, from the global witness domination.
    intro m u hu τ hτ hτcap z
    have hτcap' : τ ≤ T + 1 :=
      le_trans hτcap (by have := hUT u hu; have := epsSeq_le_one m; linarith)
    have hb := hbound τ hτ hτcap' z
    rw [← gaussDdim_zero_sub (4 * D.lam * τ) z] at hb
    exact hb
  · -- hFdom: the widened Levi envelope, centred at `0`.
    intro m u hu s hs hscap z
    have hscap' : s ≤ T + 1 :=
      le_trans hscap (by have := hUT u hu; have := epsSeq_le_one m; linarith)
    have h := hFdom s hs hscap' z 0
    simpa only [sub_zero] using h

/-! ###############################################################################
    ### §B — `hpardiff` WIRED (J4-916 slice engine + J4-912 lift), concrete witness.
    ############################################################################### -/

/-- **★★★ J4-918 — `witnessHpardiff_wired`.**  THE parametric `hpardiff` census binder, WIRED for the
    concrete gated van-Vleck witness at the LIVE census neighborhood `derivDomNb`.  Builds the inner
    `z`-level `hZ` family per `(m,u,s,c)` via `witnessHZslice_of_crudeEnv` (J4-916, differentiability
    conjunct discharged by J4-915) fed the SAME global witness envelope, then lifts to the `z`-integral
    parametric `HasDerivAt` via `hpardiff_of_zTimeDeriv` (J4-912).  The `s ≤ 0` slices vanish (`hFzero`).
    Only remaining carries beyond `{hAmp0, hCfield}` + the census Levi envelope: the `z`-slice
    measurability / base-integrability piles `{hAmeas, hDmeas, hbase}`.  ⚠ NOT `a₁ = R/6`. -/
theorem witnessHpardiff_wired (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ)
    (T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (M M' C_L : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hC_L : 0 ≤ C_L)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hFdom : ∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAmeas : ∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (u' - s) 0 z * F s z 0) volume)
    (hDmeas : ∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0) volume)
    (hbase : ∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) :
    ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ derivDomNb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0) c := by
  obtain ⟨Cwit, hCwitpos, hbound⟩ :=
    witnessTimeDeriv_domination_global hn g gi hC hK S a b D (T + 1) M M'
      (by linarith) hM hM' Cfield hgate hAmp0 hCfield hSupp
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  refine hpardiff_of_zTimeDeriv (vanVleckGatedWitness g gi hC hK S a b) F U derivDomNb hAmeas ?_
  intro m u hu
  refine ae_of_all _ (fun s hsmem c hc => ?_)
  have he : 0 < epsSeq m := epsSeq_pos m
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0`: the Levi source vanishes; the inner existential is trivial.
    refine ⟨Set.univ, Filter.univ_mem, (fun _ => 0), integrable_zero _ _ _, ?_, ?_, ?_, ?_⟩
    · -- base slice integrable.
      have hz : (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0)
          = fun _ => (0 : ℝ) := by funext z; rw [hFzero s hs0 z 0, mul_zero]
      rw [hz]; exact integrable_zero _ _ _
    · -- derivative slice AE-measurable.
      have hz : (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s)
            * F s z 0) = fun _ => (0 : ℝ) := by funext z; rw [hFzero s hs0 z 0, mul_zero]
      rw [hz]; exact aestronglyMeasurable_const
    · -- pointwise dominator.
      refine ae_of_all _ (fun z c' _ => ?_)
      simp [hFzero s hs0 z 0]
    · -- pointwise time HasDerivAt.
      refine ae_of_all _ (fun z c' _ => ?_)
      simp only [hFzero s hs0 z 0, mul_zero]
      exact hasDerivAt_const c' (0 : ℝ)
  · -- `s > 0`: the genuine window `[εₘ/2, u+εₘ]` — fire `witnessHZslice_of_crudeEnv`.
    have hub : s ∈ Set.Ioc (min 0 (u - epsSeq m)) (max 0 (u - epsSeq m)) := hsmem
    have hsmax : s ≤ max 0 (u - epsSeq m) := hub.2
    have hue : 0 < u - epsSeq m := by
      by_contra h
      push_neg at h
      rw [max_eq_left h] at hsmax
      exact absurd (lt_of_lt_of_le hs0 hsmax) (lt_irrefl 0)
    have hsue : s ≤ u - epsSeq m := by rwa [max_eq_right hue.le] at hsmax
    have hcu : |c - u| < epsSeq m / 2 := by
      have hcb : c ∈ Metric.ball u (epsSeq m / 2) := hc
      rwa [Metric.mem_ball, Real.dist_eq] at hcb
    have hcuL : u - epsSeq m / 2 < c := by have := (abs_lt.mp hcu).1; linarith
    have hcuU : c < u + epsSeq m / 2 := by have := (abs_lt.mp hcu).2; linarith
    have hlo : epsSeq m / 2 < c - s := by linarith
    have hhi : c - s < u + epsSeq m := by linarith
    refine witnessHZslice_of_crudeEnv g gi hC hK S a b F s c
      (epsSeq m / 2) (u + epsSeq m) Cwit (4 * D.lam) C_L 2
      (by linarith) (by linarith) hCwitpos.le hC_L two_pos hs0 hlo hhi ?_ ?_
      (hDmeas s c) (hbase s c)
    · -- hAcrude slice: from the global witness domination on `[εₘ/2, u+εₘ] ⊆ (0, T+1]`.
      intro z τ hτmem
      have hτpos : 0 < τ := lt_of_lt_of_le (by linarith) hτmem.1
      have hτcap : τ ≤ T + 1 :=
        le_trans hτmem.2 (by have := hUT u hu; have := epsSeq_le_one m; linarith)
      have hb := hbound τ hτpos hτcap z
      rw [← gaussDdim_zero_sub (4 * D.lam * τ) z] at hb
      exact hb
    · -- hFdom slice: the widened Levi envelope at this `s`.
      intro z
      have hsc : s ≤ T + 1 :=
        le_trans hsue (by have := hUT u hu; have := epsSeq_le_one m; linarith)
      have h := hFdom s hs0 hsc z 0
      simpa only [sub_zero] using h

/-! ###############################################################################
    ### §C — NON-VACUITY: the full `witnessHpardiff_wired` hypothesis bundle is jointly satisfiable.
    ############################################################################### -/

/-- **Non-vacuity witness.**  For ANY concrete geometry `(g, gi, hC)` at the SINGLETON gate `K := {0}`
    (compact, NONEMPTY), the FULL hypothesis bundle of `witnessHpardiff_wired` (which SUBSUMES that of
    `witnessBoundD_wired`) is jointly satisfiable — `S := Set.univ`, the zero Levi source `F ≡ 0`
    (`C_L := 0`), the singleton census `U := Set.Icc 0 1` (`T := 1`), an explicit gate record `D`
    (`r = 1`, `η = 1/2`, `lam = 4`; its near-isometry gate holds trivially at `z = 0` since
    `rncRadialSq 0 = 0`), `Cfield` the AFFINE amplitude slope (exactly the `chartFieldAmp_hasDerivAt_tau`
    derivative), and the amplitude sups `M`, `M'` supplied by the AFFINE-in-`τ` structure at the single
    point `0` up to the cap `τ ≤ T + 1 = 2`.  So the wiring fires on a genuine nonempty gate, NOT an
    empty / unsatisfiable one.  NOT `a₁ = R/6`. -/
theorem witnessHpardiff_wired_hyp_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (a b : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (F : ℝ → Point n → Point n → ℝ)
      (T : ℝ) (U : Set ℝ) (M M' C_L : ℝ) (Cfield : Point n → Point n → ℝ),
      (0 : Point n) ∈ K ∧ 0 < T ∧ (∀ u ∈ U, u ≤ T) ∧ 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ C_L ∧
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) ∧
      (∀ τ, 0 < τ → τ ≤ T + 1 → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0) ∧
      (∀ s, 0 < s → s ≤ T + 1 → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) ∧
      (∀ (s u' : ℝ), AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (u' - s) 0 z * F s z 0) volume) ∧
      (∀ (s c : ℝ), AEStronglyMeasurable
        (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) (c - s) * F s z 0)
        volume) ∧
      (∀ (s c : ℝ), Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (c - s) 0 z * F s z 0) volume) := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  set Cf : Point n → Point n → ℝ := fun z p =>
    radialCutoff a b (uniformInverseChart g gi hC hK0 z p)
      * (VanVleck.vanVleck g (uniformInverseChart g gi hC hK0 z p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (VanVleck.vanVleck g) g gi) 1
              (uniformInverseChart g gi hC hK0 z p))
    with hCfdef
  refine ⟨({0} : Set (Point n)), hK0, fun _ => Set.univ,
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ },
    (fun _ _ _ => 0), 1, Set.Icc 0 1,
    |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| * 2, |Cf 0 0|, 0, Cf,
    Set.mem_singleton_iff.mpr rfl, one_pos, (fun u hu => hu.2),
    by positivity, abs_nonneg _, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hgate: `S = univ` frees the gate membership; HasDerivAt is `chartFieldAmp_hasDerivAt_tau`.
    intro w _ _
    exact ⟨Set.mem_univ _, chartFieldAmp_hasDerivAt_tau g gi hC hK0 a b w.2.2 w.2.1 w.1⟩
  · -- hAmp0: only `z = 0`; affine-in-τ bound up to the cap `τ ≤ 2`.
    intro τ hτ hτ2 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    have haff : chartFieldAmp g gi hC hK0 a b τ 0 0
        = chartFieldAmp g gi hC hK0 a b 0 0 0 + Cf 0 0 * τ := by
      simp only [hCfdef, chartFieldAmp]; ring
    rw [haff]
    have hτ2' : τ ≤ 2 := by linarith
    calc |chartFieldAmp g gi hC hK0 a b 0 0 0 + Cf 0 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| * 2 := by
          have : |Cf 0 0| * τ ≤ |Cf 0 0| * 2 := mul_le_mul_of_nonneg_left hτ2' (abs_nonneg _)
          linarith
  · -- hCfield: only `z = 0`; `|Cf 0 0| ≤ |Cf 0 0|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _
  · -- hSupp: only `z = 0`; `‖0‖ = 0 < 1`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    simp
  · -- hFzero: `F ≡ 0`.
    intro s _ z y; rfl
  · -- hFdom: `|0| ≤ 0 * gaussDdim …`.
    intro s _ _ z y; simp
  · -- hAmeas: `F ≡ 0`, so the integrand is `0`.
    intro s u'; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hDmeas: same.
    intro s c; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hbase: same.
    intro s c; simp only [mul_zero]; exact integrable_zero _ _ _

end QIQTH.WitnessBoundDHpardiffWired

section AxiomChecks
open QIQTH.WitnessBoundDHpardiffWired
#print axioms epsSeq_le_one
#print axioms witnessBoundD_wired
#print axioms witnessHpardiff_wired
#print axioms witnessHpardiff_wired_hyp_satisfiable
end AxiomChecks
