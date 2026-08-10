/-
  CurvedA1ClassBFint — J4-568.  Discharge the INTERVAL-INTEGRABILITY census carriers `hFint` and
  `hFint_d` of the fully-wired curved a₁ two-jet capstone
  `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` at the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`), via a genuine ε-FLOORED (capped) Gaussian domination.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This discharges TWO census binders — the s-slice
  interval-integrabilities

    hFint   : ∀ m i, ∀ u ∈ U, IntervalIntegrable
                (fun s => ∫ z, witnessFieldDeriv g^K … i (u−s) 0 z · leviSeries … s z 0) 0 (u−εₘ)
    hFint_d : ∀ m,   ∀ u ∈ U, IntervalIntegrable
                (fun s => ∫ z, vanVleckGatedWitness g^K … (u−s) 0 z · leviSeries … s z 0) 0 (u−εₘ)

  It does NOT make `a₁ = R/6` unconditional: the geometric residuals `hsrc` / `hOffCollarTail`, the
  convergence trio, `hInnerCont`, and the remaining analytic census all remain owed.

  ── WHY THE FLOORED / CAPPED DOMINATION (the vacuity minefield).  The banked width-flexible engine
  `DaLimEasyTranche.pairing_intervalIntegrable` demands a WHOLE-TIME Gaussian domination
  `∀ τ, 0 < τ → … |A τ 0 z| ≤ CA·gaussDdim (wA·τ)(0−z)`.  For `A = witnessFieldDeriv` (a FIRST spatial
  derivative of the parametrix) this CLEAN whole-time bound is FALSE at `g^K`: the spatial derivative
  of `G_τ` carries an extra `τ^(−1/2)` prefactor that blows up as `τ → 0` (documented for the
  second derivative in `CensusDominations` D3 / `CappedAdom2Audit`; the first derivative has the same
  `τ → 0` pathology, one power weaker).  Feeding the whole-time engine a `hAdom` of that clean shape
  would be a VACUITY TRAP.

  The honest route matches the capstone's OWN structure: the window is `[0, u−εₘ]`, on which the shift
  `τ = u−s ∈ [εₘ, u]` is BOUNDED AWAY FROM 0 by the floor `εₘ`.  So the derivative kernel is only ever
  sampled at `τ ≥ εₘ`, where the CAPPED domination `∀ τ, εₘ ≤ τ → τ ≤ T → |A τ 0 z| ≤ CA_m·gaussDdim
  (wA·τ)(0−z)` is GENUINELY TRUE (the `τ^(−1/2)` factor is `≤ εₘ^(−1/2)`, absorbed into the per-`m`
  constant `CA_m` — exactly the mechanism behind the landed `hAdom2cap`, J4-530..537).  This file
  builds the capped engine `pairing_intervalIntegrable_capped` (the whole engine content — Gaussian
  product ⟶ constant majorant ⟶ `Integrable.mono'` — carried over, with `A` sampled only on the
  ε-floored positive strip), and feeds it the g^K per-`m` capped dominations.

  ## What is closed

  •  `pairing_intervalIntegrable_capped` — the ε-FLOORED / capped-`A` interval-integrability engine
     (geometry-generic; the analytic content of both members, DISCHARGED).
  •  `curved_hFint_at_gate`   — the capstone `hFint`   binder shape at `g^K` (A = `witnessFieldDeriv`).
  •  `curved_hFint_d_at_gate` — the capstone `hFint_d` binder shape at `g^K` (A = `vanVleckGatedWitness`).
  •  `curved_hFint_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ## Carried residuals (honest Gaussian-domination carries — same KIND the census already runs on)

  Each supplier carries {`hAdom` (the CAPPED per-`m` Gaussian domination of the derivative / raw
  witness — genuinely true for `g^K`), `hFdom` (= the capstone's own `hFdomW` Levi domination),
  `hFzero` (leviSeries vanishing at nonpositive time — banked), `hmeas` (the s-slice
  measurability — banked, J4-562..567)}.  The interval-integrability ENGINE is DISCHARGED; the
  members are reduced to the SAME Gaussian-domination + measurability carries the rest of the census
  (`hAdomHeat`, `hFdomW`, `hmeasLo`, …) already stands on.

  ## ADVERSARIAL / satisfiability gate (`κ < 0`, `Ric ≠ 0`)

  Both members are genuine `IntervalIntegrable` facts about curved s-slice pairings, discharged from
  the capped engine.  The carried `hAdom` is the CAPPED (ε-floored) domination — the TRUE one for
  `g^K`, NOT the FALSE clean whole-time `hAdom2`.  Neither member is the capstone's conclusion, and
  neither touches the `R/6` coefficient.  They hold at the genuinely-curved `g^K` (`κ < 0`, where
  `Ric(0) = n(n−1)κ ≠ 0`, `curvedRNCMetric_ricci_trace_diag_ne`,
  `curved_hFint_at_gate_curved_satisfiable`).  No `sorry`, no new axioms, no `:= True`, no hypothesis
  = conclusion, no existing file edited.  NOT `a₁ = R/6`. -/
import Mathlib
import QIQTH.DaLimEasyTranche
import QIQTH.EngineInstantiation
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCGaussWitness
import QIQTH.A1R6CoreAtGate

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1ClassBFint

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE ε-FLOORED / CAPPED-`A` INTERVAL-INTEGRABILITY ENGINE.
    ###############################################################################

    A faithful ε-capped variant of `DaLimEasyTranche.pairing_intervalIntegrable`: the window is the
    ε-floored `[0, u−ε]`, on which `A` is sampled only at `τ = u−s ≥ ε`, so only the CAPPED
    domination `∀ τ, ε ≤ τ → …` is demanded (the clean whole-time bound is false for the derivative
    kernel).  Everything else — the Gaussian PRODUCT integral collapsing to the `s`-uniform constant
    `M := CA·CF·gaussDdim (min wA wF · u) 0`, and `Integrable.mono'` against the constant majorant —
    is the same engine as the uncapped lemma. -/

/-- **★ J4-568 (ENGINE) — `pairing_intervalIntegrable_capped`.**  For a bilinear `s`-profile
    `s ↦ ∫ z, A (u−s) 0 z · F s z 0` with `A` Gaussian-dominated ONLY on the ε-floored strip
    (`ε ≤ τ ≤ Tc`, width `wA`, constant `CA`), `F` Gaussian-dominated on `(0,Tc]` (width `wF`,
    constant `CF`) and vanishing at `s ≤ 0`, the profile is `IntervalIntegrable` on `[0, u−ε]`.
    On that window `s ≤ u−ε` ⟹ `u−s ≥ ε`, so the capped `A`-bound applies at every sampled `τ = u−s`
    (the strip `s ≤ 0` — nonempty only when `u−ε < 0` — is killed by `F ≡ 0`).  The `z`-pairing is a
    Gaussian PRODUCT integral `= gaussDdim (wA(u−s)+wF s) 0`, bounded `s`-uniformly by the constant
    `M := CA·CF·gaussDdim (min wA wF · u) 0` (`abLowerW` + `gaussDdim_zero_antitone`); `Integrable.mono'`
    against `M` on the finite-volume interval closes it.  ⚠ NOT `a₁ = R/6`. -/
theorem pairing_intervalIntegrable_capped
    (A F : ℝ → Point n → Point n → ℝ)
    (u Tc ε wA CA wF CF : ℝ)
    (hu : 0 < u) (huTc : u ≤ Tc) (hε : 0 < ε)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hAdom : ∀ τ : ℝ, ε ≤ τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ z, A (u - s) 0 z * F s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - ε)))) :
    IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * F s z 0) volume 0 (u - ε) := by
  set M : ℝ := CA * CF * gaussDdim (min wA wF * u) (0 : Point n) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (mul_nonneg hCA hCF) (gaussDdim_nonneg _ _)
  have hgconst : IntegrableOn (fun _ : ℝ => M) (Set.uIoc 0 (u - ε)) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hune : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ u := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton u
  refine (intervalIntegrable_iff).mpr (Integrable.mono' hgconst hmeas ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hune] with s hsmem hsne
  have hub : s ∈ Set.Ioc (min (0 : ℝ) (u - ε)) (max (0 : ℝ) (u - ε)) := hsmem
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0`: the source `F` vanishes, so the whole `z`-integral is `0`.
    have hzeroFun : (fun z => A (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    have hI0 : (∫ z, A (u - s) 0 z * F s z 0) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    simp only [hI0, norm_zero]; exact hMnn
  · -- `0 < s`: the window forces `s ≤ u − ε`, so `u − s ≥ ε` and the capped `A`-bound applies.
    have hsle : s ≤ u - ε := by
      have h2 : s ≤ max (0 : ℝ) (u - ε) := hub.2
      rcases max_cases (0 : ℝ) (u - ε) with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm] at h2; exact absurd h2 (not_le.mpr hs0)
      · rw [hm] at h2; exact h2
    have hsu' : s ≤ u := by linarith [hε.le]
    have hts : 0 < u - s := by linarith
    have hεus : ε ≤ u - s := by linarith
    have husTc : u - s ≤ Tc := le_trans (by linarith : u - s ≤ u) huTc
    set Dz : Point n → ℝ :=
      fun z => (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) with hDzdef
    have hDz_int : Integrable Dz volume := by
      rw [hDzdef]
      exact (gaussDdim_pair_integrable (wA * (u - s)) (wF * s)).const_mul (CA * CF)
    have hpt : ∀ z : Point n, ‖A (u - s) 0 z * F s z 0‖ ≤ Dz z := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      have hAz := hAdom (u - s) hεus husTc z
      rw [gaussDdim_zero_sub] at hAz
      have hFz := hFdom s hs0 (le_trans hsu' huTc) z
      rw [hDzdef]
      calc |A (u - s) 0 z| * |F s z 0|
          ≤ (CA * gaussDdim (wA * (u - s)) z) * (CF * gaussDdim (wF * s) z) :=
            mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA (gaussDdim_nonneg _ _))
        _ = (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) := by ring
    have hpair_le : gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
        ≤ gaussDdim (min wA wF * u) (0 : Point n) :=
      gaussDdim_zero_antitone (min wA wF * u) (wA * (u - s) + wF * s)
        (mul_pos (lt_min hwA hwF) hu) (abLowerW wA u wF s hs0.le hsu')
    have hDz_le : ∫ z, Dz z ≤ M := by
      have hval : (∫ z, Dz z) = (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n) := by
        rw [hDzdef, integral_const_mul,
          gaussDdim_pairing_integral (wA * (u - s)) (wF * s) (mul_pos hwA hts) (mul_pos hwF hs0)]
      rw [hval, hMdef]
      calc (CA * CF) * gaussDdim (wA * (u - s) + wF * s) (0 : Point n)
          ≤ (CA * CF) * gaussDdim (min wA wF * u) (0 : Point n) :=
            mul_le_mul_of_nonneg_left hpair_le (mul_nonneg hCA hCF)
        _ = CA * CF * gaussDdim (min wA wF * u) (0 : Point n) := by ring
    calc ‖∫ z, A (u - s) 0 z * F s z 0‖
        ≤ ∫ z, ‖A (u - s) 0 z * F s z 0‖ :=
          norm_integral_le_integral_norm (fun z => A (u - s) 0 z * F s z 0)
      _ ≤ ∫ z, Dz z :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hDz_int (ae_of_all _ hpt)
      _ ≤ M := hDz_le

/-! ###############################################################################
    ### AT-GATE INSTANCES — the exact capstone `hFint` / `hFint_d` binder shapes at `g^K`.
    ############################################################################### -/

/-- **★ J4-568 — `curved_hFint_at_gate`.**  The census carrier `hFint` of
    `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`: for every `m`, `i` and `u ∈ U`, the s-slice map
    `s ↦ ∫ z, witnessFieldDeriv g^K … i (u−s) 0 z · leviSeries … s z 0` is `IntervalIntegrable` on
    `[0, u−εₘ]`.  Discharged from the ε-floored engine `pairing_intervalIntegrable_capped`, fed the
    per-`m` CAPPED first-derivative Gaussian domination (`hAdom`, genuinely true for `g^K` since the
    kernel is only sampled at `τ = u−s ≥ εₘ`), the Levi domination (`hFdom`), the Levi vanishing
    (`hFzero`), and the s-slice measurability (`hmeas`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (U : Set ℝ) (T : ℝ)
    (wA : ℝ) (CA : ℕ → ℝ) (wF CF : ℝ)
    (hwA : 0 < wA) (hCA : ∀ m, 0 ≤ CA m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ CA m * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m i u hu
  exact pairing_intervalIntegrable_capped
    (fun τ p z => witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ p z)
    (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))
    u T (epsSeq m) wA (CA m) wF CF (hUpos u hu) (hUT u hu) (epsSeq_pos m)
    hwA (hCA m) hwF hCF
    (fun τ hτ hτT z => hAdom m i τ hτ hτT z) hFdom hFzero (hmeas m i u hu)

/-- **★ J4-568 — `curved_hFint_d_at_gate`.**  The census carrier `hFint_d` of the capstone at `g^K`:
    for every `m`, `u ∈ U`, the s-slice map
    `s ↦ ∫ z, vanVleckGatedWitness g^K … (u−s) 0 z · leviSeries … s z 0` is `IntervalIntegrable` on
    `[0, u−εₘ]`.  Same ε-floored engine, with `A := vanVleckGatedWitness` (the RAW order-0 witness);
    the carried `hAdom` is the per-`m` capped raw-witness Gaussian domination — genuinely true for
    `g^K` (the raw witness has NO derivative blow-up; the whole-time bound `curvedRNC_baseWitness_dom`
    already holds, and the capped form is weaker still).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_d_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (U : Set ℝ) (T : ℝ)
    (wA : ℝ) (CA : ℕ → ℝ) (wF CF : ℝ)
    (hwA : 0 < wA) (hCA : ∀ m, 0 ≤ CA m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ (m : ℕ) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z|
          ≤ CA m * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (u - s) (0 : Point n) z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m u hu
  exact pairing_intervalIntegrable_capped
    (fun τ p z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ p z)
    (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
      (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b)))
    u T (epsSeq m) wA (CA m) wF CF (hUpos u hu) (hUT u hu) (epsSeq_pos m)
    hwA (hCA m) hwF hCF
    (fun τ hτ hτT z => hAdom m τ hτ hτT z) hFdom hFzero (hmeas m u hu)

/-- **★ J4-568 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the two interval-
    integrability members are discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat
    `δ`.  NOT `a₁ = R/6`. -/
theorem curved_hFint_at_gate_curved_satisfiable (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1ClassBFint

section AxiomChecks
open QIQTH.CurvedA1ClassBFint
#print axioms pairing_intervalIntegrable_capped
#print axioms curved_hFint_at_gate
#print axioms curved_hFint_d_at_gate
#print axioms curved_hFint_at_gate_curved_satisfiable
end AxiomChecks
