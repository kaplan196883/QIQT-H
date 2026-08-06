/-
  DaLimEasyTranche — J4-332: the EASY TRANCHE (items 1–3) of the `hDaLimLU_concrete` remainder
  (the dependency-ordered `X2` remainder classified by J4-331 `DaLimCensusRecon`) DISCHARGED at the
  concrete `N = 1` van-Vleck gate `H_G := vanVleckGatedWitness g gi hChr hK S a b`, source
  `F := leviSeries (heatOp g gi H_G)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  discharge of the three EASY `hDaLimLU_concrete` binders at the concrete gate.  No `sorry` (header
  prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis
  equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed.
  `hDaLimLU_concrete` remains the concrete-gate `Da`-limit and is NOT the `a₁ = R/6` diagonal.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## Z0 — THE RECON (EXACT binder types copied from `DaLimLUConcreteDischarge.hDaLimLU_concrete`,
     with `F` at the gate `:= leviSeries (heatOp g gi H_G)` and `pdpdH := witnessSecondXDeriv …`).

  ── ITEM 1 — `hFzero` (leviSeries empty-interval vanishing at `τ ≤ 0`) ──────────────────────────────
     BINDER (line 170):  `hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0`.
     ROUTE / VERDICT — DISCHARGED (Z1 `hFzero_concrete`).  The residual `E = heatOp g gi H_G` vanishes
     at `τ ≤ 0` (`DataPileWitnessAudit.hEzeroE_concrete`, needs `1 ≤ n`); each iterated convolution
     `iterE E (k+1)` then vanishes at `s ≤ 0` (`iterE_eq_zero_of_nonpos`, `Nat.le_induction`: base
     `iterE E 1 = E`; step `heatConvK E _` integrates `∫ r in 0..s` of an integrand that is `0` on the
     WHOLE `uIcc 0 s ⊆ (-∞,0]` because `E (s − r) = 0` there, via `intervalIntegral.integral_congr`
     + `integral_zero`).  Hence `leviSeries E s z y = ∑' k, ± iterE E (k+1) s z y = ∑' 0 = 0`.
     SAT: honest, trivial content; every carry satisfiable (`hEzero` holds for the gate at `1 ≤ n`).

  ── ITEM 2 — `hFdom` (Levi source Gaussian domination, width 2) ─────────────────────────────────────
     BINDER (line 169):  `hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
                                     |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)`.
     ROUTE / VERDICT — DISCHARGED (Z2 `hFdom_concrete`).  The WIDTH MATCHES the banked width-2 Levi
     envelope `LeviSeriesLocalData.hFenv` (= `GatedWitnessPackage.leviSeries_dominatedW_le`):
     `∃ C_L ≥ 0, ∀ τ p q, 0<τ → τ≤T → |leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q`; and
     `baseKernelW 2 0 s z y = gaussDdim (2·s) (z−y)` (`ParametrixHEboundWiring.baseKernelW_zero_apply`).
     Honest carry = the `LeviSeriesLocalData E C T` package (the full RNC geometry pile + base
     measurability behind it); `C_L` is EXTRACTED from `.hFenv`, both `z`,`y` free.  SAT: the landed
     J4-324 Levi domination, satisfiable at the concrete gate.

  ── ITEM 3 — `hIlo`/`hIhi` (strip) + `hII_lo`/`hII_hi` (adjacency) interval-integrabilities ──────────
     BINDER `hIlo`/`hIhi` (lines 171–178):  `∀ m, ∀ u ∈ U, IntervalIntegrable
         (fun s => ∫ z, heatOp g gi H_G (u−s) 0 z * F s z 0) volume 0 (u−ε_m)`  [resp. `(u−ε_m) u`].
     BINDER `hII_lo`/`hII_hi` (= `MemAdjLo`/`MemAdjHi`, lines 157–158):  `∀ m i, ∀ u ∈ U,
         IntervalIntegrable (fun s => ∫ z, witnessSecondXDeriv … i (u−s) z * F s z 0) volume
         0 (u−ε_m)`  [resp. `(u−ε_m) u`].
     ROUTE / VERDICT — DISCHARGED (Z3, via the generic `pairing_intervalIntegrable`).  Both factors are
     Gaussian-dominated (`A(u−s)0 z` by `CA·gaussDdim (wA(u−s))(0−z)`, `F s z 0` by `CF·gaussDdim
     (wF s) z`); the `z`-pairing is a Gaussian PRODUCT integral `= gaussDdim (wA(u−s)+wF s) 0`
     (`CConvV2GaussianPairing.gaussDdim_pairing_integral`), whose peak is bounded `s`-UNIFORMLY by
     `gaussDdim (min wA wF · u) 0` (`gaussDdim_zero_antitone` + `CConvV2WitnessStar.abLowerW`).  Hence
     the `s`-profile is bounded by the CONSTANT `M := CA·CF·gaussDdim (min wA wF · u) 0` a.e. on the
     (bounded, finite-volume) interval, so `IntervalIntegrable` follows by `Integrable.mono'` against
     the constant majorant — NO `s`-singularity, no `(t−s)^{−1/2}` sliver.  Honest carries: the two
     Gaussian dominations (banked-shaped: `hEbound`/`hFenv`-derived) + the `s`-profile measurability
     `hmeas` (the sole side condition, true for `F ≡ 0`).  SAT: routine, no singular prefactor.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DaLimLUConcreteDischarge
import QIQTH.LeviSeriesLocalData
import QIQTH.CConvV2WitnessStar
import QIQTH.AmplitudePackage

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.LeviSeriesLocalData
open QIQTH.DaLimLUWallRecon QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimEasyTranche

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Z1 — ITEM 1: the source vanishing `hFzero` at `τ ≤ 0`.
    ############################################################################### -/

/-- **`iterE_eq_zero_of_nonpos`.**  If the residual `E` vanishes at every nonpositive time, then so
    does every iterated convolution `iterE E k` (`k ≥ 1`) at nonpositive time.  `Nat.le_induction`:
    base `iterE E 1 = E` (`iterE_one`); step `iterE E (k+1) = heatConvK E (iterE E k)`
    (`iterE_succ`), whose `heatConv` integrand `∫ z, E (s − r) x z · iterE E k r z y` is `0` on the
    WHOLE `uIcc 0 s ⊆ (−∞,0]` (there `s − r ≤ 0`, so `E (s − r) = 0`), hence the `∫ r in 0..s`
    interval integral vanishes (`intervalIntegral.integral_congr` + `intervalIntegral.integral_zero`).
    ⚠ NOT `a₁ = R/6`. -/
theorem iterE_eq_zero_of_nonpos (E : ℝ → Point n → Point n → ℝ)
    (hE : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) :
    ∀ (k : ℕ), 1 ≤ k → ∀ s : ℝ, s ≤ 0 → ∀ x y : Point n, iterE E k s x y = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro s hs x y
      rw [iterE_one]
      exact hE s hs x y
  | succ m hm _ =>
      intro s hs x y
      rw [iterE_succ E hm, heatConvK_apply]
      simp only [heatConv]
      -- the `∫ r in 0..s` integrand is `0` on `uIcc 0 s = Icc s 0`.
      have hEqOn : Set.EqOn
          (fun r => ∫ z, E (s - r) x z * iterE E m r z y)
          (fun _ => (0 : ℝ)) (Set.uIcc (0 : ℝ) s) := by
        intro r hr
        rw [Set.uIcc_of_ge hs] at hr
        obtain ⟨hsr, _⟩ := Set.mem_Icc.mp hr
        have hzero : (fun z => E (s - r) x z * iterE E m r z y) = fun _ => (0 : ℝ) := by
          funext z
          rw [hE (s - r) (by linarith) x z, zero_mul]
        simp only [hzero]
        exact integral_zero (Point n) ℝ
      rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_zero]

/-- **`leviSeries_eq_zero_of_nonpos`.**  If the residual `E` vanishes at every nonpositive time then
    the signed Levi series `leviSeries E` vanishes at nonpositive time: every term
    `(−1)^(k+1) · iterE E (k+1) s z y` is `0` (`iterE_eq_zero_of_nonpos`), so the `tsum` is `0`.
    ⚠ NOT `a₁ = R/6`. -/
theorem leviSeries_eq_zero_of_nonpos (E : ℝ → Point n → Point n → ℝ)
    (hE : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) :
    ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n, leviSeries E s z y = 0 := by
  intro s hs z y
  simp only [leviSeries]
  have hterm : (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) s z y) = fun _ => (0 : ℝ) := by
    funext k
    rw [iterE_eq_zero_of_nonpos E hE (k + 1) (by omega) s hs z y, mul_zero]
  rw [hterm]
  exact tsum_zero

/-- **★ Z1 (ITEM 1) — `hFzero_concrete`.**  The concrete-gate `hFzero` binder: the Levi source
    `F := leviSeries (heatOp g gi H_G)` vanishes at nonpositive time.  From
    `DataPileWitnessAudit.hEzeroE_concrete` (`heatOp g gi H_G` vanishes at `τ ≤ 0`, needs `1 ≤ n`)
    fed to `leviSeries_eq_zero_of_nonpos`.  EXACT binder shape (`∀ s, s ≤ 0 → ∀ z y, F s z y = 0`).
    ⚠ NOT `a₁ = R/6`. -/
theorem hFzero_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hn : 1 ≤ n) :
    ∀ s : ℝ, s ≤ 0 → ∀ z y : Point n,
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0 :=
  leviSeries_eq_zero_of_nonpos (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (QIQTH.DataPileWitnessAudit.hEzeroE_concrete g gi hChr hK S a b hn)

/-! ###############################################################################
    ### Z2 — ITEM 2: the source Gaussian domination `hFdom` (width 2).
    ############################################################################### -/

/-- **★ Z2 (ITEM 2) — `hFdom_concrete`.**  The concrete-gate `hFdom` binder: the Levi source
    `F := leviSeries E` obeys the width-2 Gaussian domination `∃ C_L ≥ 0, ∀ s, 0<s → s≤T → ∀ z y,
    |F s z y| ≤ C_L · gaussDdim (2·s) (z−y)`.  Extract `C_L` from `LeviSeriesLocalData.hFenv`
    (the banked width-2 Levi envelope) and rewrite `baseKernelW 2 0 s z y = gaussDdim (2·s) (z−y)`
    (`baseKernelW_zero_apply`).  Generic in `E`; the honest carry is the `LeviSeriesLocalData E C T`
    package (the RNC geometry pile + base measurability behind the banked domination).  ⚠ NOT
    `a₁ = R/6`. -/
theorem hFdom_concrete (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (data : LeviSeriesLocalData E C T) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries E s z y| ≤ C_L * gaussDdim (2 * s) (z - y) := by
  obtain ⟨C_L, hCL0, hLdom⟩ := data.hFenv
  refine ⟨C_L, hCL0, fun s hs hsT z y => ?_⟩
  have h := hLdom s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

/-! ###############################################################################
    ### Z3 — ITEM 3: the strip / adjacency interval-integrabilities.
    ############################################################################### -/

/-- **★ Z3 (ITEM 3, engine) — `pairing_intervalIntegrable`.**  The generic pairing interval-
    integrability behind `hIlo`/`hIhi` (`A := heatOp g gi H_G`) and `hII_lo`/`hII_hi`
    (`A := witnessSecondXDeriv …`).  For a bilinear `s`-profile `s ↦ ∫ z, A (u−s) 0 z · F s z 0`
    with BOTH factors Gaussian-dominated on the window (widths `wA`, `wF`; constants `CA`, `CF`) and
    `F` vanishing at `s ≤ 0`, the `z`-pairing integral is bounded `s`-UNIFORMLY by the CONSTANT
    `M := CA·CF·gaussDdim (min wA wF · u) 0`: the widths satisfy `min wA wF · u ≤ wA(u−s)+wF s`
    (`abLowerW`), so the Gaussian PRODUCT peak `gaussDdim (wA(u−s)+wF s) 0`
    (`gaussDdim_pairing_integral`) is `≤ gaussDdim (min wA wF · u) 0` (`gaussDdim_zero_antitone`).
    Hence `IntervalIntegrable` on ANY `[α,β] ⊆ (−∞,u]` follows from `Integrable.mono'` against the
    constant `M` on the (finite-volume) interval.  Carries: the two Gaussian dominations + the
    `s`-profile measurability `hmeas` (the sole side condition, true for `F ≡ 0`).  NO singular
    prefactor.  ⚠ NOT `a₁ = R/6`. -/
theorem pairing_intervalIntegrable
    (A F : ℝ → Point n → Point n → ℝ)
    (u Tc wA CA wF CF : ℝ)
    (hu : 0 < u) (huTc : u ≤ Tc)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hAdom : ∀ τ : ℝ, 0 < τ → τ ≤ Tc → ∀ z : Point n,
        |A τ 0 z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, F s z 0 = 0)
    (α β : ℝ) (hαu : α ≤ u) (hβu : β ≤ u)
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ z, A (u - s) 0 z * F s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc α β))) :
    IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * F s z 0) volume α β := by
  set M : ℝ := CA * CF * gaussDdim (min wA wF * u) (0 : Point n) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact mul_nonneg (mul_nonneg hCA hCF) (gaussDdim_nonneg _ _)
  -- the constant majorant is integrable on the finite-volume interval.
  have hgconst : IntegrableOn (fun _ : ℝ => M) (Set.uIoc α β) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  -- `s ≠ u` holds `a.e.`
  have hune : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ u := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton u
  refine (intervalIntegrable_iff).mpr (Integrable.mono' hgconst hmeas ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hune] with s hsmem hsne
  -- `s ≤ u` from membership in `Ι α β` and `α,β ≤ u`.
  have hub : s ∈ Set.Ioc (min α β) (max α β) := hsmem
  have hsu' : s ≤ u := le_trans hub.2 (max_le hαu hβu)
  rcases le_or_gt s 0 with hs0 | hs0
  · -- `s ≤ 0`: the source `F` vanishes, so the whole `z`-integral is `0`.
    have hzeroFun : (fun z => A (u - s) 0 z * F s z 0) = fun _ => (0 : ℝ) := by
      funext z; rw [hFzero s hs0 z, mul_zero]
    have hI0 : (∫ z, A (u - s) 0 z * F s z 0) = 0 := by
      rw [hzeroFun]; exact integral_zero (Point n) ℝ
    simp only [hI0, norm_zero]; exact hMnn
  · -- `0 < s < u`: Gaussian-pairing constant bound.
    have hsu : s < u := lt_of_le_of_ne hsu' hsne
    have hts : 0 < u - s := by linarith
    -- the dominating integrand over `z`.
    set Dz : Point n → ℝ :=
      fun z => (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) with hDzdef
    have hDz_int : Integrable Dz volume := by
      rw [hDzdef]
      exact (gaussDdim_pair_integrable (wA * (u - s)) (wF * s)).const_mul (CA * CF)
    have hpt : ∀ z : Point n, ‖A (u - s) 0 z * F s z 0‖ ≤ Dz z := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      have hAz := hAdom (u - s) hts (by linarith) z
      rw [gaussDdim_zero_sub] at hAz
      have hFz := hFdom s hs0 (le_trans hsu' huTc) z
      rw [hDzdef]
      calc |A (u - s) 0 z| * |F s z 0|
          ≤ (CA * gaussDdim (wA * (u - s)) z) * (CF * gaussDdim (wF * s) z) :=
            mul_le_mul hAz hFz (abs_nonneg _) (mul_nonneg hCA (gaussDdim_nonneg _ _))
        _ = (CA * CF) * (gaussDdim (wA * (u - s)) z * gaussDdim (wF * s) z) := by ring
    -- the `s`-uniform constant bound on the pairing integral.
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

/-- **★ Z3 (ITEM 3·a) — `hIlo_concrete`.**  The strip interval-integrability on `[0, u−ε_m]` of the
    `E·F` inner pairing at the concrete gate (`E = heatOp g gi H_G`, `F = leviSeries E`), for every
    `m` and `u ∈ U`.  From `pairing_intervalIntegrable` with `A := E`, the width-`wA` heat-operator
    Gaussian bound (`hAdom`), the width-`wF` Levi bound (`hFdom`), the source vanishing (`hFzero`),
    and the `s`-profile measurability (`hmeas`).  ⚠ NOT `a₁ = R/6`. -/
theorem hIlo_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA CA wF CF : ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m) := by
  intro m u hu
  exact pairing_intervalIntegrable
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    u T wA CA wF CF (hUpos u hu) (hUT u hu) hwA hCA hwF hCF hAdom hFdom hFzero
    0 (u - epsSeq m) (le_of_lt (hUpos u hu)) (by have := epsSeq_pos m; linarith)
    (hmeas m u hu)

/-- **★ Z3 (ITEM 3·b) — `hIhi_concrete`.**  The strip interval-integrability on `[u−ε_m, u]`, the
    adjacency-`hi` companion of `hIlo_concrete`.  Same carries; `α = u−ε_m ≤ u`, `β = u`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hIhi_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA CA wF CF : ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u))) :
    ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume (u - epsSeq m) u := by
  intro m u hu
  exact pairing_intervalIntegrable
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    u T wA CA wF CF (hUpos u hu) (hUT u hu) hwA hCA hwF hCF hAdom hFdom hFzero
    (u - epsSeq m) u (by have := epsSeq_pos m; linarith) le_rfl (hmeas m u hu)

/-- **★ Z3 (ITEM 3·c) — `hII_lo_concrete`.**  The adjacency interval-integrability `MemAdjLo` on
    `[0, u−ε_m]` of the `pdpdH·F` pairing at `pdpdH := witnessSecondXDeriv …`, `F := leviSeries E`.
    From `pairing_intervalIntegrable` with `A := fun τ _ z => witnessSecondXDeriv … i τ z` (the middle
    point slot ignored), the second-`x`-partial Gaussian bound (`hAdom`), the Levi bound (`hFdom`),
    the source vanishing (`hFzero`), and measurability (`hmeas`).  ⚠ NOT `a₁ = R/6`. -/
theorem hII_lo_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (E : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T wA CA wF CF : ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries E s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, leviSeries E s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * leviSeries E s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    MemAdjLo (leviSeries E) U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  intro m i u hu
  exact pairing_intervalIntegrable
    (fun τ _ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) (leviSeries E)
    u T wA CA wF CF (hUpos u hu) (hUT u hu) hwA hCA hwF hCF
    (fun τ hτ hτT z => hAdom i τ hτ hτT z) hFdom hFzero
    0 (u - epsSeq m) (le_of_lt (hUpos u hu)) (by have := epsSeq_pos m; linarith)
    (hmeas m i u hu)

/-- **★ Z3 (ITEM 3·d) — `hII_hi_concrete`.**  The adjacency interval-integrability `MemAdjHi` on
    `[u−ε_m, u]`, the companion of `hII_lo_concrete`.  ⚠ NOT `a₁ = R/6`. -/
theorem hII_hi_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (E : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T wA CA wF CF : ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries E s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, leviSeries E s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * leviSeries E s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u))) :
    MemAdjHi (leviSeries E) U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  intro m i u hu
  exact pairing_intervalIntegrable
    (fun τ _ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) (leviSeries E)
    u T wA CA wF CF (hUpos u hu) (hUT u hu) hwA hCA hwF hCF
    (fun τ hτ hτT z => hAdom i τ hτ hτT z) hFdom hFzero
    (u - epsSeq m) u (by have := epsSeq_pos m; linarith) le_rfl (hmeas m i u hu)

end QIQTH.DaLimEasyTranche

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimEasyTranche.pairing_intervalIntegrable
#print axioms QIQTH.DaLimEasyTranche.hIlo_concrete
#print axioms QIQTH.DaLimEasyTranche.hIhi_concrete
#print axioms QIQTH.DaLimEasyTranche.hII_lo_concrete
#print axioms QIQTH.DaLimEasyTranche.hII_hi_concrete
#print axioms QIQTH.DaLimEasyTranche.iterE_eq_zero_of_nonpos
#print axioms QIQTH.DaLimEasyTranche.leviSeries_eq_zero_of_nonpos
#print axioms QIQTH.DaLimEasyTranche.hFzero_concrete
#print axioms QIQTH.DaLimEasyTranche.hFdom_concrete
