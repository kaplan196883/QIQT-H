/-
  # QIQTH.UniformCRDischarge — J4-157: the m-UNIFORM `C_R` plumbing.

  ## What this file does (HONEST FIREWALL).
  This file closes ONE bookkeeping brick of the a₁ = R/6 campaign: the `witness → hbnd` chain for
  the concrete formal-Hessian sliver.  It proves **NOTHING** about `a₁ = R/6`.

  The terminal sliver bound `GaussReplaceSlice.witness_sliver2_grand` / `RemainderIntegration.
  witness_sliver2_complete` is stated in the **per-ε existential form**
      `∀ ε (with the ε-side-conditions), ∃ C_R ≥ 0, |∫ᵉ sliver| ≤ ((15/2·n·L + C_R) + C₁)·2√ε + C₂·ε`.
  The witnessed constant `C_R = C_E1 + C_E2` produced by `tE1_slice_bound` / `tE2_slice_bound` is,
  at the VALUE level, **ε-free** (it is built only from the FIXED strip/moduli data
  `n, L, M₀, M₁, M₂, C_L, T, a, τ₀, C_W, C_P, C_Q` — read `tE2_slice_bound`'s witness, lines 148-155
  of `RemainderIntegration.lean`, which contains no `ε`).  But because the `∃ C_R` sits INSIDE the
  `∀ ε`, re-applying the grand at each `ε := epsSeq m` yields a syntactically DIFFERENT constant per
  `m`, which the `hbnd` slot (`SliverSumPlumbing` / `EngineInstantiation.hbnd_witness_supplied`)
  cannot consume — it needs ONE `D0`/`D1` for all `m`.

  THE MOVE (U1, `witness_sliver2_eventual`): extract the remainder constant `C_R` **once** at a fixed
  master gap `ε₀` via `hRem_discharge` (whose `hRemE1` half is itself discharged by `tE1_slice_bound`
  at `ε₀`), then feed `witness_sliver2_final` — which takes `C_R` as an EXPLICIT argument — at every
  `ε := epsSeq m ≤ ε₀` by restricting the per-slice remainder bound from the master window
  `Ioo (u−ε₀) u` down to `Ioo (u−epsSeq m) u`.  The resulting `D0 = (15/2·n·L + C_R) + C₁`,
  `D1 = C₂` are `m`-uniform.  This is EXACTLY the eventual per-`m` shape that
  `EngineInstantiation.hbnd_witness_supplied` (via `hbnd_from_eventual`) extends to all `m`.

  THE CLOSURE (U2, `hbnd_witness_final`): package the per-coordinate `witness_sliver2_eventual`
  outputs (with the common, `i`-independent `M₀`) into `hbnd_witness_supplied`'s `heventual` slot,
  delivering the ∀`m` `hbnd` consumed by the sliver-sum plumbing — the `witness → hbnd` chain CLOSED.

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses (all carries are the
  standard analytic strip data, satisfiable e.g. by `Y = −id`).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### U1 — the constants-first restatement: `m`-UNIFORM `C_R`, eventual `√ε` bound.
    ############################################################################### -/

/-- **★★★ U1 — `witness_sliver2_eventual`.**  The `m`-UNIFORM restatement of the terminal
    formal-Hessian sliver bound.  Under the FIXED strip + moduli hypothesis family of
    `witness_sliver2_final`/`hRem_discharge`/`tE1_slice_bound` (the ε-dependent integrability and
    Lipschitz carries phrased over the MASTER window `Ioo (u−ε₀) u`), there are `m`-uniform
    amplitudes `D0, D1 ≥ 0` and a threshold `M₀` such that for every `m ≥ M₀` BOTH the three sliver
    side conditions (`epsSeq m ≤ u ∧ < a/2 ∧ ≤ τ₀`, from `epsSeq_sliver_side_conditions`) hold AND
      `|∫ s in (u − epsSeq m)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ D0·(2√(epsSeq m)) + D1·epsSeq m`.
    The key move: the remainder constant `C_R` is extracted ONCE (at the master gap `ε₀`) and the
    explicit-`C_R` composite `witness_sliver2_final` is fired at each `ε := epsSeq m ≤ ε₀` by
    restricting the master-window carries — so `D0 = (15/2·n·L + C_R) + C₁`, `D1 = C₂` do NOT depend
    on `m`.  This is EXACTLY `hbnd_witness_supplied`'s `heventual` input.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_eventual
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (i : Fin n) (L M₀ M₁ M₂ C_L T a τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε₀ : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hu0 : 0 < u) (hτ₀0 : 0 < τ₀)
    (hε₀0 : 0 < ε₀) (hε₀a : ε₀ < a / 2) (hε₀τ : ε₀ ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z + sTerm2 Y A2 τ z)
    (hIntT1 : ∀ s ∈ Set.Ioo (u - ε₀) u,
        Integrable (fun z => (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT2 : ∀ s ∈ Set.Ioo (u - ε₀) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z 0)) volume)
    (hIntT3 : ∀ s ∈ Set.Ioo (u - ε₀) u,
        Integrable (fun z => ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
            * (A0 (u - s) z * F s z 0)) volume)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε₀) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M)
    (hInt1 : ∀ s ∈ Set.Ioo (u - ε₀) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε₀) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z 0) volume) :
    ∃ (D0 D1 : ℝ) (M₀nat : ℕ), 0 ≤ D0 ∧ 0 ≤ D1 ∧
      ∀ m : ℕ, M₀nat ≤ m →
        (epsSeq m ≤ u ∧ epsSeq m < a / 2 ∧ epsSeq m ≤ τ₀) ∧
        |∫ s in (u - epsSeq m)..u, ∫ z, D2H (u - s) z * F s z 0|
          ≤ D0 * (2 * Real.sqrt (epsSeq m)) + D1 * epsSeq m := by
  -- (1) master extraction of the E1 half at the fixed gap `ε₀`.
  obtain ⟨C_E1, hC_E1nn, hE1m⟩ := tE1_slice_bound Y P Q A0 F i M₀ C_L T a u ε₀ τ₀ C_W C_P C_Q
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hε₀0.le hε₀a hε₀τ hco hYdisp hJ3 hJ3Q hA0bdd hFdom
  -- (2) master extraction of the entangled remainder constant `C_R = C_E1 + C_E2` at `ε₀`.
  obtain ⟨C_R, hC_Rnn, hRemM⟩ := hRem_discharge Y P Q A0 F i M₀ C_L T a u ε₀ τ₀ C_W C_P C_Q C_E1
    hM₀ hC_L hC_W hC_P hC_Q hC_E1nn ha hau huT hε₀0.le hε₀a hε₀τ hYdisp hJ3 hJ3Q hA0bdd hFdom
    hE1m hIntT1 hIntT2 hIntT3
  -- (3) the eventual windows: side conditions (`u`,`a`,`τ₀`) and `epsSeq m ≤ ε₀`.
  obtain ⟨N1, hN1⟩ := epsSeq_sliver_side_conditions u a τ₀ hu0 ha hτ₀0
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (epsSeq_eventually_lt ε₀ hε₀0)
  -- `gaussDdim a 0 ≥ 0`, for the amplitude nonnegativities.
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  refine ⟨(15 / 2 * (n : ℝ) * L + C_R)
            + ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
                * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
                  + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
                  + ((n : ℝ) * C_W * C_P)
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀))),
          (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n),
          max N1 N2, ?_, ?_, ?_⟩
  · -- `0 ≤ D0`.
    have hbrkt : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
          + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
          + ((n : ℝ) * C_W * C_P)
            * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) := by
      have ht2 : (0 : ℝ) ≤ ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀) :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
      have ht3 : (0 : ℝ) ≤ ((n : ℝ) * C_W * C_P)
          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC_W) hC_P)
          (mul_nonneg (by positivity) hτ₀0.le)
      have ht1 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2) := by positivity
      linarith
    have hC₀ : (0 : ℝ) ≤ 15 / 2 * (n : ℝ) * L + C_R :=
      add_nonneg (mul_nonneg (by positivity) hL) hC_Rnn
    have hC₁ : (0 : ℝ) ≤ (Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
          * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
            + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
            + ((n : ℝ) * C_W * C_P)
              * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₁) (mul_nonneg hC_L hga)) hbrkt
    linarith
  · -- `0 ≤ D1`.
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₂) hC_L) hga
  · -- the eventual per-`m` bound.
    intro m hm
    have hm1 : N1 ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : N2 ≤ m := le_trans (le_max_right _ _) hm
    obtain ⟨hsu, hsa, hsτ⟩ := hN1 m hm1
    have hεm_le : epsSeq m ≤ ε₀ := (hN2 m hm2).le
    refine ⟨⟨hsu, hsa, hsτ⟩, ?_⟩
    -- master → `epsSeq m` window restriction.
    have hsub : ∀ s, s ∈ Set.Ioo (u - epsSeq m) u → s ∈ Set.Ioo (u - ε₀) u :=
      fun s hs => ⟨by linarith [hs.1], hs.2⟩
    -- `sTerm0·F` integrability on the `epsSeq m` window, via the add-and-subtract identity.
    have hInt0 : ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z 0) volume := by
      intro s hs
      have heq : (fun z : Point n => sTerm0 Y P Q A0 (u - s) z * F s z 0)
          = fun z => (((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
                * (A0 (u - s) z * F s z 0)
              + (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
                  * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                      - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
                  * (A0 (u - s) z * F s z 0))
            + gaussDdim (u - s) z
                * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
                    - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
                    - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
                * (A0 (u - s) z * F s z 0) := by
        funext z; simp only [sTerm0]; ring
      rw [heq]
      exact ((hIntT3 s (hsub s hs)).add (hIntT1 s (hsub s hs))).add (hIntT2 s (hsub s hs))
    -- fire the explicit-`C_R` composite at `ε := epsSeq m`, `C_R` FIXED.
    exact witness_sliver2_final D2H F Y P Q A0 A1 A2 i L C_R M₁ M₂ C_L T a τ₀ C_W C_P
      hL hC_Rnn hM₁ hM₂ hC_L hC_W hC_P u (epsSeq m) ha hau huT (epsSeq_pos m).le hsu hsa hsτ
      hco hYdisp hJ3 hA1bdd hA2bdd hFdom
      (fun s hs => hqLip s (hsub s hs)) (fun s hs => hRemM s (hsub s hs)) hNormalForm
      hInt0 (fun s hs => hInt1 s (hsub s hs)) (fun s hs => hInt2 s (hsub s hs))

/-! ###############################################################################
    ### U2 — the closure: the per-coordinate eventual bound → the ∀`m` `hbnd` slot.
    ############################################################################### -/

/-- **★★ U2 — `hbnd_witness_final`.**  THE `witness → hbnd` CHAIN CLOSED.  Given, for a coordinate
    family, the `m`-uniform eventual per-coordinate `√ε` sliver bound with a COMMON threshold `M₀`
    (exactly the shape `witness_sliver2_eventual` delivers — the `M₀ = max N1 N2` there depends only
    on `u, a, τ₀, ε₀`, NOT on `i`), the finite-max extension `hbnd_from_eventual` (inside
    `hbnd_witness_supplied`) closes the ∀`m` form: an `ε`-free `D0'` with
      `∀ i m, |slivInt i m| ≤ D0' i·(2√(epsSeq m)) + D1 i·epsSeq m`,
    the EXACT per-`i`,`m` `hbnd` consumed by `SliverSumPlumbing.sliver_sum_bound`.  Pure forward to
    `hbnd_witness_supplied` — the eventual carry is the genuine, non-vacuous U1 output.  NOT
    `a₁ = R/6`. -/
theorem hbnd_witness_final (slivInt : Fin n → ℕ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i) (M₀nat : ℕ)
    (heventual : ∀ (i : Fin n) (m : ℕ), M₀nat ≤ m →
        |slivInt i m| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ D0' : Fin n → ℝ, (∀ i, 0 ≤ D0' i) ∧
      ∀ (i : Fin n) (m : ℕ),
        |slivInt i m| ≤ D0' i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m :=
  hbnd_witness_supplied slivInt D0 D1 hD0 hD1 M₀nat heventual

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.witness_sliver2_eventual
#print axioms QIQTH.HeatResidualBound.hbnd_witness_final
