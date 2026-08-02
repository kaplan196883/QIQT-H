/-
  GatedWitnessMeas — J4-109: the integrability/measurability wiring for the `N = 1` gated
  van-Vleck witness `hInt`, plus the `hEmeas`-conditional concrete hand-off.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE ∀τ MISMATCH (the decisive architectural fact).

  The `N = 1` gated witness residual `E := heatOp g gi H_G` satisfies (LANDED, J4-108
  `gatedWitnessN1_hEboundW_le_vanVleck_final`) only the `(0,t]`-RESTRICTED α=0 bound
      `∀ τ p q, 0 < τ → τ ≤ t → |E τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q`,
  because the genuine α=1 diagonal tail (`τ·R₀[u']`) makes the FULL-∀τ α=0 bound FALSE (a linear-`τ`
  tail cannot be dominated by a τ-free constant × `baseKernelW 2 0`).

  But the producer `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas` demands a FULL-∀τ α=0
  bound, and the restricted capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted` consumes the
  FULL `hInt : IterConvIntegrableW E 2 0 C` (∀ outer time).

  ── THE TIME-CAP RESOLUTION (Sol-consult verdict, cheapest sound route). ─────────────────────────
  `IterConvIntegrableW E 2 0 Cmodel` bundles, at every OUTER time `t`, five conjuncts: (1)(2)(3) are
  the interval/Lebesgue integrability of the ACTUAL iterated convolutions (`C`-FREE), (4)(5) are the
  pure-Gaussian MODEL facts (hold for any `Cmodel`, independent of `E`).  For a fixed outer time `t`,
  ALL times at which `E`/`iterE E k` are evaluated inside conjuncts (1)(2)(3) lie in `[0,t]` (via the
  convolution simplex + the vanishing `hEzero` at nonpositive time).  So we may replace `E` by its
  TIME-CAP `timeCap t E := if τ ≤ t then E τ else 0`, which HAS a full-∀τ α=0 bound (constant
  `C·(1+t)`; for `τ > t` it is `0 ≤ RHS`), feed the EXISTING full producer to it, and transfer the
  actual-`E` conjuncts back at outer time `t` via `iterE_timeCap_eq` (causal equality below the cap).
  The output has the EXISTING full `IterConvIntegrableW` type — NO downstream re-plumb of the
  restricted Levi/capstone chain.

  ⚠ HONEST SCOPE.  `iterConvIntegrableW_of_locally_bound_baseMeas` reduces `hInt` to `hEzero`,
  `hEmeas`, and the `(0,T]`-LOCAL bound family (each LANDED for the concrete van-Vleck witness).  It
  does NOT manufacture a global pointwise `|iterE E k t| ≤ Cmodel^k·iterKernelW …` with a
  time-independent constant (that is FALSE under the mixed tail — the restricted downstream pointwise
  bounds keep the `C·(1+T)` constant).  The SINGLE remaining input for a fully-discharged concrete
  `hInt` is `hEmeas` (M1, the parameterized-deriv measurability of `heatOp g gi H_G` — the C¹-chart /
  gate-frontier regularity wall, censused below).  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no
  vacuous hypotheses.
-/
import Mathlib
import QIQTH.IterEMeasurable
import QIQTH.CoeffU1Fix
import QIQTH.CoeffBoundsN1

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.PullbackMetric QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. The time-cap of a residual kernel and its elementary algebra. -/

/-- **The time-cap of a residual kernel.**  `timeCap T E τ p q = E τ p q` for `τ ≤ T`, and `0` for
    `τ > T`.  Used to give a FULL-∀τ α=0 bound (the tail `τ > T` is `0`) to a kernel that only obeys a
    `(0,T]`-restricted bound. -/
noncomputable def timeCap (T : ℝ) (E : ℝ → Point n → Point n → ℝ) :
    ℝ → Point n → Point n → ℝ :=
  fun τ p q => if τ ≤ T then E τ p q else 0

/-- Below the cap, `timeCap` is the original kernel. -/
theorem timeCap_apply_of_le (T : ℝ) (E : ℝ → Point n → Point n → ℝ) {τ : ℝ} (p q : Point n)
    (h : τ ≤ T) : timeCap T E τ p q = E τ p q := by
  simp only [timeCap, if_pos h]

/-- Above the cap, `timeCap` vanishes. -/
theorem timeCap_apply_of_gt (T : ℝ) (E : ℝ → Point n → Point n → ℝ) {τ : ℝ} (p q : Point n)
    (h : T < τ) : timeCap T E τ p q = 0 := by
  simp only [timeCap, if_neg (not_le.mpr h)]

/-- The time-cap inherits vanishing at nonpositive time (no constraint on `T`: below the cap it is
    `E` which vanishes; above the cap it is `0`). -/
theorem timeCap_zero (T : ℝ) (E : ℝ → Point n → Point n → ℝ)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, timeCap T E τ p q = 0 := by
  intro τ hτ p q
  simp only [timeCap]
  split_ifs with h
  · exact hEzero τ hτ p q
  · rfl

/-- The joint strong measurability of the time-cap, from that of the base kernel: a measurable
    `ite` over the (measurable) sub-level set `{w | w.1 ≤ T}`. -/
theorem stronglyMeasurable_timeCap (T : ℝ) (E : ℝ → Point n → Point n → ℝ)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n => timeCap T E w.1 w.2.1 w.2.2) := by
  classical
  have hset : MeasurableSet {w : ℝ × Point n × Point n | w.1 ≤ T} :=
    measurableSet_le measurable_fst measurable_const
  have hmeasE : Measurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2) :=
    hEmeas.measurable
  have hrw : (fun w : ℝ × Point n × Point n => timeCap T E w.1 w.2.1 w.2.2)
      = (fun w : ℝ × Point n × Point n => if w.1 ≤ T then E w.1 w.2.1 w.2.2 else 0) := by
    funext w; simp only [timeCap]
  rw [hrw]
  exact (Measurable.ite hset hmeasE measurable_const).stronglyMeasurable

/-! ### 2. The vanishing of iterated residual convolutions at nonpositive time (standalone). -/

/-- **The iterated residual vanishes at nonpositive time.**  Standalone version of the local `have`
    in `iterConvIntegrableW_of_bound_continuous`.  From `hEzero`, for every `k ≥ 1` and `s ≤ 0`,
    `iterE E k s z y = 0` (the base is `hEzero`; the step integrates a product with a vanishing right
    factor). -/
theorem iterE_nonpos (E : ℝ → Point n → Point n → ℝ)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ), s ≤ 0 → ∀ (z y : Point n), iterE E k s z y = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro s hs z y; rw [iterE_one]; exact hEzero s hs z y
  | succ m hm ih =>
      intro s hs z y
      rw [iterE_succ E hm, heatConvK_apply]
      simp only [heatConv]
      refine (intervalIntegral.integral_congr (fun s' hs' => ?_)).trans intervalIntegral.integral_zero
      have hmem : s' ∈ Set.Icc s 0 := by rwa [Set.uIcc_of_ge hs] at hs'
      have hzero : (fun w => E (s - s') z w * iterE E m s' w y) = fun _ => (0 : ℝ) := by
        funext w; rw [ih s' hmem.2 w y, mul_zero]
      show (∫ w, E (s - s') z w * iterE E m s' w y) = 0
      rw [hzero, integral_zero]

/-! ### 3. Causal equality of iterated convolutions below the cap. -/

/-- **★ CAUSAL EQUALITY BELOW THE CAP.**  For every `s ≤ T`, the iterated convolution of the
    time-capped kernel agrees with that of the original: `iterE (timeCap T E) k s x y = iterE E k s
    x y`.  Induction on `k`: the convolution at outer time `s ≤ T` integrates over `u ∈ [0,s]`, where
    both inner times `s−u` and `u` are `≤ T`, so the cap is inactive and the IH applies. -/
theorem iterE_timeCap_eq (E : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ), s ≤ T → ∀ (x y : Point n),
      iterE (timeCap T E) k s x y = iterE E k s x y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro s hsT x y
      simp only [iterE_one]
      exact timeCap_apply_of_le T E x y hsT
  | succ m hm ih =>
      intro s hsT x y
      by_cases hs0 : s ≤ 0
      · rw [iterE_nonpos (timeCap T E) (timeCap_zero T E hEzero) (m + 1) (by omega) s hs0 x y,
            iterE_nonpos E hEzero (m + 1) (by omega) s hs0 x y]
      · push_neg at hs0
        rw [iterE_succ (timeCap T E) hm, iterE_succ E hm, heatConvK_apply, heatConvK_apply]
        simp only [heatConv]
        refine intervalIntegral.integral_congr (fun u hu => ?_)
        rw [Set.uIcc_of_le hs0.le] at hu
        obtain ⟨hu0, hus⟩ := hu
        have hbody : (fun z => timeCap T E (s - u) x z * iterE (timeCap T E) m u z y)
            = (fun z => E (s - u) x z * iterE E m u z y) := by
          funext z
          rw [timeCap_apply_of_le T E x z (by linarith), ih u (by linarith) z y]
        show (∫ z, timeCap T E (s - u) x z * iterE (timeCap T E) m u z y)
            = ∫ z, E (s - u) x z * iterE E m u z y
        rw [hbody]

/-! ### 4. ★ THE LOCALLY-BOUNDED PRODUCER — full `IterConvIntegrableW` from a `(0,T]`-local bound. -/

/-- **★★ J4-109 — THE TIME-CAP PRODUCER.**  Given `E`'s vanishing at nonpositive time (`hEzero`),
    the base joint strong measurability (`hEmeas`), and the `(0,T]`-LOCAL α=0 bound family (for every
    `T > 0` a constant `CT ≥ 0` dominating `|E τ p q|` on `(0,T]`), the FULL per-step integrability
    family `IterConvIntegrableW E 2 0 Cmodel` holds — for ANY `Cmodel` (the model conjuncts (4)(5) are
    pure Gaussian facts).

    ROUTE: at each outer time `t`, cap `E` at `t`; the cap has a FULL-∀τ α=0 bound with constant `CT`
    (`|timeCap| = 0 ≤ RHS` above the cap), so `iterConvIntegrableW_of_bound_baseMeas` yields the five
    conjuncts for the cap.  The actual-`E` conjuncts (1)(2)(3) transfer at outer time `t` via
    `iterE_timeCap_eq` (all inner times `≤ t`); the model conjuncts (4)(5) are supplied by
    `iterConvIntegrableW_model` at `Cmodel`.  Output has the EXISTING `IterConvIntegrableW` type. -/
theorem iterConvIntegrableW_of_locally_bound_baseMeas
    (E : ℝ → Point n → Point n → ℝ) (Cmodel : ℝ)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2))
    (hlocal : ∀ T : ℝ, 0 < T → ∃ CT : ℝ, 0 ≤ CT ∧
        ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    IterConvIntegrableW E (2 : ℝ) (0 : ℝ) Cmodel := by
  intro k hk t ht x y
  obtain ⟨Ct, hCt0, hCt⟩ := hlocal t ht
  -- The time-capped kernel has a FULL-∀τ α=0 bound with constant `Ct`.
  have hbnd : ∀ τ p q, 0 < τ → |timeCap t E τ p q| ≤ Ct * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ
    by_cases hle : τ ≤ t
    · rw [timeCap_apply_of_le t E p q hle]; exact hCt τ p q hτ hle
    · rw [timeCap_apply_of_gt t E p q (not_le.mp hle), abs_zero]
      have hb : 0 ≤ baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
        rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _
      exact mul_nonneg hCt0 hb
  have hzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, timeCap t E τ p q = 0 :=
    timeCap_zero t E hEzero
  have hmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => timeCap t E w.1 w.2.1 w.2.2) :=
    stronglyMeasurable_timeCap t E hEmeas
  have hIntCap : IterConvIntegrableW (timeCap t E) (2 : ℝ) (0 : ℝ) Ct :=
    iterConvIntegrableW_of_bound_baseMeas (timeCap t E) Ct hbnd hzero hmeas
  obtain ⟨c1, c2, c3, _, _⟩ := hIntCap k hk t ht x y
  obtain ⟨hmod4, hmod5⟩ := iterConvIntegrableW_model (2 : ℝ) Cmodel (by norm_num) k hk t ht x y
  -- Pointwise (in `z`) equality of the capped and original integrands, ALL `s`.
  have hprod : ∀ s : ℝ,
      (fun z => timeCap t E (t - s) x z * iterE (timeCap t E) k s z y)
        = (fun z => E (t - s) x z * iterE E k s z y) := by
    intro s
    funext z
    by_cases hs0 : s ≤ 0
    · rw [iterE_nonpos (timeCap t E) hzero k hk s hs0 z y,
          iterE_nonpos E hEzero k hk s hs0 z y, mul_zero, mul_zero]
    · push_neg at hs0
      by_cases hst : s ≤ t
      · rw [timeCap_apply_of_le t E x z (by linarith), iterE_timeCap_eq E t hEzero k hk s hst z y]
      · push_neg at hst
        have h1 : E (t - s) x z = 0 := hEzero (t - s) (by linarith) x z
        have h2 : timeCap t E (t - s) x z = 0 := by
          rw [timeCap_apply_of_le t E x z (by linarith)]; exact hEzero (t - s) (by linarith) x z
        rw [h1, h2, zero_mul, zero_mul]
  -- Conjunct (1): transfer the norm-integrand.
  have c1' : IntervalIntegrable
      (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t := by
    refine c1.congr (fun s _ => ?_)
    dsimp only
    have hII : (∫ z, timeCap t E (t - s) x z * iterE (timeCap t E) k s z y)
        = ∫ z, E (t - s) x z * iterE E k s z y :=
      integral_congr_ae (Filter.Eventually.of_forall (fun z => congrFun (hprod s) z))
    rw [hII]
  -- Conjunct (2): transfer the abs-product integrand.
  have c2' : IntervalIntegrable
      (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t := by
    refine c2.congr (fun s _ => ?_)
    dsimp only
    have hII : (∫ z, |timeCap t E (t - s) x z| * |iterE (timeCap t E) k s z y|)
        = ∫ z, |E (t - s) x z| * |iterE E k s z y| := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show |timeCap t E (t - s) x z| * |iterE (timeCap t E) k s z y|
          = |E (t - s) x z| * |iterE E k s z y|
      rw [← abs_mul, ← abs_mul, congrFun (hprod s) z]
    rw [hII]
  -- Conjunct (3): transfer per-`s`.
  have c3' : ∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|) := by
    intro s
    refine (c3 s).congr (Filter.Eventually.of_forall (fun z => ?_))
    show |timeCap t E (t - s) x z| * |iterE (timeCap t E) k s z y|
        = |E (t - s) x z| * |iterE E k s z y|
    rw [← abs_mul, ← abs_mul, congrFun (hprod s) z]
  exact ⟨c1', c2', c3', hmod4, hmod5⟩

/-! ### 5. ★ THE CONCRETE `N = 1` VAN-VLECK HAND-OFF (`hInt` conditional on `hEmeas`). -/

/-- **★★ J4-109 — THE CONCRETE `hInt` FOR THE `N = 1` GATED VAN-VLECK WITNESS, CONDITIONAL ON
    `hEmeas`.**  From the SAME geometric/gauge/all-`k`-smoothness inputs as the LANDED
    `gatedWitnessN1_hEboundW_le_vanVleck_final` (J4-108) plus `1 ≤ n`, there exist the cutoff radii
    `a < b`, a constant `C ≥ 0`, and the gate `S` such that the concrete witness residual `E`
    simultaneously (i) obeys the `(0,t]`-restricted α=0 bound with constant `C·(1+t)`, and (ii) — GIVEN
    the single base joint strong measurability `hEmeas` of `E` (M1) — satisfies the FULL per-step
    integrability family `IterConvIntegrableW E 2 0 Cmodel` for ANY `Cmodel`.

    Route: the bound (i) is `gatedWitnessN1_hEboundW_le_vanVleck_final` verbatim; it supplies the
    `(0,T]`-LOCAL bound family (`CT := C·(1+T)`) for `iterConvIntegrableW_of_locally_bound_baseMeas`.
    The `hEzero` slot is `heatOp_gatedWitnessN1_eq_zero_of_nonpos` (needs `1 ≤ n`).  Thus the ONLY
    remaining input to a fully-discharged concrete `hInt` is `hEmeas` — the parameterized-deriv
    measurability of `heatOp g gi H_G` (M1, censused in the module note).  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hInt_of_hEmeas (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hn : 1 ≤ n) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ∀ (Cmodel : ℝ),
          StronglyMeasurable (fun w : ℝ × Point n × Point n =>
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) w.1 w.2.1 w.2.2) →
          IterConvIntegrableW (heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1
            (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK)))) (2 : ℝ) (0 : ℝ) Cmodel := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound⟩ :=
    gatedWitnessN1_hEboundW_le_vanVleck_final g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C, ha, hab, hC0, S, hbound, ?_⟩
  intro Cmodel hEmeas
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK))) τ p q = 0 :=
    heatOp_gatedWitnessN1_eq_zero_of_nonpos g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK)
  refine iterConvIntegrableW_of_locally_bound_baseMeas _ Cmodel hEzero hEmeas ?_
  intro T hT
  exact ⟨C * (1 + T), mul_nonneg hC0 (by linarith), fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩

/-!
  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## (M3) CAPSTONE-READY CENSUS — inputs of `trueKernel_diagonal_a1_eq_R6_residual_restricted`
  at the `N = 1` van-Vleck witness after J4-109 (M1/M2).

  The restricted capstone (`RestrictedEboundW.trueKernel_diagonal_a1_eq_R6_residual_restricted`),
  instantiated with `H := gatedKernel K S (globalCutoffParametrixWitnessN 1 …)`, `C := C·(1+t)` at
  the fixed capstone time `t`, needs the following inputs.  Status after this file:

    • `hEboundW_le` (★ C4c primitive, `(0,t]`-restricted α=0)  — LANDED.
      `gatedWitnessN1_hEboundW_le_vanVleck_final` (J4-108), exposed here as the first conjunct of
      `gatedWitnessN1_hInt_of_hEmeas`.  Constant `C·(1+t)`, from geometry+gauge+`hw` only.

    • `hInt : IterConvIntegrableW (heatOp g gi H) 2 0 (C·(1+t))`  — LANDED CONDITIONAL ON `hEmeas`.
      `gatedWitnessN1_hInt_of_hEmeas` second conjunct (with `Cmodel := C·(1+t)`).  The ∀τ mismatch is
      resolved by the TIME-CAP producer `iterConvIntegrableW_of_locally_bound_baseMeas` (no
      re-plumb).  Uses `hEzero = heatOp_gatedWitnessN1_eq_zero_of_nonpos` (needs `1 ≤ n`).

    • `hEmeas` (base joint strong measurability of `E = heatOp g gi H_G`)  — ⚠ THE SINGLE REMAINING
      INPUT (M1, NOT discharged here).  `heatOp = ∂_τ − laplaceBeltrami`, and BOTH slots are
      PARAMETERIZED 1D derivatives (`pd f i x = deriv (fun t => f (update x i t)) (x i)`), so
      `measurable_deriv_with_param`/`stronglyMeasurable_deriv_with_param` (which need JOINT
      CONTINUITY of the family) do NOT apply directly — `H_G` is discontinuous at the gate frontier
      and involves the `Classical.choose` chart `uniformInverseChart`.  SOUND ROUTE (Sol-consult):
        (a) gated normal form eliminating `Classical.choose` under the gate (on `S q`,
            `uniformInverseChart … q = ` the known continuous inverse of `uniformFlowExp q`);
        (b) a cutoff zero-neighbourhood / vanishing-2-jet lemma at the moving cutoff frontier
            (needed because `laplaceBeltrami` uses SECOND `p`-derivatives — a value-only null-frontier
            argument is insufficient);
        (c) on the positive-time gated branch, build the measurable derivative fields via
            `stronglyMeasurable_deriv_with_param` on the (continuous) subtype family, and assemble an
            explicit measurable `Eformula` (finite sums/products of `gi`, `christoffel`, and the
            derivative fields), then prove `E = Eformula` pointwise (gated normal form + local
            derivative congruence + `hEzero` on nonpositive time).  This is the expensive brick.

    • `hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t 0`, `1 ≤ N`
      — at `N = 1` the exact match is `gatedWitnessN1_diag_eval_vanVleck` (`heatParametrixFn 1`); the
      capstone consumes `heatParametrixFn N` with `hN : 1 ≤ N`, satisfied at `N = 1` (✓ exact).

    • `hg`,`hg0`,`hgi`,`hΓ`,`hdg0`,`htr`,`hsrc`  — GENUINE RNC / gauge inputs (carried).

    • `hDuhamel`,`hInter`,`hDH`,`hDConv`,`hCH`,`hCConv`  — the Levi/Duhamel analytic + near-diagonal
      regularity carries (the `hDuhamel` wall; orthogonal to this file).

  NET: after J4-109, the restricted-capstone input surface for the `N = 1` witness is reduced to
  `{hEmeas}` (M1) on the measurability/integrability axis, plus the pre-existing `hHdiag` /
  Duhamel-wall / RNC-gauge carries.  NOT unconditional `a₁ = R/6`.
-/

end QIQTH.HeatResidualBound
