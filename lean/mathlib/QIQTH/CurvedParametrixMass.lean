/-
  CurvedParametrixMass — J4-510: the CURVED-parametrix heat-mass → 1 (the approximate-identity
  sub-lemma attacking the J4-509 flat-only obstruction).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the J4-509 flat-only obstruction).  The a₁ mainline `A1R6FromLabelled.a1_R6_from_labelled`
  is CONDITIONAL, and J4-509 exhibited a demonstrated FLAT-ONLY obstruction: two antecedent
  hypotheses are jointly satisfiable only by metrics with `Ric(0)=0`, so the advertised `t`-coefficient
  `R/6` is identically `0` in every instance.  The obstructing pair is
    • `hframeK : ∀ q∈K, g q = δ`  — the metric is FLAT on ALL of the witness gate `K` (⟹ `Ric(0)=0`);
    • `hmassone : Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)` — the gated witness carries
      unit heat mass as `τ ↓ 0`.

  ⚠ THE FIX ATTACKED HERE (this file, J4-510).  The mathematically-correct fact is that the CURVED
  van-Vleck parametrix has heat mass → 1 as `τ ↓ 0` by the GAUSSIAN APPROXIMATE-IDENTITY property,
  INDEPENDENT of whether `g = δ`.  With the parametrix ansatz
      `heatParametrix N Θ u τ w = gaussDdim τ w · (Θ w)^{−1/2} · Σ_{k≤N} u_k(w) τ^k`
  the mass over a FIXED neighbourhood `Ω` of `0` (density `1` at `0`, NOT the `δ`-agreement set)
      `∫_{w∈Ω} heatParametrix N Θ u τ w  →  Θ(0)^{−1/2}·u_0(0) = 1`   as `τ ↓ 0`,
  because the Gaussian concentrates at `0` and the amplitude `A τ w = (Θ w)^{−1/2}·Σ u_k(w)τ^k`
  approaches its value `A(0,0) = 1` at the origin — with `Θ(0)=1` and `u_0(0)=1` but `Θ ≢ 1`
  (a genuinely CURVED amplitude).  So `hmassone`'s CONTENT can be proved for a curved parametrix,
  WITHOUT `hframeK`.

  WHAT LANDS.
    • `parametrixAmp` — the amplitude factor `A τ w = (Θ w)^{−1/2}·Σ_{k≤N} u_k(w) τ^k`.
    • `heatParametrix_eq_gauss_mul_amp` — `heatParametrix = gaussDdim · parametrixAmp` (`ring`).
    • `parametrixAmp_zero_zero` — `A(0,0) = 1` from `Θ(0)=1 ∧ u_0(0)=1` (curvature-agnostic).
    • `parametrixAmp_continuousAt_zero` — joint continuity of `A` at `(0,0)`.
    • `heatParametrix_setMass_tendsto_one` — ★ the CURVED-parametrix mass → 1 over a fixed
        neighbourhood `Ω`, reusing the banked moving approximate identity
        `ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving`.  The `L = 1` (`hlocal`) part
        is PROVED from joint continuity + the diagonal values, NOT assumed.
    • `curvedTheta` / `curvedTheta_zero` / `curvedTheta_ne_one`
        / `heatParametrix_setMass_tendsto_one_curved_certificate`
        — the SATISFIABILITY GATE: a concrete GENUINELY-CURVED `Θ = 1 + ‖w‖²` (`Θ(0)=1`, `Θ ≢ 1`)
        for which the mass → 1 holds.  Certifies the lemma is NOT secretly flat-only.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`.  This is ONE brick attacking the mass side of the J4-509
  obstruction.  It proves the CONTENT that lets `hmassone` hold for a curved witness.  It does NOT by
  itself make `a1_R6_from_labelled` curved-satisfiable: the exact `hmassone` is stated on the
  CHART-IMAGE gated witness `∫_z Wit(τ,0,z) dz` (Gaussian in `w = Vmap z 0`, hard gate `z∈K`,
  `radialCutoff`), so wiring this lemma into it needs the Layer-A on-gate factorization
  `Wit τ 0 z = gaussDdim τ (Vmap z 0)·amp` and the Layer-B change of variables `w = Vmap z 0`
  (with Jacobian `J(0)=1`; separate, later bricks); and `hframeK` is ALSO consumed elsewhere (the
  `hDaLimLU_from_labelled` Da-limit residual gauge), which must be independently weakened.  No
  `sorry`, no new axioms, no `:= True`, no conclusion-in-disguise hypothesis (`hmeas`/`hbound` are
  genuine a.e./eventual carries).
-/
import Mathlib
import QIQTH.ChartImageApproxIdentity
import QIQTH.HeatParametrixAnsatz

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open scoped Topology BigOperators

namespace QIQTH.CurvedParametrixMass

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The amplitude factor of the parametrix. -/

/-- **The parametrix AMPLITUDE** `A τ w = (Θ w)^{−1/2} · Σ_{k≤N} u_k(w) τ^k` — the non-Gaussian
    factor of `heatParametrix N Θ u τ w = gaussDdim τ w · A τ w`. -/
noncomputable def parametrixAmp (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (τ : ℝ) (w : Point n) : ℝ :=
  (Θ w) ^ (-(1 : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), u k w * τ ^ k

/-- The parametrix factors as `gaussDdim · parametrixAmp` (pure `ring` regrouping of `heatParametrix`). -/
theorem heatParametrix_eq_gauss_mul_amp (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (τ : ℝ) (w : Point n) :
    heatParametrix N Θ u τ w = gaussDdim τ w * parametrixAmp N Θ u τ w := by
  unfold heatParametrix parametrixAmp
  ring

/-- **`A(0,0) = 1`** from the diagonal DeWitt normalization `Θ(0)=1`, `u_0(0)=1`.  Curvature-agnostic:
    `(Θ 0)^{−1/2} = 1^{−1/2} = 1`, and at `τ=0` the sum collapses to its `k=0` term `u_0(0)·0^0 = 1`. -/
theorem parametrixAmp_zero_zero (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hΘ0 : Θ (0 : Point n) = 1) (hu0 : u 0 (0 : Point n) = 1) :
    parametrixAmp N Θ u 0 (0 : Point n) = 1 := by
  unfold parametrixAmp
  rw [hΘ0, Real.one_rpow, one_mul, Finset.sum_eq_single 0]
  · simp [hu0]
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

/-- **Joint continuity of the amplitude at `(0,0)`.**  `A` is continuous at the space-time origin:
    `(Θ ·)^{−1/2}` is continuous at `w=0` (base `Θ(0)=1 ≠ 0`, so the negative-exponent `rpow` is
    continuous), and each term `u_k(·)·(·)^k` is jointly continuous, so their finite sum is. -/
theorem parametrixAmp_continuousAt_zero (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hΘ0 : Θ (0 : Point n) = 1) (hΘcont : ContinuousAt Θ (0 : Point n))
    (hucont : ∀ k, ContinuousAt (u k) (0 : Point n)) :
    ContinuousAt (fun p : ℝ × Point n => parametrixAmp N Θ u p.1 p.2) (0, 0) := by
  simp only [parametrixAmp]
  -- the `Θ^{−1/2}` factor
  have hbase : ContinuousAt (fun p : ℝ × Point n => Θ p.2) ((0 : ℝ), (0 : Point n)) :=
    ContinuousAt.comp_of_eq hΘcont continuousAt_snd rfl
  have hrpow : ContinuousAt (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) (Θ (0 : Point n)) := by
    apply Real.continuousAt_rpow_const
    left; rw [hΘ0]; norm_num
  have hΘfac : ContinuousAt (fun p : ℝ × Point n => (Θ p.2) ^ (-(1 : ℝ) / 2))
      ((0 : ℝ), (0 : Point n)) := ContinuousAt.comp_of_eq hrpow hbase rfl
  -- the DeWitt polynomial factor
  have hpoly : ContinuousAt
      (fun p : ℝ × Point n => ∑ k ∈ Finset.range (N + 1), u k p.2 * p.1 ^ k)
      ((0 : ℝ), (0 : Point n)) := by
    apply tendsto_finset_sum
    intro k _
    exact (ContinuousAt.comp_of_eq (hucont k) continuousAt_snd rfl).mul (continuousAt_fst.pow k)
  exact hΘfac.mul hpoly

/-! ### The curved-parametrix mass → 1 over a fixed neighbourhood. -/

/-- **★★ J4-510 — THE CURVED-PARAMETRIX MASS → 1 (approximate-identity sub-lemma).**  Let `Ω` be a
    measurable neighbourhood of the origin, and let the amplitude satisfy the diagonal DeWitt
    normalization `Θ(0)=1`, `u_0(0)=1` with `Θ`, `u_k` continuous at `0`, plus the genuine regularity
    carries `hmeas` (eventual a.e.-measurability of `A τ` on `Ω`) and `hbound` (eventual UNIFORM
    a.e.-bound on `Ω`).  Then the CURVED heat parametrix carries unit heat mass over `Ω` as `τ ↓ 0`:
        `∫_{w∈Ω} heatParametrix N Θ u τ w  →  1`   in `𝓝[>] (0 : ℝ)`.
    ROUTE: rewrite `heatParametrix = gaussDdim · parametrixAmp` and apply the banked MOVING approximate
    identity `ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving` with `L := 1`; the
    `hlocal` (joint approach to `1`) is PROVED — not assumed — from `parametrixAmp_continuousAt_zero`
    and `parametrixAmp_zero_zero`.  ⚠ Independent of flatness: `Θ ≢ 1` is allowed (see the certificate).
    NOT `a₁ = R/6`. -/
theorem heatParametrix_setMass_tendsto_one (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {Ω : Set (Point n)} (hΩmeas : MeasurableSet Ω) (hΩnhds : Ω ∈ 𝓝 (0 : Point n))
    (hΘ0 : Θ (0 : Point n) = 1) (hu0 : u 0 (0 : Point n) = 1)
    (hΘcont : ContinuousAt Θ (0 : Point n)) (hucont : ∀ k, ContinuousAt (u k) (0 : Point n))
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (parametrixAmp N Θ u τ) (volume.restrict Ω))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ w ∂(volume.restrict Ω), ‖parametrixAmp N Θ u τ w‖ ≤ C) :
    Tendsto (fun τ => ∫ w in Ω, heatParametrix N Θ u τ w) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  -- rewrite the integrand into `gaussDdim · amplitude`
  have hrw : (fun τ => ∫ w in Ω, heatParametrix N Θ u τ w)
      = fun τ => ∫ w in Ω, gaussDdim τ w * parametrixAmp N Θ u τ w := by
    funext τ
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun w => heatParametrix_eq_gauss_mul_amp N Θ u τ w))
  rw [hrw]
  -- joint continuity of the amplitude, valued `1` at the origin
  have hcont := parametrixAmp_continuousAt_zero N Θ u hΘ0 hΘcont hucont
  -- derive `hlocal` (joint approach to `L = 1`) from continuity
  have hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict Ω), ‖w‖ < r → ‖parametrixAmp N Θ u τ w - 1‖ < ε := by
    intro ε εpos
    -- eventual `dist (A τ w) (A 0 0) < ε` near `(0,0)`, from joint continuity
    have hkey : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : Point n)),
        dist (parametrixAmp N Θ u p.1 p.2) (parametrixAmp N Θ u 0 (0 : Point n)) < ε :=
      Metric.tendsto_nhds.mp hcont.tendsto ε εpos
    -- split the product neighbourhood into a `τ`-part and a `w`-ball
    rw [nhds_prod_eq, Filter.eventually_prod_iff] at hkey
    obtain ⟨pa, hpa, pb, hpb, hP⟩ := hkey
    obtain ⟨r, rpos, hr⟩ := Metric.eventually_nhds_iff.1 hpb
    refine ⟨r, rpos, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hpa] with τ hτ
    refine Filter.Eventually.of_forall (fun w hw => ?_)
    have hwpb : pb w := hr (by simpa [dist_zero_right] using hw)
    have hd := hP hτ hwpb
    rw [Real.dist_eq, parametrixAmp_zero_zero N Θ u hΘ0 hu0] at hd
    rw [Real.norm_eq_abs]; exact hd
  -- apply the banked moving approximate identity at `L = 1`
  exact ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving hΩmeas hΩnhds
    hmeas hbound hlocal

/-! ### Satisfiability gate — a CONCRETE genuinely-curved amplitude. -/

/-- **A concrete CURVED van-Vleck-shaped profile** `Θ_curved w = 1 + ‖w‖²` (`= 1 + Σ_i (w i)²`).
    Smooth, `≥ 1` everywhere (so `(Θ_curved)^{−1/2} ≤ 1` is globally bounded), `Θ_curved(0)=1`, but
    `Θ_curved ≢ 1`.  Certifies that the curved mass → 1 is NOT secretly flat-only. -/
noncomputable def curvedTheta (w : Point n) : ℝ := 1 + ∑ i, (w i) ^ 2

theorem curvedTheta_zero : curvedTheta (0 : Point n) = 1 := by
  simp [curvedTheta]

theorem curvedTheta_ge_one (w : Point n) : (1 : ℝ) ≤ curvedTheta w := by
  unfold curvedTheta
  have : (0 : ℝ) ≤ ∑ i, (w i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

theorem curvedTheta_continuous : Continuous (curvedTheta : Point n → ℝ) := by
  unfold curvedTheta
  exact continuous_const.add (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2))

/-- **`Θ_curved ≢ 1` — the amplitude is GENUINELY CURVED (`n ≥ 1`).**  At the all-ones point we have
    `Θ_curved (fun _ => 1) = 1 + n ≠ 1`, so `curvedTheta` is not the flat `Θ ≡ 1`. -/
theorem curvedTheta_ne_one (hn : 1 ≤ n) : curvedTheta (fun _ : Fin n => (1 : ℝ)) ≠ 1 := by
  have hval : curvedTheta (fun _ : Fin n => (1 : ℝ)) = 1 + (n : ℝ) := by
    simp [curvedTheta, Finset.card_univ]
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [hval]; intro h; linarith

/-- The leading (constant `1`) DeWitt profile used in the certificate: `u_0 ≡ 1`, `u_k ≡ 0` (`k ≥ 1`). -/
noncomputable def flatU : ℕ → Point n → ℝ := fun k _ => if k = 0 then (1 : ℝ) else 0

theorem flatU_zero : flatU 0 (0 : Point n) = 1 := by simp [flatU]

theorem flatU_continuousAt (k : ℕ) : ContinuousAt (flatU k) (0 : Point n) := by
  unfold flatU; exact continuousAt_const

/-- The certificate amplitude collapses to `A τ w = (curvedTheta w)^{−1/2}` for every `τ`
    (the DeWitt sum is `1`, since only the `k=0` term survives and `τ^0 = 1`). -/
theorem parametrixAmp_curved_eq (N : ℕ) (τ : ℝ) (w : Point n) :
    parametrixAmp N curvedTheta flatU τ w = (curvedTheta w) ^ (-(1 : ℝ) / 2) := by
  unfold parametrixAmp
  rw [Finset.sum_eq_single 0]
  · simp [flatU]
  · intro k _ hk
    simp [flatU, hk]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

theorem parametrixAmp_curved_abs_le_one (N : ℕ) (τ : ℝ) (w : Point n) :
    ‖parametrixAmp N curvedTheta flatU τ w‖ ≤ 1 := by
  rw [parametrixAmp_curved_eq, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < curvedTheta w := lt_of_lt_of_le one_pos (curvedTheta_ge_one w)
  rw [abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
  calc (curvedTheta w) ^ (-(1 : ℝ) / 2)
      ≤ (1 : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos one_pos (curvedTheta_ge_one w) (by norm_num)
    _ = 1 := Real.one_rpow _

/-- **★ SATISFIABILITY GATE — CURVED mass → 1.**  The curved-parametrix mass → 1 holds for the
    GENUINELY-CURVED profile `Θ = curvedTheta` (`Θ(0)=1`, `Θ ≢ 1` by `curvedTheta_ne_one`),
    `u = flatU`, over `Ω = univ`.  This certifies `heatParametrix_setMass_tendsto_one` is NOT secretly
    flat-only: a curved amplitude carries unit heat mass.  NOT `a₁ = R/6`. -/
theorem heatParametrix_setMass_tendsto_one_curved_certificate (N : ℕ) :
    Tendsto (fun τ => ∫ w : Point n, heatParametrix N curvedTheta flatU τ w)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (parametrixAmp N curvedTheta flatU τ)
        (volume.restrict (Set.univ : Set (Point n))) := by
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hc : Continuous (fun w : Point n => (curvedTheta w) ^ (-(1 : ℝ) / 2)) :=
      curvedTheta_continuous.rpow_const
        (fun w => Or.inl (lt_of_lt_of_le one_pos (curvedTheta_ge_one w)).ne')
    have heq : parametrixAmp N (curvedTheta (n := n)) (flatU (n := n)) τ
        = fun w : Point n => (curvedTheta w) ^ (-(1 : ℝ) / 2) :=
      funext (fun w => parametrixAmp_curved_eq (n := n) N τ w)
    rw [heq]
    exact hc.aestronglyMeasurable.restrict
  have h := heatParametrix_setMass_tendsto_one (n := n) N curvedTheta flatU
    (Ω := (Set.univ : Set (Point n))) MeasurableSet.univ Filter.univ_mem
    curvedTheta_zero flatU_zero curvedTheta_continuous.continuousAt flatU_continuousAt
    hmeas
    ⟨1, Filter.Eventually.of_forall (fun τ =>
      Filter.Eventually.of_forall (fun w => parametrixAmp_curved_abs_le_one N τ w))⟩
  simpa only [setIntegral_univ] using h

end QIQTH.CurvedParametrixMass

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.CurvedParametrixMass

#print axioms heatParametrix_eq_gauss_mul_amp
#print axioms parametrixAmp_zero_zero
#print axioms parametrixAmp_continuousAt_zero
#print axioms heatParametrix_setMass_tendsto_one
#print axioms curvedTheta_ne_one
#print axioms heatParametrix_setMass_tendsto_one_curved_certificate

end AxiomChecks
