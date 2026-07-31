/-
  DoubledFamilyConfine — J4-46: discharging the FULL-doubled-point confinement `hmem` for the CLOSE
  bridge `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`) via a
  JACOBI-FACTOR Grönwall bound into a per-`(a,b)` PRODUCT-BALL confinement set.

  ## Context

  `DoubledFamilyFullSupply.lean` (J4-45) landed the `s`-perturbed confined doubled-family supply
  `sPerturbed_confined_doubled_family_exists`: over a compact `K`, a doubled family `Y q v a b s` with
  closed-`Icc 0 1` `hYode`, exact affine `hIC`, per-`(a,b)` velocity window `σ`, and GEODESIC-factor
  confinement `‖(Y…s τ).1 − (q,0)‖ ≤ C₀‖v+s·a‖`.  The bridge additionally CARRIES `hmem`: confinement
  of the FULL doubled point (INCLUDING the Jacobi factor `(Y…s τ).2`) into a compact convex
  `S q v a b`.  J4-45 firewalled `hmem` because the Jacobi factor needs a Grönwall spread bound.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `sPerturbed_confined_doubled_family_confined_exists` — **the confinement upgrade.**  It extends the
    J4-45 supply with a genuine per-`(a,b)` PRODUCT-BALL confinement set
        `S q v a b = closedBall (q,0) (C₀·ρ) ×ˢ closedBall 0 (‖(0,b)‖·e^{K'_q})`
    (`K'_q` = a uniform operator-norm bound on `fderiv (geodesicField)` over the geodesic ball
    `closedBall (q,0) (C₀·ρ)`, from `geodesicField_fderiv_bddOn_compact`), together with:
      * `hScompact` / `hSconvex` — `S q v a b` is compact and convex (`IsCompact.prod` / `Convex.prod`
        of two closed balls), for EVERY `q,v,a,b`;
      * `hmem : ∀ τ ∈ [0,1], Y q v a b s τ ∈ S q v a b` — DERIVED, not carried:
          - the GEODESIC factor `(Y…s τ).1` lands in `closedBall (q,0) (C₀·ρ)` from the J4-45
            geodesic-factor confinement `‖(Y…s τ).1 − (q,0)‖ ≤ C₀‖v+s·a‖ ≤ C₀·ρ` (velocity window);
          - the JACOBI factor `(Y…s τ).2 = J τ` solves the linearised ODE
            `J' τ = fderiv (geodesicField) (P τ) (J τ)` with seed `J 0 = (0,b)`; Grönwall
            (`norm_le_gronwallBound_of_norm_deriv_right_le`, `ε = 0`) with
            `‖fderiv (geodesicField)(P τ)‖ ≤ K'_q` (valid since `P τ ∈ closedBall (q,0) (C₀·ρ)`) gives
            `‖J τ‖ ≤ ‖(0,b)‖·e^{K'_q·τ} ≤ ‖(0,b)‖·e^{K'_q}`, so `J τ ∈ closedBall 0 (‖(0,b)‖·e^{K'_q})`.
    SATISFIABLE, NOT vacuous: `S q v a b` is a concrete product of closed balls containing the real
    trajectory `(P τ, J τ)`, and `hmem` is PROVED from the Grönwall bound.

  ## HONEST FIREWALL (binding) — what remains CARRIED by the bridge

  This discharges the bridge's `hmem` / `hScompact` / `hSconvex` (the `(S1)` full-point confinement).
  It does NOT construct:

  1. `Vf` / `hVode` / `hV0` — the doubled linearised variation field along `Y…0` with seed
     `((0,a),(0,0))` solving `Vf' = fderiv (doubledField) (Y…0 τ) (Vf τ)`.  This is a further linODE
     one level up, whose base curve is the DOUBLED curve `Y…0 = (P₀, J₀)`; running the narrow-pad
     linODE engine on it needs padded (`[-1/2,3/2]`) CONTINUITY of the Jacobi factor `J₀`, which the
     narrow-pad Jacobi lemma exposes only as `HasDerivAt` on `[0,1]`.  CARRIED.
  2. `hlink` — the first-jet endpoint identification.  CARRIED.
  3. the second-variation block (`Zf`/`Src`, `hZf`, `h0d`, `hKbd`, `hZ`, `h0cap`, `hKbcap`, `hAd`,
     `hXb`, `hSd`).  CARRIED.

  So `(J)` is NOT closed self-contained here: this file discharges the `(S1)` full-point confinement
  (`hmem` + the enclosing compact convex `S`), leaving `Vf`/`hlink`/second-variation as the honest
  residual.  It does NOT smuggle `hid`/`hlink`/`Vf`, does NOT build the covariant `D²/dτ²`, NOT
  Raychaudhuri, NOT `a₁ = R/6`, and the conclusion is NOT among any hypotheses.
-/
import QIQTH.DoubledFamilyFullSupply
import QIQTH.JacobiDoubledFamily
import QIQTH.BoundedGeometry
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyConstruction
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **The `s`-perturbed confined doubled-family supply with FULL-point confinement (`hmem` discharged).**
    Over a compact `K` there is ONE `ρ > 0`, ONE `C₀ ≥ 0`, a per-`(a,b)` positive window `σ q v a b`, a
    doubled family `Y q v a b s`, and a per-`(q,v,a,b)` compact convex PRODUCT-BALL confinement set
    `S q v a b` such that for every `q ∈ K`, `‖v‖ ≤ ρ/2`, seeds `a, b`, and `s ∈ [-(σ q v a b), σ q v a b]`:
      * `Y q v a b s 0 = ((q, v + s • a), (0, b))`;
      * `∀ τ ∈ [0,1], HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ`;
      * `∀ τ ∈ [0,1], ‖(Y q v a b s τ).1 − (q,0)‖ ≤ C₀ * ‖v + s • a‖`;
      * `Y q v a b s 0 − Y q v a b 0 0 = s • ((0,a),(0,0))`;
      * `∀ τ ∈ [0,1], Y q v a b s τ ∈ S q v a b`   -- **the FULL-point confinement (`hmem`)**,
    with `S q v a b` compact and convex.  This is the confinement upgrade of
    `sPerturbed_confined_doubled_family_exists`: the Jacobi factor `(Y…s τ).2` is bounded by
    `‖(0,b)‖·e^{K'_q}` (Grönwall on the linearised ODE), so the full doubled point lands in the product
    of two closed balls.  SATISFIABLE, not vacuous.  `Vf`, `hlink`, and the second-variation block
    remain CARRIED by the bridge (see file firewall). -/
theorem sPerturbed_confined_doubled_family_confined_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∃ σ : Point n → Point n → Point n → Point n → ℝ, (∀ q v a b : Point n, 0 < σ q v a b) ∧
      ∃ Y : Point n → Point n → Point n → Point n → ℝ → ℝ →
          (Point n × Point n) × (Point n × Point n),
      ∃ S : Point n → Point n → Point n → Point n →
          Set ((Point n × Point n) × (Point n × Point n)),
        (∀ q v a b : Point n, IsCompact (S q v a b)) ∧
        (∀ q v a b : Point n, Convex ℝ (S q v a b)) ∧
        ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ / 2 → ∀ a b : Point n,
          ∀ s ∈ Set.Icc (-(σ q v a b)) (σ q v a b),
            Y q v a b s 0 = ((q, v + s • a), ((0 : Point n), b)) ∧
            (∀ τ ∈ Set.Icc (0 : ℝ) 1,
              HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ) ∧
            (∀ τ ∈ Set.Icc (0 : ℝ) 1,
              ‖(Y q v a b s τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v + s • a‖) ∧
            Y q v a b s 0 - Y q v a b 0 0
              = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
            (∀ τ ∈ Set.Icc (0 : ℝ) 1, Y q v a b s τ ∈ S q v a b) := by
  classical
  obtain ⟨ρ, hρ0, C₀, hC0, hconf⟩ := geodesic_apriori_confinement_uniform g gi hC hK
  -- Uniform operator-norm bound `K'_q` on `fderiv (geodesicField)` over the geodesic ball for each `q`.
  have hAcompact : ∀ q : Point n,
      IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    fun q => isCompact_closedBall _ _
  have hbd : ∀ q : Point n, ∃ Kb : ℝ, 0 ≤ Kb ∧
      ∀ z ∈ Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ),
        ‖fderiv ℝ (geodesicField g gi) z‖ ≤ Kb :=
    fun q => geodesicField_fderiv_bddOn_compact g gi hC (hAcompact q)
  choose Kbq hKbq0 hKbqbd using hbd
  -- Per-seed confined doubled integral curve at a fixed admissible velocity `w`, WITH the Jacobi
  -- Grönwall bound `‖(Yc τ).2‖ ≤ ‖(0,b)‖·e^{K'_q}`.
  have hcurve : ∀ q ∈ K, ∀ w : Point n, ‖w‖ ≤ ρ → ∀ b : Point n,
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        Yc 0 = ((q, w), ((0 : Point n), b)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Yc τ).2‖ ≤ ‖((0 : Point n), b)‖ * Real.exp (Kbq q)) := by
    intro q hq w hw b
    obtain ⟨P, hP0, hPderiv, hPconf⟩ := hconf q hq w hw
    have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      intro t ht
      have htoo : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ((hPderiv t htoo).continuousAt).continuousWithinAt
    obtain ⟨J, hJ0, hJderiv⟩ :=
      geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC P hPcont ((0 : Point n), b)
    -- fderiv bound along the confined geodesic base curve `P` on `[0,1]`.
    have hfderivbd : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kbq q := by
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      refine hKbqbd q (P x) ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖P x - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖ := hPconf x hxIcc
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hw hC0
    -- Grönwall on the Jacobi factor: `‖J τ‖ ≤ gronwallBound ‖(0,b)‖ (K'_q) 0 (τ-0)`.
    have hJcont : ContinuousOn J (Set.Icc (0 : ℝ) 1) :=
      fun τ hτ => ((hJderiv τ hτ).continuousAt).continuousWithinAt
    have hJbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        ‖J x‖ ≤ gronwallBound ‖((0 : Point n), b)‖ (Kbq q) 0 (x - 0) :=
      norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖((0 : Point n), b)‖)
        (K := Kbq q) (ε := 0) (a := 0) (b := 1) hJcont
        (fun x hx => (hJderiv x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
        (le_of_eq (by rw [hJ0]))
        (fun x hx => by
          have hle := (fderiv ℝ (geodesicField g gi) (P x)).le_opNorm (J x)
          calc ‖fderiv ℝ (geodesicField g gi) (P x) (J x)‖
              ≤ ‖fderiv ℝ (geodesicField g gi) (P x)‖ * ‖J x‖ := hle
            _ ≤ Kbq q * ‖J x‖ := mul_le_mul_of_nonneg_right (hfderivbd x hx) (norm_nonneg _)
            _ = Kbq q * ‖J x‖ + 0 := by ring)
    refine ⟨fun t => (P t, J t), ?_, ?_, ?_, ?_⟩
    · show (P 0, J 0) = ((q, w), ((0 : Point n), b)); rw [hP0, hJ0]
    · intro τ hτ
      have htoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact doubledField_prod_hasDerivAt g gi (hPderiv τ htoo) (hJderiv τ hτ)
    · intro τ hτ; simpa using hPconf τ hτ
    · intro τ hτ
      show ‖J τ‖ ≤ ‖((0 : Point n), b)‖ * Real.exp (Kbq q)
      have h1 := hJbound τ hτ
      rw [sub_zero, gronwallBound_ε0] at h1
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [Real.exp_le_exp]
      calc Kbq q * τ ≤ Kbq q * 1 := mul_le_mul_of_nonneg_left hτ.2 (hKbq0 q)
        _ = Kbq q := mul_one _
  -- Total doubled family via choice: genuine curve where admissible, junk otherwise.
  have key : ∀ (q w b : Point n),
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        (q ∈ K → ‖w‖ ≤ ρ →
          Yc 0 = ((q, w), ((0 : Point n), b)) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            ‖(Yc τ).2‖ ≤ ‖((0 : Point n), b)‖ * Real.exp (Kbq q))) := by
    intro q w b
    by_cases h : q ∈ K ∧ ‖w‖ ≤ ρ
    · obtain ⟨Yc, h1, h2, h3, h4⟩ := hcurve q h.1 w h.2 b
      exact ⟨Yc, fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨fun _ => 0, fun hq hw => absurd ⟨hq, hw⟩ h⟩
  refine ⟨ρ, hρ0, C₀, hC0, fun q v a b => ρ / (2 * (1 + ‖a‖)), ?_,
    fun q v a b s => Classical.choose (key q (v + s • a) b),
    fun q v a b => Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) (‖((0 : Point n), b)‖ * Real.exp (Kbq q)),
    ?_, ?_, ?_⟩
  · intro q v a b; exact div_pos hρ0 (by positivity)
  · intro q v a b; exact (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  · intro q v a b; exact (convex_closedBall _ _).prod (convex_closedBall _ _)
  intro q hq v hv a b s hs
  dsimp only at hs ⊢
  set σv : ℝ := ρ / (2 * (1 + ‖a‖)) with hσv
  have hσvpos : 0 < σv := by rw [hσv]; exact div_pos hρ0 (by positivity)
  -- Velocity window keeps `‖v + s • a‖ ≤ ρ`.
  have hσva : σv * ‖a‖ ≤ ρ / 2 := by
    have hne' : (1 + ‖a‖) ≠ 0 := by positivity
    have heq : σv * (1 + ‖a‖) = ρ / 2 := by rw [hσv]; field_simp
    calc σv * ‖a‖ ≤ σv * (1 + ‖a‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg a]) hσvpos.le
      _ = ρ / 2 := heq
  have hws : ‖v + s • a‖ ≤ ρ := by
    have habs : |s| ≤ σv := abs_le.mpr ⟨hs.1, hs.2⟩
    have h1 : ‖v + s • a‖ ≤ ‖v‖ + |s| * ‖a‖ := by
      calc ‖v + s • a‖ ≤ ‖v‖ + ‖s • a‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |s| * ‖a‖ ≤ σv * ‖a‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg a)
    linarith [hv, hσva, h1, h2]
  have hw0 : ‖v + (0 : ℝ) • a‖ ≤ ρ := by
    rw [zero_smul, add_zero]; linarith [hv, hρ0.le]
  obtain ⟨hY0s, hYodes, hconfs, hJacs⟩ := Classical.choose_spec (key q (v + s • a) b) hq hws
  have hY00 := (Classical.choose_spec (key q (v + (0 : ℝ) • a) b) hq hw0).1
  refine ⟨hY0s, hYodes, hconfs, ?_, ?_⟩
  · rw [hY0s, hY00]
    simp only [Prod.mk_sub_mk, sub_self, Prod.smul_mk, smul_zero, add_sub_add_left_eq_sub,
      zero_smul, sub_zero, Prod.mk_zero_zero]
  · -- FULL-point confinement `hmem` from the geodesic confinement + Jacobi Grönwall bound.
    intro τ hτ
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖(Classical.choose (key q (v + s • a) b) τ).1 - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + s • a‖ := hconfs τ hτ
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hws hC0
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hJacs τ hτ

end QIQTH.ExpMap
