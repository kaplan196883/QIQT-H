/-
  DoubledVariationField — J4-47: constructing the doubled linearized variation field `Vf` with its
  IC `hV0` and ODE `hVode` for the CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply`
  (`JacobiDoubledFamily.lean`).

  ## Context

  `DoubledFamilyConfine.lean` (J4-46) discharged the bridge's `(S1)` full-point confinement
  (`hScompact`/`hSconvex`/`hmem`) on top of the `s`-perturbed confined doubled-family supply
  (`DoubledFamilyFullSupply.lean`, J4-45: `hYode`/`hIC`/`σ`).  The remaining `(S1)` residual was the
  doubled linearized variation field `Vf` with `hV0 : Vf q v a b 0 = ((0,a),(0,0))` and
  `hVode : ∀ τ ∈ [0,1], HasDerivAt (Vf q v a b) (fderiv (doubledField g gi) (Y…0 τ) (Vf q v a b τ)) τ`
  — a linear ODE ONE LEVEL UP whose base is the DOUBLED base curve `Y…0 = (P₀, J₀)`.  Running the
  narrow-pad linODE engine on it needs padded (`[-1/2,3/2]`) CONTINUITY of the base doubled curve,
  which `geodesicJacobi_narrowpad_hasDerivAt_Icc` exposes only as `HasDerivAt` on `[0,1]`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `linODE_exists_narrowpad_continuousOn` (**D1a**) — the narrow-padded linear-ODE existence, now ALSO
    exposing `ContinuousOn J (Icc (-1/2) (3/2))`.  The glued solution (forward on `[0,3/2]`, backward on
    `[-1/2,0]`) has `HasDerivWithinAt` on the WHOLE padded `[-1/2,3/2]` (`glue_Icc_hasDerivWithinAt`),
    hence is continuous there — the padded continuity is EXTRACTED from the existing glue witness.
  * `geodesicJacobi_narrowpad_continuousOn` (**D1b**) — the geodesic Jacobi specialization with padded
    continuity: for a base curve continuous on `[-1/2,3/2]`, the Jacobi field is continuous on
    `[-1/2,3/2]` (not merely `[0,1]`).  So the base DOUBLED curve `Y…0 = (P₀, J₀)` is padded-continuous.
  * `doubledVariation_narrowpad_hasDerivAt_Icc` (**D2**) — `Vf` as a GENUINE linODE solution: for a
    padded-continuous base doubled curve `Ybase₀` and seed `w₀`, the linear ODE
    `V' τ = fderiv (doubledField g gi) (Ybase₀ τ) (V τ)` has a solution with `V 0 = w₀` and two-sided
    `HasDerivAt` on `[0,1]`.  `A₂ τ = fderiv (doubledField)(Ybase₀ τ)` is continuous on `[-1/2,3/2]`
    (`contDiff_doubledField ⇒ continuous_fderiv`, composed with the padded-continuous base).
  * `confined_doubled_family_with_variation_exists` (**D3**) — the `(S1)+Vf` supply: the J4-46 confined
    doubled family EXTENDED with `Vf`/`hVode`/`hV0`.  Reconstructs the confined family from
    `geodesic_apriori_confinement_uniform` (so the base doubled curve `Y…0` is exposed with padded
    continuity via D1b), pairs it with the D2 variation field, and re-derives the J4-45/J4-46 supply
    (`hYode`/`hIC`/`hmem` + compact convex `S`).  So `hYode`/`hIC`/`σ`/`hScompact`/`hSconvex`/`hmem`
    AND `Vf`/`hVode`/`hV0` are all discharged here.  SATISFIABLE, not vacuous: `Vf` is a genuine
    `doubledField`-linearized integral curve, `hV0`/`hVode` PROVED.

  ## HONEST FIREWALL (binding) — what remains CARRIED by the bridge

  This discharges the `(S1)` supply INCLUDING `Vf`/`hVode`/`hV0`.  It does NOT construct:

  1. `hlink` — the first-jet endpoint identification `(Y…s 1).2.1 = fderiv (expMap g gi hC q)(v+s·a) b`.
     CARRIED.
  2. the second-variation block (`Zf`/`Src`, `hZf`, `h0d`, `hKbd`, `hZ`, `h0cap`, `hKbcap`, `hAd`,
     `hXb`, `hSd`).  CARRIED.

  So `(J)` is NOT closed self-contained here: this file discharges the `(S1)+Vf` supply, leaving
  `hlink` and the second-variation block as the honest residual.  It does NOT smuggle `hid`/`hlink`,
  does NOT build the covariant `D²/dτ²`, NOT Raychaudhuri, NOT `a₁ = R/6`, and the conclusion is NOT
  among any hypotheses.
-/
import QIQTH.DoubledFamilyConfine
import QIQTH.DoubledFamilyFullSupply
import QIQTH.JacobiDoubledFamily
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyConstruction
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

section NarrowPadContinuousOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **D1a — Narrow-padded linear-ODE existence WITH padded continuity.**  With `A` continuous on the
    padded `[-1/2, 3/2]` (fitting inside the confined tube's `(-2,2)` window), the linear ODE
    `J' τ = A τ (J τ)` with seed `w₀` at `0` has a solution with two-sided `HasDerivAt` on the closed
    `[0,1]` AND `ContinuousOn J (Icc (-1/2) (3/2))`.  The glued solution (forward on `[0,3/2]`, backward
    on `[-1/2,0]`) has `HasDerivWithinAt` on the whole padded interval, hence continuity there. -/
theorem linODE_exists_narrowpad_continuousOn (A : ℝ → (E →L[ℝ] E))
    (hA : ContinuousOn A (Set.Icc (-(1/2) : ℝ) (3/2))) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (A τ (J τ)) τ) ∧
      ContinuousOn J (Set.Icc (-(1/2) : ℝ) (3/2)) := by
  obtain ⟨Jf, hJf0, hJfd⟩ := linODE_exists_forward A (3/2) (by norm_num)
    (hA.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) w₀
  obtain ⟨Jb, hJb0, hJbd⟩ := linODE_exists_backward A (1/2) (by norm_num)
    (hA.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) w₀
  set J := glueAt 0 Jb Jf with hJdef
  have hmatch : Jb 0 = Jf 0 := by rw [hJb0, hJf0]
  have hglue := glue_Icc_hasDerivWithinAt (F := fun t (y : E) => A t y)
    (a := -(1/2)) (b := 0) (c := 3/2) (by norm_num) (by norm_num) hmatch hJbd hJfd
  refine ⟨J, ?_, fun τ hτ => ?_, fun t ht => ?_⟩
  · have hJ0 : J 0 = Jb 0 := by rw [hJdef]; simp only [glueAt]; rw [if_pos (le_refl (0 : ℝ))]
    rw [hJ0, hJb0]
  · have hmem : τ ∈ Set.Icc (-(1/2) : ℝ) (3/2) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (hglue τ hmem).hasDerivAt (Icc_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2]))
  · exact (hglue t ht).continuousWithinAt

end NarrowPadContinuousOn

variable {n : ℕ}

/-- **D1b — Geodesic Jacobi narrow-pad existence WITH padded continuity.**  For a base curve `Ybase`
    continuous on `[-1/2,3/2]`, the Jacobi field `J' τ = fderiv (geodesicField g gi)(Ybase τ)(J τ)`
    solves on `[0,1]` with two-sided `HasDerivAt` and is `ContinuousOn` on the padded `[-1/2,3/2]`.
    Continuity of `A τ = fderiv (geodesicField)(Ybase τ)` is DERIVED from `geodesicField ∈ C^∞`. -/
theorem geodesicJacobi_narrowpad_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase : ℝ → Point n × Point n) (hYbase : ContinuousOn Ybase (Set.Icc (-(1/2) : ℝ) (3/2)))
    (w₀ : Point n × Point n) :
    ∃ J : ℝ → Point n × Point n, J 0 = w₀ ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt J (fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)) τ) ∧
      ContinuousOn J (Set.Icc (-(1/2) : ℝ) (3/2)) := by
  have hcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  set A : ℝ → (Point n × Point n →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Ybase τ) with hAdef
  have hA : ContinuousOn A (Set.Icc (-(1/2) : ℝ) (3/2)) := hcont.comp_continuousOn hYbase
  exact linODE_exists_narrowpad_continuousOn A hA w₀

/-- **D2 — The doubled linearized variation field `Vf` as a genuine linODE solution.**  For a base
    DOUBLED curve `Ybase₀` continuous on `[-1/2,3/2]` and a seed `w₀`, the linear ODE
    `V' τ = fderiv (doubledField g gi)(Ybase₀ τ)(V τ)` has a solution `V` with `V 0 = w₀` and two-sided
    `HasDerivAt` on `[0,1]`.  The operator `A₂ τ = fderiv (doubledField)(Ybase₀ τ)` is continuous on
    `[-1/2,3/2]` (`contDiff_doubledField ⇒ continuous_fderiv`, composed with the padded-continuous
    base).  This is EXACTLY the bridge's `Vf`/`hV0`/`hVode` data along the base doubled curve. -/
theorem doubledVariation_narrowpad_hasDerivAt_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase₀ : ℝ → (Point n × Point n) × (Point n × Point n))
    (hYbase₀ : ContinuousOn Ybase₀ (Set.Icc (-(1/2) : ℝ) (3/2)))
    (w₀ : (Point n × Point n) × (Point n × Point n)) :
    ∃ V : ℝ → (Point n × Point n) × (Point n × Point n), V 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt V (fderiv ℝ (doubledField g gi) (Ybase₀ τ) (V τ)) τ := by
  have hcont : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  set A : ℝ → (((Point n × Point n) × (Point n × Point n)) →L[ℝ]
      ((Point n × Point n) × (Point n × Point n))) :=
    fun τ => fderiv ℝ (doubledField g gi) (Ybase₀ τ) with hAdef
  have hA : ContinuousOn A (Set.Icc (-(1/2) : ℝ) (3/2)) := hcont.comp_continuousOn hYbase₀
  obtain ⟨V, hV0, hVd, _⟩ := linODE_exists_narrowpad_continuousOn A hA w₀
  exact ⟨V, hV0, hVd⟩

/-- **D3 — The `(S1)+Vf` confined doubled-family supply.**  Over a compact `K` there is ONE `ρ > 0`,
    ONE `C₀ ≥ 0`, a per-`(a,b)` positive window `σ q v a b`, a doubled family `Y q v a b s`, a doubled
    linearized variation field `Vf q v a b`, and a per-`(q,v,a,b)` compact convex product-ball
    confinement set `S q v a b`, such that for every `q ∈ K`, `‖v‖ ≤ ρ/2`, and seeds `a, b`:
      * `Vf q v a b 0 = ((0,a),(0,0))` — the bridge's `hV0`;
      * `∀ τ ∈ [0,1], HasDerivAt (Vf q v a b) (fderiv (doubledField g gi)(Y q v a b 0 τ)(Vf q v a b τ)) τ`
        — the bridge's `hVode` (the doubled field linearized along the base doubled curve `Y…0`);
      * for all `s ∈ [-(σ q v a b), σ q v a b]`: the J4-45/J4-46 supply — `Y q v a b s 0 = ((q,v+s•a),(0,b))`,
        `hYode`, geodesic-factor confinement, the exact affine `hIC`, and the full-point confinement `hmem`.
    So `hYode`/`hIC`/`σ`/`hScompact`/`hSconvex`/`hmem` AND `Vf`/`hVode`/`hV0` are all discharged.  The base
    doubled curve `Y…0 = (P₀, J₀)` is exposed with padded (`[-1/2,3/2]`) continuity via
    `geodesicJacobi_narrowpad_continuousOn`, so `Vf` is a GENUINE `doubledField`-linearized integral curve
    (`doubledVariation_narrowpad_hasDerivAt_Icc`), not vacuous.  `hlink` and the second-variation block
    remain CARRIED (see file firewall). -/
theorem confined_doubled_family_with_variation_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∃ σ : Point n → Point n → Point n → Point n → ℝ, (∀ q v a b : Point n, 0 < σ q v a b) ∧
      ∃ Y : Point n → Point n → Point n → Point n → ℝ → ℝ →
          (Point n × Point n) × (Point n × Point n),
      ∃ Vf : Point n → Point n → Point n → Point n → ℝ →
          (Point n × Point n) × (Point n × Point n),
      ∃ S : Point n → Point n → Point n → Point n →
          Set ((Point n × Point n) × (Point n × Point n)),
        (∀ q v a b : Point n, IsCompact (S q v a b)) ∧
        (∀ q v a b : Point n, Convex ℝ (S q v a b)) ∧
        ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ / 2 → ∀ a b : Point n,
          Vf q v a b 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt (Vf q v a b)
              (fderiv ℝ (doubledField g gi) (Y q v a b 0 τ) (Vf q v a b τ)) τ) ∧
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
  -- Grönwall bound AND padded (`[-1/2,3/2]`) continuity of the whole doubled curve.
  have hcurve : ∀ q ∈ K, ∀ w : Point n, ‖w‖ ≤ ρ → ∀ b : Point n,
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        Yc 0 = ((q, w), ((0 : Point n), b)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Yc τ).2‖ ≤ ‖((0 : Point n), b)‖ * Real.exp (Kbq q)) ∧
        ContinuousOn Yc (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro q hq w hw b
    obtain ⟨P, hP0, hPderiv, hPconf⟩ := hconf q hq w hw
    have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      intro t ht
      have htoo : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ((hPderiv t htoo).continuousAt).continuousWithinAt
    obtain ⟨J, hJ0, hJderiv, hJpad⟩ :=
      geodesicJacobi_narrowpad_continuousOn g gi hC P hPcont ((0 : Point n), b)
    -- fderiv bound along the confined geodesic base curve `P` on `[0,1]`.
    have hfderivbd : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kbq q := by
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      refine hKbqbd q (P x) ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖P x - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖ := hPconf x hxIcc
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hw hC0
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
    refine ⟨fun t => (P t, J t), ?_, ?_, ?_, ?_, ?_⟩
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
    · exact hPcont.prodMk hJpad
  -- Total doubled family via choice: genuine curve where admissible, junk otherwise.
  have key : ∀ (q w b : Point n),
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        (q ∈ K → ‖w‖ ≤ ρ →
          Yc 0 = ((q, w), ((0 : Point n), b)) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            ‖(Yc τ).2‖ ≤ ‖((0 : Point n), b)‖ * Real.exp (Kbq q)) ∧
          ContinuousOn Yc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro q w b
    by_cases h : q ∈ K ∧ ‖w‖ ≤ ρ
    · obtain ⟨Yc, h1, h2, h3, h4, h5⟩ := hcurve q h.1 w h.2 b
      exact ⟨Yc, fun _ _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨fun _ => 0, fun hq hw => absurd ⟨hq, hw⟩ h⟩
  -- Variation field `Vf` via the doubled-variation linODE along the base doubled curve `Y…0`.
  have varkey : ∀ (q v a b : Point n),
      ∃ V : ℝ → (Point n × Point n) × (Point n × Point n),
        (q ∈ K → ‖v‖ ≤ ρ →
          V 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt V
              (fderiv ℝ (doubledField g gi)
                (Classical.choose (key q (v + (0 : ℝ) • a) b) τ) (V τ)) τ)) := by
    intro q v a b
    by_cases h : q ∈ K ∧ ‖v‖ ≤ ρ
    · have hbase : ‖v + (0 : ℝ) • a‖ ≤ ρ := by rw [zero_smul, add_zero]; exact h.2
      obtain ⟨_, _, _, _, hpad⟩ := Classical.choose_spec (key q (v + (0 : ℝ) • a) b) h.1 hbase
      obtain ⟨V, hV0, hVd⟩ := doubledVariation_narrowpad_hasDerivAt_Icc g gi hC
        (Classical.choose (key q (v + (0 : ℝ) • a) b)) hpad
        (((0 : Point n), a), ((0 : Point n), (0 : Point n)))
      exact ⟨V, fun _ _ => ⟨hV0, hVd⟩⟩
    · exact ⟨fun _ => 0, fun hq hv => absurd ⟨hq, hv⟩ h⟩
  refine ⟨ρ, hρ0, C₀, hC0, fun q v a b => ρ / (2 * (1 + ‖a‖)), ?_,
    fun q v a b s => Classical.choose (key q (v + s • a) b),
    fun q v a b => Classical.choose (varkey q v a b),
    fun q v a b => Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) (‖((0 : Point n), b)‖ * Real.exp (Kbq q)),
    ?_, ?_, ?_⟩
  · intro q v a b; exact div_pos hρ0 (by positivity)
  · intro q v a b; exact (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  · intro q v a b; exact (convex_closedBall _ _).prod (convex_closedBall _ _)
  intro q hq v hv a b
  have hvρ : ‖v‖ ≤ ρ := hv.trans (half_le_self hρ0.le)
  obtain ⟨hVfV0, hVfode⟩ := Classical.choose_spec (varkey q v a b) hq hvρ
  refine ⟨hVfV0, hVfode, ?_⟩
  intro s hs
  dsimp only at hs ⊢
  set σv : ℝ := ρ / (2 * (1 + ‖a‖)) with hσv
  have hσvpos : 0 < σv := by rw [hσv]; exact div_pos hρ0 (by positivity)
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
  obtain ⟨hY0s, hYodes, hconfs, hJacs, _⟩ :=
    Classical.choose_spec (key q (v + s • a) b) hq hws
  have hY00 := (Classical.choose_spec (key q (v + (0 : ℝ) • a) b) hq hw0).1
  refine ⟨hY0s, hYodes, hconfs, ?_, ?_⟩
  · rw [hY0s, hY00]
    simp only [Prod.mk_sub_mk, sub_self, Prod.smul_mk, smul_zero, add_sub_add_left_eq_sub,
      zero_smul, sub_zero, Prod.mk_zero_zero]
  · intro τ hτ
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖(Classical.choose (key q (v + s • a) b) τ).1 - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + s • a‖ := hconfs τ hτ
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hws hC0
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hJacs τ hτ

end QIQTH.ExpMap
