/-
  DoubledFamilyFullSupply — J4-45: constructing the `s`-perturbed confined DOUBLED-FAMILY supply for
  the CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## Context

  The CLOSE bridge `(J)` (compact-uniform local exp-nondegeneracy radius) is proved in
  `JacobiDoubledFamily.lean` from a CARRIED, now per-`(a,b)` doubled-family SUPPLY over the compact `K`
  (`σ q v a b`, `S q v a b`).  `DoubledFamilyAssembly.lean` (J4-43) landed the FIXED-seed confined
  doubled integral curve `confined_doubled_family_exists` (geodesic-factor confinement, `Ioo 0 1`
  derivatives).  This file extends that heart to the `s`-PERTURBED family with base velocity `v + s·a`
  and per-`(a,b)` velocity window `σ q v a b`, delivering — GREEN and satisfiable, not vacuous — the
  reachable subset of the bridge's `(S1)` supply binders:
    * `hYode` on the CLOSED `Icc 0 1` (two-sided derivatives at the endpoints, the exact bridge shape);
    * `hIC` in the bridge's EXACT affine shape `Y…s 0 − Y…0 0 = s • ((0,a),(0,0))`;
    * geodesic-factor confinement `‖(Y…s τ).1 − (q,0)‖ ≤ C₀‖v+s·a‖`, uniform over `q ∈ K`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `linODE_exists_hasDerivAt_Icc_narrow` — the narrow-padded (`[-1/2,3/2]`) two-sided `Icc 0 1`
    linear-ODE existence: `A` continuous on `[-1/2,3/2]` (a base interval available INSIDE the confined
    tube's open existence window `(-2,2)`, unlike the `[-1,2]` engine which needs the endpoint `2`) gives
    a solution with genuine two-sided `HasDerivAt` on `[0,1]`.  Built from `linODE_exists_forward`
    (to `3/2`), `linODE_exists_backward` (to `-1/2`), glued at `0` (`glue_Icc_hasDerivWithinAt`).

  * `geodesicJacobi_narrowpad_hasDerivAt_Icc` — the geodesic specialisation: for a base curve continuous
    on `[-1/2,3/2]` the Jacobi field `J' = DF(Ybase)·J` has two-sided `HasDerivAt` on `[0,1]`.

  * `sPerturbed_confined_doubled_family_exists` — **the `(S1)` `s`-perturbed confined doubled-family
    supply.**  Over a compact `K`, ONE `ρ > 0` and ONE `C₀ ≥ 0`, a per-`(a,b)` positive window
    `σ q v a b = ρ/(2(1+‖a‖))`, and a doubled family `Y q v a b s` such that for all `q ∈ K`,
    `‖v‖ ≤ ρ/2`, seeds `a, b`, and `s ∈ [-σ,σ]`:
      * `Y q v a b s 0 = ((q, v+s·a), (0,b))` — base geodesic IC at velocity `v+s·a`, Jacobi seed `(0,b)`;
      * `∀ τ ∈ [0,1], HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ` — the doubled ODE;
      * `∀ τ ∈ [0,1], ‖(Y q v a b s τ).1 − (q,0)‖ ≤ C₀‖v+s·a‖` — geodesic-factor confinement;
      * `Y q v a b s 0 − Y q v a b 0 0 = s • ((0,a),(0,0))` — the bridge's EXACT affine IC.
    The velocity window `σ q v a b` keeps `‖v+s·a‖ ≤ ρ` for all `|s| ≤ σ` (since `‖a‖/(1+‖a‖) < 1`), so
    the confined tube exists at every perturbed velocity.  DERIVED by welding
    `geodesic_apriori_confinement_uniform` (the confined geodesic base, uniform over `K`),
    `geodesicJacobi_narrowpad_hasDerivAt_Icc` (the Jacobi field on the closed `[0,1]`), and
    `doubledField_prod_hasDerivAt` (the pair is a `doubledField` integral curve).

  ## HONEST FIREWALL (binding) — why this does NOT close `(J)` self-contained

  This file discharges the `(S1)` ODE / IC / geodesic-confinement structure of the bridge's supply.  It
  does NOT feed the full CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply`, which additionally
  CARRIES (each still an honest input, none smuggled):

  1. `hmem : Y q v a b s τ ∈ S q v a b` — confinement of the FULL doubled point (incl. the Jacobi
     factor) into a compact convex `S q v a b`.  We confine only the GEODESIC factor; bounding the
     Jacobi factor into `S q v a b` needs a Grönwall spread bound on the linearized ODE solution (its
     norm `≤ ‖(0,b)‖·e^{K'}`), plus `hScompact`/`hSconvex` for the enclosing product ball.  CARRIED.
  2. `Vf`/`hVode`/`hV0` — the doubled linearized field with seed `((0,a),(0,0))` along `Y…0`.  A further
     linODE along the base doubled curve (same engines, generator `fderiv (doubledField)(Y…0 τ)`).
     CARRIED.
  3. `hlink : (Y q v a b s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v+s·a) b` — the first-jet endpoint
     identification of the constructed Jacobi position field with the exp-map IC-derivative.  The
     pointwise ingredient exists (`flowVelocity_endpoint_position_hasFDerivAt_exists`); welding it by
     linear-ODE-solution uniqueness is a separate assembly.  CARRIED.
  4. `Zf`/`Src` and the entire second-variation block (`hZf`, `h0d`, `hKbd`, `hZ`, `h0cap`, `hKbcap`,
     `hAd`, `hXb`, `hSd`) — the second-variation engine plus the uniform / Lipschitz-in-`q` operator-norm
     bounds over `K` (`BoundedGeometry`).  CARRIED.

  So `(J)` is NOT closed self-contained here.  This file constructs the `s`-perturbed confined doubled
  family (the (S1) ODE/IC/geodesic-confinement heart, per-`(a,b)`, satisfiable NOT vacuous) and firewalls
  (1)–(4) honestly.  It does NOT smuggle `hid`/`hlink`/`Zf`, does NOT build the covariant `D²/dτ²`, NOT
  Raychaudhuri, NOT `a₁ = R/6`, and the conclusion (a uniform common exp-nondeg radius) is NOT among any
  hypotheses.
-/
import QIQTH.JacobiDoubledFamily
import QIQTH.DoubledFamilyAssembly
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyConstruction
import QIQTH.BoundedGeometryConfine
import QIQTH.VelocitySecondJetId
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

section NarrowPad

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Narrow-padded two-sided `Icc 0 1` linear-ODE existence.**  With the time-dependent operator `A`
    continuous on `[-1/2, 3/2]` — a padded interval that fits INSIDE the confined geodesic tube's open
    existence window `(-2,2)`, unlike the `[-1,2]` engine `linODE_exists_hasDerivAt_Icc` which needs the
    endpoint `2` (outside `(-2,2)`) — the linear ODE `J' τ = A τ (J τ)` with seed `w₀` at `0` has a
    solution with genuine two-sided `HasDerivAt` on the CLOSED `[0,1]`.  Forward on `[0,3/2]`, backward
    on `[-1/2,0]`, glued at `0`; every `τ ∈ [0,1] ⊆ Ioo (-1/2) (3/2)` gets a two-sided derivative. -/
theorem linODE_exists_hasDerivAt_Icc_narrow (A : ℝ → (E →L[ℝ] E))
    (hA : ContinuousOn A (Set.Icc (-(1/2) : ℝ) (3/2))) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (A τ (J τ)) τ := by
  obtain ⟨Jf, hJf0, hJfd⟩ := linODE_exists_forward A (3/2) (by norm_num)
    (hA.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) w₀
  obtain ⟨Jb, hJb0, hJbd⟩ := linODE_exists_backward A (1/2) (by norm_num)
    (hA.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) w₀
  set J := glueAt 0 Jb Jf with hJdef
  have hmatch : Jb 0 = Jf 0 := by rw [hJb0, hJf0]
  have hglue := glue_Icc_hasDerivWithinAt (F := fun t (y : E) => A t y)
    (a := -(1/2)) (b := 0) (c := 3/2) (by norm_num) (by norm_num) hmatch hJbd hJfd
  refine ⟨J, ?_, fun τ hτ => ?_⟩
  · have hJ0 : J 0 = Jb 0 := by rw [hJdef]; simp only [glueAt]; rw [if_pos (le_refl (0 : ℝ))]
    rw [hJ0, hJb0]
  · have hmem : τ ∈ Set.Icc (-(1/2) : ℝ) (3/2) := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (hglue τ hmem).hasDerivAt (Icc_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2]))

end NarrowPad

variable {n : ℕ}

/-- **Geodesic Jacobi-field existence with two-sided `HasDerivAt` on `[0,1]` from a narrow-padded base.**
    For a base curve `Ybase` continuous on `[-1/2, 3/2]` (available for the confined geodesic phase-flow,
    which exists on the open `(-2,2) ⊇ [-1/2,3/2]`), the Jacobi field
    `J' τ = fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)` solves on `[0,1]` with genuine two-sided
    derivatives and `J 0 = w₀`.  Continuity of the operator `A τ = fderiv (geodesicField)(Ybase τ)` is
    DERIVED from `geodesicField ∈ C^∞`.  The `Icc`-derivative Jacobi shape the bridge's `hYode` wants. -/
theorem geodesicJacobi_narrowpad_hasDerivAt_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase : ℝ → Point n × Point n) (hYbase : ContinuousOn Ybase (Set.Icc (-(1/2) : ℝ) (3/2)))
    (w₀ : Point n × Point n) :
    ∃ J : ℝ → Point n × Point n, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt J (fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)) τ := by
  have hcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  set A : ℝ → (Point n × Point n →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Ybase τ) with hAdef
  have hA : ContinuousOn A (Set.Icc (-(1/2) : ℝ) (3/2)) := hcont.comp_continuousOn hYbase
  exact linODE_exists_hasDerivAt_Icc_narrow A hA w₀

/-- **The `s`-perturbed confined doubled-family supply (`(S1)` heart, per-`(a,b)`).**  Over a compact
    `K` there is ONE `ρ > 0`, ONE `C₀ ≥ 0`, a per-`(a,b)` positive velocity window
    `σ q v a b = ρ/(2(1+‖a‖))`, and a doubled family `Y q v a b s` such that for every `q ∈ K`, every
    `v` with `‖v‖ ≤ ρ/2`, all seeds `a, b`, and all `s ∈ [-(σ q v a b), σ q v a b]`:
      * `Y q v a b s 0 = ((q, v + s • a), (0, b))`;
      * `∀ τ ∈ [0,1], HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ`;
      * `∀ τ ∈ [0,1], ‖(Y q v a b s τ).1 − (q,0)‖ ≤ C₀ * ‖v + s • a‖`;
      * `Y q v a b s 0 − Y q v a b 0 0 = s • (((0:Point n), a), ((0:Point n), (0:Point n)))`.
    This is the `s`-perturbed extension of `confined_doubled_family_exists`, now with `Icc 0 1`
    (endpoint) derivatives and the bridge's EXACT affine `hIC`.  The window `σ` keeps the perturbed
    velocity `v + s·a` inside the confinement radius `ρ` (as `‖a‖/(1+‖a‖) < 1`).  Satisfiable, NOT
    vacuous: the constructed `Y` is a genuine confined doubled integral curve at every admissible seed.
    The full-point confinement (`hmem`), the linearized field `Vf`, the first-jet link `hlink`, and the
    second-variation block remain CARRIED by the bridge (see file firewall). -/
theorem sPerturbed_confined_doubled_family_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∃ σ : Point n → Point n → Point n → Point n → ℝ, (∀ q v a b : Point n, 0 < σ q v a b) ∧
      ∃ Y : Point n → Point n → Point n → Point n → ℝ → ℝ →
          (Point n × Point n) × (Point n × Point n),
        ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ / 2 → ∀ a b : Point n,
          ∀ s ∈ Set.Icc (-(σ q v a b)) (σ q v a b),
            Y q v a b s 0 = ((q, v + s • a), ((0 : Point n), b)) ∧
            (∀ τ ∈ Set.Icc (0 : ℝ) 1,
              HasDerivAt (Y q v a b s) (doubledField g gi (Y q v a b s τ)) τ) ∧
            (∀ τ ∈ Set.Icc (0 : ℝ) 1,
              ‖(Y q v a b s τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v + s • a‖) ∧
            Y q v a b s 0 - Y q v a b 0 0
              = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n))) := by
  classical
  obtain ⟨ρ, hρ0, C₀, hC0, hconf⟩ := geodesic_apriori_confinement_uniform g gi hC hK
  -- Per-seed confined doubled integral curve at a fixed admissible velocity `w`.
  have hcurve : ∀ q ∈ K, ∀ w : Point n, ‖w‖ ≤ ρ → ∀ b : Point n,
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        Yc 0 = ((q, w), ((0 : Point n), b)) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) := by
    intro q hq w hw b
    obtain ⟨P, hP0, hPderiv, hPconf⟩ := hconf q hq w hw
    have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
      intro t ht
      have htoo : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      exact ((hPderiv t htoo).continuousAt).continuousWithinAt
    obtain ⟨J, hJ0, hJderiv⟩ :=
      geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC P hPcont ((0 : Point n), b)
    refine ⟨fun t => (P t, J t), ?_, ?_, ?_⟩
    · show (P 0, J 0) = ((q, w), ((0 : Point n), b)); rw [hP0, hJ0]
    · intro τ hτ
      have htoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      exact doubledField_prod_hasDerivAt g gi (hPderiv τ htoo) (hJderiv τ hτ)
    · intro τ hτ; simpa using hPconf τ hτ
  -- Package a total doubled family via choice: genuine curve where admissible, junk otherwise.
  have key : ∀ (q w b : Point n),
      ∃ Yc : ℝ → (Point n × Point n) × (Point n × Point n),
        (q ∈ K → ‖w‖ ≤ ρ →
          Yc 0 = ((q, w), ((0 : Point n), b)) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Yc (doubledField g gi (Yc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            ‖(Yc τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖)) := by
    intro q w b
    by_cases h : q ∈ K ∧ ‖w‖ ≤ ρ
    · obtain ⟨Yc, h1, h2, h3⟩ := hcurve q h.1 w h.2 b
      exact ⟨Yc, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ => 0, fun hq hw => absurd ⟨hq, hw⟩ h⟩
  refine ⟨ρ, hρ0, C₀, hC0, fun q v a b => ρ / (2 * (1 + ‖a‖)), ?_,
    fun q v a b s => Classical.choose (key q (v + s • a) b), ?_⟩
  · intro q v a b; exact div_pos hρ0 (by positivity)
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
  obtain ⟨hY0s, hYodes, hconfs⟩ := Classical.choose_spec (key q (v + s • a) b) hq hws
  have hY00 := (Classical.choose_spec (key q (v + (0 : ℝ) • a) b) hq hw0).1
  refine ⟨hY0s, hYodes, hconfs, ?_⟩
  rw [hY0s, hY00]
  simp only [Prod.mk_sub_mk, sub_self, Prod.smul_mk, smul_zero, add_sub_add_left_eq_sub,
    zero_smul, sub_zero, Prod.mk_zero_zero]

end QIQTH.ExpMap
