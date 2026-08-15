/-
  UniformFlowThirdJetClose2 — J4-677 (Brick-A β, C³ climb, W2 CLOSE): the value-identification (Y4)
  that turns the banked quadruple-flow supply (J4-73) into the per-seed THIRD jet of `uniformFlowExp`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It closes the
  W2 leg of the C³ climb of the exp-map jets, one order up from J4-67's R2-b.  No `sorry` (header prose
  excepted), no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-a-hyp.
  std-3 only.  No existing file is edited.

  ── CONTEXT (what was already banked).
    * J4-67 `UniformFlowSecondSupply` — R2-a (doubled-flow supply) + R2-b (per-seed SECOND jet).
    * J4-72 `UniformFlowThirdFDeriv` — the quadrupled field `Φ̃ = genericDoubled (doubledField g gi)`
      with its full regularity supply, and W2-pre (`DifferentiableOn` of the applied second jet).
    * J4-73 `QuadrupleFlowSupply` — Y1/Y2/Y3/Y3′: the base-velocity-perturbed confined QUADRUPLE
      uniform-tube supply and, projecting `.2.1`, the existence of the Fréchet derivative of the
      doubled-linearized endpoint `δ ↦ (Uf δ 1).2.1` at `0` (`uniformFlow_quadrupleEndpoint_component_hasFDerivAt`).
    * J4-481 `SecondVariationModulus` — `uniformFlowExp_secondVar_spec`: the SECOND-jet endpoint
      identification `fderiv (fun w => fderiv (uniformFlowExp q) w b) v = L₂`, `L₂ δ = (Vf δ 1).2.1`,
      with `Vf` the doubled second-variation field along `(tube q v, Jf0)`, seed `((0,δ),(0,0))`.

  ── THE MISSING PIECE the header of `QuadrupleFlowSupply` names as W2's residue (Y4): the value-id
        `(Uf δ 1).2.1 = fderiv (fun w => fderiv (uniformFlowExp q) w b) (v+δ) a`   on the velocity window,
     i.e. the quadruple-supply doubled-linearized endpoint IS the `a`-derivative of the applied second
     jet.  The crux tool it needed was a field-agnostic LINEAR-ODE UNIQUENESS to MATCH the two
     independently-`Classical.choose`'d doubled-linearized families (the quadruple supply's `Uf` and the
     `secondVar_spec`'s `Vf`) — currently ABSENT from the codebase (only the geodesic-specialised
     `jacobiSol_unique` existed).

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `linODE_unique` — **★ the field-agnostic linear-ODE uniqueness (the missing generic tool).**  Two
      solutions of `X' = A(τ)·X` on `[0,1]` in ANY Banach space, with the SAME initial value and a
      bounded coefficient `‖A τ‖ ≤ K`, agree on all of `[0,1]`.  DERIVED from
      `BasepointJetModulus.linODE_twopoint_diff_bound` (the `Dcoef = 0`, `Dsrc = 0` diagonal), with the
      solution bound extracted from continuity on the compact interval.  Reusable for the geodesic, the
      doubled and the quadrupled fields alike; the `q = q'` diagonal generalisation of `jacobiSol_unique`
      to an arbitrary field.

    * `uniformFlow_secondJet_apply_eq_quadEndpoint` — **★ Y4, the value-identification.**  For `q ∈ K`,
      `‖w‖ < ρ_K`, and seeds `a b`, ANY doubled-linearized family `Uf` along the doubled base curve
      `(tube q w, Jf)` (with `Jf` the velocity Jacobi seed `(0,b)`, `Uf` seed `((0,a),(0,0))`) has
        `(Uf 1).2.1 = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u b) w a`.
      DERIVED: `secondVar_spec` at `w` names the same object as `(Vf a 1).2.1`; `linODE_unique` matches
      `Jf` with `secondVar_spec`'s `Jf0` (both velocity Jacobi, same seed), whence the doubled base
      curves coincide, whence `linODE_unique` (doubled field) matches `Uf` with `Vf a` (same seed).

    * `uniformFlowExp_thirdJet_apply_hasFDerivAt` — **★★ W2, the per-seed THIRD jet.**  For `q ∈ K`,
      `‖v‖ < ρ_K`, seeds `a b`, the applied THIRD-jet map
        `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u b) w a`
      has a Fréchet derivative at `v`.  DERIVED: `Y3′` gives the derivative of `δ ↦ (Uf δ 1).2.1` at `0`;
      Y4 rewrites `(Uf δ 1).2.1 = fderiv (…) (v+δ) a` on the window nbhd; transfer + recentre `δ ↦ v+δ`,
      exactly as R2-b recentred R2-a one order down.  NOT `a₁ = R/6`.

  ⚠ WHAT REMAINS (NOT here): W3 (uniform `‖B₃‖` bound), W4 (`uniformFlowExp ∈ C³ ⟹ g̃ ∈ C²`), and the
  CLM-valued third jet (assembling the per-seed scalar jets into an operator-norm little-o).  Those are
  the same residues R2 carried one order down.  NOT `a₁ = R/6`; a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.QuadrupleFlowSupply
import QIQTH.SecondVariationModulus
import QIQTH.BasepointJetModulus
import QIQTH.BasepointFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 10

/-! ### The field-agnostic linear-ODE uniqueness (the missing generic tool). -/

/-- **★ Field-agnostic linear-ODE uniqueness.**  Two solutions `X₁, X₂` of the homogeneous linear ODE
    `X' = A(τ)·X` on `[0,1]` in any Banach space `E`, with the SAME initial value `X₁ 0 = X₂ 0` and a
    bounded coefficient `‖A τ‖ ≤ K`, agree on all of `[0,1]`.  DERIVED from
    `linODE_twopoint_diff_bound` (`Dcoef = 0`, `Dsrc = 0`), the solution bound `Xb` extracted from the
    continuity of `X₂` on the compact interval.  The arbitrary-field generalisation of
    `jacobiSol_unique`. -/
theorem linODE_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → (E →L[ℝ] E)} {X₁ X₂ : ℝ → E} {K : ℝ} (hK0 : 0 ≤ K)
    (hX1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X₁ (A t (X₁ t)) t)
    (hX2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X₂ (A t (X₂ t)) t)
    (h0 : X₁ 0 = X₂ 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    X₁ t = X₂ t := by
  have hX2cont : ContinuousOn X₂ (Set.Icc (0 : ℝ) 1) :=
    fun s hs => ((hX2 s hs).continuousAt).continuousWithinAt
  obtain ⟨Xb, hXb⟩ := isCompact_Icc.exists_bound_of_continuousOn hX2cont
  have hbnd := linODE_twopoint_diff_bound (E := E)
    (A₁ := A) (A₂ := A) (X₁ := X₁) (X₂ := X₂) (b₁ := fun _ => 0) (b₂ := fun _ => 0)
    (K := K) (Dcoef := 0) (Xb := Xb) (Dsrc := 0) hK0
    (fun s hs => by simpa using hX1 s hs)
    (fun s hs => by simpa using hX2 s hs)
    h0 hKb (fun s _ => by simp) hXb (fun s _ => by simp)
  have h := hbnd t ht
  simp only [zero_mul, add_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-! ### Y4 — the value-identification: the quadruple endpoint IS the second-jet `a`-derivative. -/

section Y4

variable {n : ℕ}

/-- **★ Y4 — the value-identification.**  Fix `q ∈ K`, `‖w‖ < ρ_K`, seeds `a b`.  Let `Jf` be ANY
    velocity Jacobi field along `uniformFlowTube g gi hC hK q w` (seed `Jf 0 = (0,b)`, the geodesic
    linearized ODE), and `Uf` ANY `doubledField`-linearized field along the doubled base curve
    `(uniformFlowTube … q w, Jf)` (seed `Uf 0 = ((0,a),(0,0))`).  Then the doubled endpoint's `.2.1`
    component IS the `a`-derivative of the applied second jet:
        `(Uf 1).2.1 = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u b) w a`.
    DERIVED: `uniformFlowExp_secondVar_spec` at `w` names the RHS as `(Vf a 1).2.1` (`L₂ a` via
    `HasFDerivAt.fderiv`); `linODE_unique` matches `Jf` with `secondVar_spec`'s `Jf0` (both velocity
    Jacobi along the same tube, same seed), so the two doubled base curves coincide, so `linODE_unique`
    (doubled field) matches `Uf` with `Vf a` (same seed, same doubled coefficient).  NOT `a₁ = R/6`. -/
theorem uniformFlow_secondJet_apply_eq_quadEndpoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ < uniformFlowRadius g gi hC hK) (a b : Point n)
    (Jf : ℝ → Point n × Point n) (hJf0 : Jf 0 = ((0 : Point n), b))
    (hJfode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Jf (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ) (Jf τ)) τ)
    (Uf : ℝ → (Point n × Point n) × (Point n × Point n))
    (hUf0 : Uf 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hUfode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Uf
        (fderiv ℝ (doubledField g gi)
          ((uniformFlowTube g gi hC hK q w τ, Jf τ) : (Point n × Point n) × (Point n × Point n))
          (Uf τ)) τ) :
    (Uf 1).2.1 = fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) w a := by
  classical
  -- The second-jet endpoint exposure at base velocity `w`.
  obtain ⟨Jf0, Vf, L₂, hJf0'0, hJf0'ode, hVf0, hVfode, hL₂eq, hL₂FD⟩ :=
    QIQTH.SecondVariationModulus.uniformFlowExp_secondVar_spec g gi hC hK q hq w hw b
  -- Continuity of the base tube on `[0,1]`.
  have htubecont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q w τ) (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq w hw.le τ hτoo).continuousAt).continuousWithinAt
  -- Inner matching: `Jf = Jf0` via the geodesic-coefficient bound + `linODE_unique`.
  have hgeocont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hAgeo : ContinuousOn
      (fun τ => fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ)) (Set.Icc (0 : ℝ) 1) :=
    hgeocont.comp_continuousOn htubecont
  obtain ⟨Kgeo, hKgeo⟩ := isCompact_Icc.exists_bound_of_continuousOn hAgeo
  have hKgeo0 : 0 ≤ Kgeo := le_trans (norm_nonneg _) (hKgeo 0 (Set.left_mem_Icc.mpr zero_le_one))
  have hJfeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Jf τ = Jf0 τ := fun τ hτ =>
    linODE_unique (A := fun τ => fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q w τ))
      hKgeo0 hJfode hJf0'ode (by rw [hJf0, hJf0'0]) hKgeo hτ
  -- Doubled base curve `(tube, Jf0)` continuous + coefficient bound.
  have hJf0cont : ContinuousOn Jf0 (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => ((hJf0'ode τ hτ).continuousAt).continuousWithinAt
  have hbasecont : ContinuousOn
      (fun τ => ((uniformFlowTube g gi hC hK q w τ, Jf0 τ) : (Point n × Point n) × (Point n × Point n)))
      (Set.Icc (0 : ℝ) 1) := htubecont.prodMk hJf0cont
  have hdblcont : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  have hAdbl : ContinuousOn
      (fun τ => fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q w τ, Jf0 τ))
      (Set.Icc (0 : ℝ) 1) := hdblcont.comp_continuousOn hbasecont
  obtain ⟨Kdbl, hKdbl⟩ := isCompact_Icc.exists_bound_of_continuousOn hAdbl
  have hKdbl0 : 0 ≤ Kdbl := le_trans (norm_nonneg _) (hKdbl 0 (Set.left_mem_Icc.mpr zero_le_one))
  -- Rewrite `Uf`'s doubled ODE to the `Jf0`-based coefficient (equal base curves).
  have hUfode' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Uf
        (fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q w τ, Jf0 τ) (Uf τ)) τ := by
    intro τ hτ
    have h := hUfode τ hτ
    rw [hJfeq τ hτ] at h
    exact h
  -- Doubled matching: `Uf = Vf a` via `linODE_unique`.
  have hUfeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Uf τ = Vf a τ := fun τ hτ =>
    linODE_unique
      (A := fun τ => fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q w τ, Jf0 τ))
      hKdbl0 hUfode' (hVfode a) (by rw [hUf0, hVf0 a]) hKdbl hτ
  have h1 : Uf 1 = Vf a 1 := hUfeq 1 (Set.right_mem_Icc.mpr zero_le_one)
  rw [h1, ← hL₂eq a, hL₂FD.fderiv]

end Y4

/-! ### W2 — the per-seed THIRD jet of `uniformFlowExp` (Y3′ ⊕ Y4 ⊕ recentre). -/

section W2

variable {n : ℕ}

/-- **★★ W2 — the per-seed THIRD jet.**  For `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b`, the applied
    THIRD-jet map
        `w ↦ fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) w a`
    has a Fréchet derivative at `v`:
        `∃ L₃, HasFDerivAt (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp … q) u b) w a) L₃ v`.
    DERIVED: `Y3′` (`uniformFlow_quadrupleEndpoint_component_hasFDerivAt`) gives the Fréchet derivative
    of `δ ↦ (Uf δ 1).2.1` at `0`; `Y4` rewrites `(Uf δ 1).2.1 = fderiv (…) (v+δ) a` on the velocity
    window nbhd; transfer the derivative across the eventual equality, then recentre `δ ↦ v+δ` — exactly
    as R2-b recentred R2-a one order down.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_thirdJet_apply_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Point n) :
    ∃ L₃ : Point n →L[ℝ] Point n,
      HasFDerivAt
        (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) w a) L₃ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  -- Y3′.
  obtain ⟨Jf, Uf, hprops, L₃, hFD⟩ :=
    uniformFlow_quadrupleEndpoint_component_hasFDerivAt g gi hC hK q hq v hv a b
  -- On the velocity window, `(Uf δ 1).2.1 = fderiv (…) (v+δ) a` (Y4).
  have hEq : (fun δ => (Uf δ 1).2.1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) (v + δ) a) := by
    refine Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds (0 : Point n) hσ) (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ σ := hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJf0, hJfode, hUf0, hUfode⟩ := hprops δ hδσ
    exact uniformFlow_secondJet_apply_eq_quadEndpoint g gi hC hK q hq (v + δ) hvδ a b
      (Jf δ) hJf0 hJfode (Uf δ) hUf0 hUfode
  -- Transfer the Y3′ derivative across the eventual equality.
  have hFD2 : HasFDerivAt
      (fun δ => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) (v + δ) a) L₃ 0 :=
    hFD.congr_of_eventuallyEq hEq.symm
  -- Recentre `δ ↦ v + δ` (i.e. `w ↦ w − v`).
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt
      (fun δ => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) (v + δ) a) L₃ (v - v) := by
    rw [sub_self]; exact hFD2
  have hcomp : HasFDerivAt
      (fun u => fderiv ℝ (fun u' => fderiv ℝ (uniformFlowExp g gi hC hK q) u' b) (v + (u - v)) a)
      (L₃.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun u : Point n => u - v) v hshift
  have hfun2 : (fun u => fderiv ℝ (fun u' => fderiv ℝ (uniformFlowExp g gi hC hK q) u' b) (v + (u - v)) a)
      = (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u b) w a) := by
    funext u; congr 2; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨L₃, hcomp⟩

end W2

end QIQTH.ExpMap
