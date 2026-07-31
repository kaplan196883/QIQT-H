/-
  DoubledFamilyLink — J4-48: discharging `hlink`, the FIRST-JET ENDPOINT IDENTITY of the doubled-family
  supply for the CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply`
  (`JacobiDoubledFamily.lean`).

  ## The target

  The bridge carries the first-jet link
    `hlink : ∀ q ∈ K, ∀ v ∈ closedBall 0 r, ∀ a b, ∀ s ∈ Icc (-(σ q v a b)) (σ q v a b),
              (Y q v a b s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v + s • a) b`.
  With `Y q v a b s = (P, J)` the doubled integral curve — `P` the geodesic phase-flow from
  `(q, v+s·a)`, `J` the Jacobi field with seed `(0,b)` — `(Y … s 1).2.1 = (J 1).1` is the POSITION of
  the Jacobi endpoint.  The claim: this equals the velocity-derivative of the exp-map endpoint.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `doubled_endpoint_eq_expMap_fderiv` — **the hlink identity, per fixed base velocity `w`.**  Given
    a doubled integral curve `Y` with `Y' = doubledField g gi (Y)` on `[0,1]`,
    `Y 0 = ((q,w),(0,b))`, geodesic-factor confinement `‖(Y τ).1 − (q,0)‖ ≤ C₀‖w‖`, and
    `‖w‖ < expRho g gi hC q`, we prove
        `(Y 1).2.1 = fderiv ℝ (expMap g gi hC q) w b`.
    FULLY PROVED via TWO linear/geodesic ODE-uniqueness steps welded to
    `expDiff_flow_isGeodesicVariation` (which identifies `fderiv (expMap q) w = π ∘ Φ(1) ∘ ι`, i.e. the
    exp-derivative IS the position of the flow-column `V_b(τ) = (Φ τ)(0,b)` Jacobi field at `τ=1`):
      (E-base) the geodesic phase-factor `τ ↦ (Y τ).1` equals the exp-tube base geodesic
        `expTube g gi hC q w` on `[0,1]` (`ODE_solution_unique_of_mem_Icc_right` on the geodesic field);
      (E-jac)  the doubled Jacobi factor `τ ↦ (Y τ).2` and the flow column `V_b` solve the SAME linear
        Jacobi ODE `X' = DF(expTube q w τ)·X` on `[0,1]` with the SAME seed `(0,b)`, hence agree at
        `τ=1` (`ODE_solution_unique_of_mem_Icc_right` on the linearized field).
    Projecting `.1` closes the identity.

  * `hlink_of_confined_doubled_family` — **the exact hlink binder shape**, per `(q,v,a,b)` and over the
    seed window, obtained by applying the core identity at `w := v + s·a`.  The ONLY extra input is the
    per-seed radius bound `‖v+s·a‖ < expRho g gi hC q` (a genuine geometric input the caller threads via
    `hr_lt : r < expRho g gi hC q` and the window `σ q v a b` keeping `‖v+s·a‖ ≤ r`).  This is NOT
    smuggled: it is the natural admissibility of the exp-tube, and the conclusion (the endpoint
    identity) is NOT among the hypotheses.

  ## HONEST FIREWALL

  `hlink` is PROVED here (via genuine ODE uniqueness), NOT assumed.  This file does NOT build the
  second-variation block (`Zf`/`Src`/`hZf`/…), does NOT prove `a₁ = R/6`, and does not touch curvature
  identification.  The per-seed radius bound `‖v+s·a‖ < expRho q` is carried as an explicit
  admissibility hypothesis (matching the bridge's `hr_lt`); no other input is introduced.
-/
import Mathlib
import QIQTH.DoubledVariationField
import QIQTH.JacobiDoubledFamily
import QIQTH.ExpDiffVariation
import QIQTH.BasepointFDeriv
import QIQTH.UniformFlowBridge
import QIQTH.GenericJacobiExists

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Topology Filter

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **The hlink identity, per fixed base velocity `w`.**

    For a doubled integral curve `Y` of `doubledField g gi` on `[0,1]` with initial condition
    `Y 0 = ((q,w),(0,b))` and geodesic-factor confinement `‖(Y τ).1 − (q,0)‖ ≤ C₀‖w‖`, and provided the
    base velocity is exp-admissible (`‖w‖ < expRho g gi hC q`), the POSITION of the Jacobi endpoint
    equals the velocity-derivative of the exp-map endpoint:
        `(Y 1).2.1 = fderiv ℝ (expMap g gi hC q) w b`.

    PROOF (two ODE-uniqueness steps, no `sorry`):
    * the geodesic phase factor `(Y ·).1` solves the geodesic field ODE from `(q,w)`, as does the
      exp-tube `expTube g gi hC q w`; Grönwall uniqueness on the confinement ball gives their equality;
    * the doubled Jacobi factor `(Y ·).2` and the flow column `V_b(τ) = (Φ τ)(0,b)` from
      `expDiff_flow_isGeodesicVariation` both solve the linear Jacobi ODE `X' = DF(expTube q w τ)·X`
      with the same seed `(0,b)`, so they agree at `τ=1`;
    * `fderiv (expMap q) w = π ∘ Φ(1) ∘ ι` (the same lemma) makes `fderiv (expMap q) w b = (V_b 1).1`,
      and `.1`-projection of the Jacobi equality closes the goal. -/
theorem doubled_endpoint_eq_expMap_fderiv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q w b : Point n) (hw : ‖w‖ < QIQTH.ExpMap.expRho g gi hC q)
    {C₀ : ℝ}
    {Y : ℝ → (Point n × Point n) × (Point n × Point n)}
    (hY0 : Y 0 = ((q, w), ((0 : Point n), b)))
    (hYode : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y (doubledField g gi (Y τ)) τ)
    (hYconf : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(Y τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖w‖) :
    (Y 1).2.1 = fderiv ℝ (QIQTH.ExpMap.expMap g gi hC q) w b := by
  classical
  -- Notation for the exp-tube base geodesic and the two factors of `Y`.
  set E : ℝ → Point n × Point n := QIQTH.ExpMap.expTube g gi hC q w with hEdef
  -- Exp-tube spec: IC, geodesic ODE on `(-2,2)`, confinement on `[0,1]`.
  obtain ⟨hE0, hEderiv, hEconf⟩ := expTube_spec g gi hC q w hw.le
  -- Interval inclusions.
  have hIco_Ioo : Set.Ico (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hIcc_Ioo : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- The geodesic phase factor `(Y ·).1` solves the geodesic ODE.
  have hPode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (Y t).1) (geodesicField g gi (Y τ).1) τ := by
    intro τ hτ
    have h := (ContinuousLinearMap.fst ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ (hYode τ hτ)
    simpa [Function.comp, doubledField] using h
  -- The doubled Jacobi factor `(Y ·).2` solves the linearized (Jacobi) ODE along `(Y ·).1`.
  have hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (Y t).2)
        (fderiv ℝ (geodesicField g gi) (Y τ).1 (Y τ).2) τ := by
    intro τ hτ
    have h := (ContinuousLinearMap.snd ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ (hYode τ hτ)
    simpa [Function.comp, doubledField] using h
  ------------------------------------------------------------------------------------------------
  -- (E-base) `(Y ·).1 = E` on `[0,1]` by geodesic-flow Grönwall uniqueness.
  ------------------------------------------------------------------------------------------------
  set e : Point n × Point n := (q, 0) with hedef
  set R : ℝ := max (QIQTH.ExpMap.expConst g gi hC q * ‖w‖) (C₀ * ‖w‖) with hRdef
  set S : Set (Point n × Point n) := Metric.closedBall e R with hSdef
  have hScompact : IsCompact S := isCompact_closedBall e R
  have hSconvex : Convex ℝ S := convex_closedBall e R
  -- geodesicField is Lipschitz on the compact convex ball `S`.
  obtain ⟨Kq, hLipS⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconvex hScompact
  -- Confinement of both curves into `S` on `[0,1]`.
  have hmemE : ∀ t ∈ Set.Icc (0 : ℝ) 1, E t ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hEconf t ht) (le_max_left _ _)
  have hmemP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (Y t).1 ∈ S := by
    intro t ht
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    exact le_trans (hYconf t ht) (le_max_right _ _)
  -- Continuity on `[0,1]`.
  have hcontE : ContinuousOn E (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hEderiv t (hIcc_Ioo ht)).continuousAt.continuousWithinAt
  have hcontP : ContinuousOn (fun t => (Y t).1) (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hPode t ht).continuousAt.continuousWithinAt
  -- Grönwall uniqueness `E = (Y ·).1` on `[0,1]`.
  have hEP : Set.EqOn E (fun t => (Y t).1) (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right (v := fun _ => geodesicField g gi)
      (s := fun _ => S) (K := Kq)
      (fun t _ => hLipS) hcontE
      (fun t ht => (hEderiv t (hIco_Ioo ht)).hasDerivWithinAt)
      (fun t ht => hmemE t (Set.Ico_subset_Icc_self ht))
      hcontP
      (fun t ht => (hPode t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => hmemP t (Set.Ico_subset_Icc_self ht))
      (by rw [hEdef, hE0, hY0])
  ------------------------------------------------------------------------------------------------
  -- The exp-differential flow `Φ` and its column `V_b`.
  ------------------------------------------------------------------------------------------------
  obtain ⟨Φ, hΦ0, hFD, hcol⟩ := expDiff_flow_isGeodesicVariation g gi hC q w hw
  set Vb : ℝ → Point n × Point n := fun τ => (Φ τ) ((0 : Point n), b) with hVbdef
  have hVb0 : Vb 0 = ((0 : Point n), b) := by
    simp [hVbdef, hΦ0]
  -- Uniform operator-norm bound on the linearized generator over `S`.
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  ------------------------------------------------------------------------------------------------
  -- (E-jac) `(Y ·).2 = V_b` on `[0,1]` by linear Jacobi-ODE uniqueness along `E`.
  ------------------------------------------------------------------------------------------------
  -- Continuity of both Jacobi solutions on `[0,1]`.
  have hcontJ : ContinuousOn (fun t => (Y t).2) (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hJode t ht).continuousAt.continuousWithinAt
  have hcontVb : ContinuousOn Vb (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hcol ((0 : Point n), b) t ht).continuousWithinAt
  -- Lipschitz bound for the linearized (linear) generator `X ↦ DF(E t)·X` on all of the space.
  have hvLip : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      LipschitzOnWith Kb.toNNReal
        (fun X => fderiv ℝ (geodesicField g gi) (E t) X) (Set.univ) := by
    intro t ht
    have hEt : E t ∈ S := hmemE t (Set.Ico_subset_Icc_self ht)
    have hnorm : ‖fderiv ℝ (geodesicField g gi) (E t)‖ ≤ Kb := hKbbd (E t) hEt
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖fderiv ℝ (geodesicField g gi) (E t) (x - y)‖
        ≤ ‖fderiv ℝ (geodesicField g gi) (E t)‖ * ‖x - y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Kb * ‖x - y‖ := by gcongr
      _ = (Kb.toNNReal : ℝ) * ‖x - y‖ := by rw [Real.coe_toNNReal Kb hKb0]
  -- Jacobi ODE for `(Y ·).2` recast along `E` (via `E = (Y ·).1`), with `Ici`-derivatives.
  have hf'J : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun t => (Y t).2)
        (fderiv ℝ (geodesicField g gi) (E t) ((Y t).2)) (Set.Ici t) t := by
    intro t ht
    have hd := hJode t (Set.Ico_subset_Icc_self ht)
    rw [show (Y t).1 = E t from (hEP (Set.Ico_subset_Icc_self ht)).symm] at hd
    exact hd.hasDerivWithinAt
  -- Jacobi ODE for the flow column `V_b`, upgraded from `Icc`-within to `Ici`-within.
  have hg'J : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt Vb
        (fderiv ℝ (geodesicField g gi) (E t) (Vb t)) (Set.Ici t) t := by
    intro t ht
    have hd := hcol ((0 : Point n), b) t (Set.Ico_subset_Icc_self ht)
    refine hd.mono_of_mem_nhdsWithin ?_
    -- `Icc 0 1 ∈ 𝓝[Ici t] t` since `t < 1`.
    have h1 : Set.Iic (1 : ℝ) ∈ 𝓝[Set.Ici t] t :=
      nhdsWithin_le_nhds (Iic_mem_nhds (by linarith [ht.2]))
    have h2 : Set.Ici t ∈ 𝓝[Set.Ici t] t := self_mem_nhdsWithin
    have h3 : Set.Ici t ∩ Set.Iic 1 ∈ 𝓝[Set.Ici t] t := Filter.inter_mem h2 h1
    refine Filter.mem_of_superset h3 (fun x hx => ?_)
    obtain ⟨hxl, hxr⟩ := hx
    rw [Set.mem_Ici] at hxl
    rw [Set.mem_Iic] at hxr
    exact Set.mem_Icc.mpr ⟨le_trans (Set.mem_Ico.mp ht).1 hxl, hxr⟩
  -- Linear-ODE uniqueness: `(Y ·).2 = V_b` on `[0,1]`.
  have hJV : Set.EqOn (fun t => (Y t).2) Vb (Set.Icc (0 : ℝ) 1) :=
    ODE_solution_unique_of_mem_Icc_right
      (v := fun t X => fderiv ℝ (geodesicField g gi) (E t) X)
      (s := fun _ => (Set.univ : Set (Point n × Point n))) (K := Kb.toNNReal)
      hvLip hcontJ hf'J (fun t _ => Set.mem_univ _)
      hcontVb hg'J (fun t _ => Set.mem_univ _)
      (by rw [hVb0, hY0])
  ------------------------------------------------------------------------------------------------
  -- Assemble: project the Jacobi endpoint equality onto the position component.
  ------------------------------------------------------------------------------------------------
  have hJV1 : (Y 1).2 = Vb 1 := hJV (Set.right_mem_Icc.mpr zero_le_one)
  have hfd : fderiv ℝ (QIQTH.ExpMap.expMap g gi hC q) w =
      QIQTH.ExpMap.expJetPi.comp ((Φ 1).comp QIQTH.ExpMap.expJetIota) := hFD.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, expJetIota_apply, expJetPi_apply]
  rw [hJV1]

/-- **The hlink binder shape** — the first-jet endpoint identity over the seed window, per `(q,v,a,b)`.

    Given the doubled family `Y ·` (indexed by seed `s`) with the bridge's ODE / IC / geodesic-factor
    confinement data, plus the per-seed exp-admissibility `‖v + s·a‖ < expRho g gi hC q`, the position
    of the Jacobi endpoint equals the exp-map velocity-derivative:
        `(Y s 1).2.1 = fderiv ℝ (expMap g gi hC q) (v + s·a) b`.

    This is exactly the bridge's `hlink` binder (specialised to a fixed `(q,v,a,b)` and quantified over
    `s ∈ [-σ, σ]`), with the single extra admissibility input `hrad` that the caller supplies from its
    `hr_lt : r < expRho g gi hC q` and the window `σ` keeping `‖v+s·a‖ ≤ r`.  DERIVED by applying
    `doubled_endpoint_eq_expMap_fderiv` at `w := v + s·a`. -/
theorem hlink_of_confined_doubled_family (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q v a b : Point n) {C₀ σ : ℝ}
    {Y : ℝ → ℝ → (Point n × Point n) × (Point n × Point n)}
    (hY0 : ∀ s ∈ Set.Icc (-σ) σ, Y s 0 = ((q, v + s • a), ((0 : Point n), b)))
    (hYode : ∀ s ∈ Set.Icc (-σ) σ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (doubledField g gi (Y s τ)) τ)
    (hYconf : ∀ s ∈ Set.Icc (-σ) σ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(Y s τ).1 - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v + s • a‖)
    (hrad : ∀ s ∈ Set.Icc (-σ) σ, ‖v + s • a‖ < QIQTH.ExpMap.expRho g gi hC q) :
    ∀ s ∈ Set.Icc (-σ) σ,
      (Y s 1).2.1 = fderiv ℝ (QIQTH.ExpMap.expMap g gi hC q) (v + s • a) b := by
  intro s hs
  exact doubled_endpoint_eq_expMap_fderiv g gi hC q (v + s • a) b (hrad s hs)
    (hY0 s hs) (hYode s hs) (hYconf s hs)

end QIQTH.ExpMap
