/-
  GeodesicVariationCompact — J4-725, J3 BRICK 3: the compact-hypothesis CONSUMER WIRE for the
  first-order smooth-dependence-on-IC existence theorem.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md §5.  `GeodesicSmoothDep.lean` proved
      `geodesicVariation_exists_uncond`
  — `HasDerivAt (fun s => Y s t) (V t) 0` — but it CARRIES four regularity hypotheses as explicit
  numbers:
      `hbound2 : ∀ x ∈ S, ‖∂²F x‖ ≤ M₂`     (the field's C² sup bound),
      `hLip    : LipschitzOnWith K₀ F S`     (the field Lipschitz on `S`),
      `hKb     : ∀ τ, ‖DF(Y 0 τ)‖ ≤ K`       (the Jacobi-coefficient bound along the base geodesic),
      `hK0     : 0 ≤ K`.
  `GeodesicTaylorCompact.lean` (banked) already produces `hbound2`'s constant BY COMPACTNESS
  (`geodesicField_snd_fderiv_bddOn_compact`).  This file supplies the remaining two compactness
  producers and wires all four away:

  * `geodesicField_fst_fderiv_bddOn_compact` — brick engine: `F = geodesicField g gi` is `C^∞`, so
    its FIRST Fréchet derivative `DF = fderiv ℝ F` is continuous, hence bounded on a compact `S`
    (constant produced by compactness).  This single bound discharges BOTH `hLip` (via the mean-value
    inequality) AND `hKb` (since the base trajectory `Y 0 τ ∈ S`).

  * `geodesicField_lipschitzOnWith_compact` — brick (1): on a convex compact `S`, `F` itself is
    Lipschitz there (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`, the mean-value inequality, using
    the compactness-derived `‖DF‖` sup).  The Lipschitz constant is EXISTENTIALLY produced — NOT a
    carried number.  (Mirrors `geodesicField_fderiv_lipschitzOnWith`, but for `F` not `DF`; the same
    banked pattern as `ExpMap`'s `geodesicField_uniform_C1_remainder` uses at line 4082.)

  * `geodesicVariation_exists_uncond_compact` — ★ THE CONSUMER WIRE: the version of
    `geodesicVariation_exists_uncond` whose `hbound2`, `hLip`, `hKb`, `hK0` are ALL produced by
    compactness of `S`.  It carries ONLY the honest structural/geometric data: `S` convex + compact,
    the geodesic ODE `hYode`, the Jacobi solution ODE/IC `hVode`/`hV0`/`hIC`, and the flow tube
    containment `hmem : Y s τ ∈ S`.  Of these, `hYode`/`hVode`/`hV0`/`hIC` are the SUPPLIED ODE
    solution (structural, not regularity), and `hmem` is the genuine short-time Grönwall a-priori
    carry (not produced here — the flow does not automatically stay in a fixed ball).

  * `geodesicVariation_exists_uncond_closedBall` — cp466 witness: instantiates the convex-compact
    region at a closed ball `Metric.closedBall c r`, matching the curved-witness closedBall pattern.

  All axiom-clean (std-3), no `sorry`, no new axioms.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — it removes the carried `{hbound2, hLip,
  hKb, hK0}` from the first-order IC-derivative existence, leaving `{hYode, hVode, hV0, hIC, hmem}`.
  It is NOT the heat-kernel coefficient `a₁ = R/6` (which remains a labelled carrier); it does NOT
  build the second-order Jacobi equation (L2), Raychaudhuri (L3), the small-window MVI contraction,
  or numerical `G`.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicSmoothDep
import QIQTH.GeodesicTaylorCompact

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

variable {n : ℕ}

/-- **The geodesic field's first Fréchet derivative is bounded on a compact set (constant produced by
    compactness).**  `F = geodesicField g gi` is `C^∞`, so `DF = fderiv ℝ F` is continuous
    (`ContDiff.continuous_fderiv`); on a compact `S` its norm attains a finite bound
    (`IsCompact.bddAbove_image`).  This single bound is shared by brick (1) (`hLip`, via the
    mean-value inequality) and the consumer wire's `hKb` (since the base trajectory stays in `S`). -/
theorem geodesicField_fst_fderiv_bddOn_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hcomp : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖fderiv ℝ (geodesicField g gi) x‖ ≤ M := by
  set F := geodesicField g gi with hFdef
  have hdFcont : Continuous (fderiv ℝ F) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hcomp.bddAbove_image hdFcont.norm.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- **J3 brick (1) — `F = geodesicField g gi` is Lipschitz on a convex compact set, constant obtained
    by compactness.**  `F` is `C^∞`, so `DF = fderiv ℝ F` is continuous, hence bounded on the compact
    `S` (`geodesicField_fst_fderiv_bddOn_compact`); the mean-value inequality
    (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`, using convexity of `S`) then makes `F` Lipschitz on
    `S` with the compactness-derived constant.

    The Lipschitz constant is EXISTENTIALLY produced — NOT a carried number.  This is exactly the
    `hLip` hypothesis carried by `geodesicVariation_exists_uncond`. -/
theorem geodesicField_lipschitzOnWith_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) (hcomp : IsCompact S) :
    ∃ K₀ : NNReal, LipschitzOnWith K₀ (geodesicField g gi) S := by
  set F := geodesicField g gi with hFdef
  have hFdiff : Differentiable ℝ F := (contDiff_geodesicField g gi hC).differentiable (by simp)
  obtain ⟨M, hM0, hMbound⟩ := geodesicField_fst_fderiv_bddOn_compact g gi hC hcomp
  refine ⟨Real.toNNReal M, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hFdiff x) (fun x hx => ?_) hconv
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM0]
  exact hMbound x hx

/-- **★ J3 brick (3), THE CONSUMER WIRE — first-order smooth-dependence-on-IC on a convex compact
    region, all regularity hypotheses produced by compactness.**  The version of
    `geodesicVariation_exists_uncond` whose carried regularity numbers `{hbound2, hLip, hKb, hK0}`
    are ALL produced from `IsCompact S`:

    * `hbound2` (field C² sup bound) — `geodesicField_snd_fderiv_bddOn_compact` (banked);
    * `hLip` (field Lipschitz on `S`) — `geodesicField_lipschitzOnWith_compact` (brick (1) above);
    * `hKb`/`hK0` (Jacobi-coefficient bound along `Y 0`) — `geodesicField_fst_fderiv_bddOn_compact`
      combined with `hmem 0` (the base trajectory `Y 0 τ ∈ S`).

    What remains CARRIED is only the honest data: `S` convex + compact, the geodesic ODE `hYode`, the
    Jacobi solution ODE `hVode` with IC `hV0`, the linear IC perturbation `hIC`, and the flow tube
    containment `hmem`.  Of these, `hYode`/`hVode`/`hV0`/`hIC` are the SUPPLIED ODE solution
    (structural), and `hmem` is the genuine short-time Grönwall a-priori carry (the flow does not
    automatically stay in a fixed ball — that is the next geometric brick).

    HONEST: J3 regularity only.  It does NOT build the second-order Jacobi equation, the small-window
    MVI contraction, or `a₁ = R/6`. -/
theorem geodesicVariation_exists_uncond_compact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    {S : Set (Point n × Point n)} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hconv : Convex ℝ S) (hcomp : IsCompact S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S) :
    HasDerivAt (fun s => Y s t) (V t) 0 := by
  -- `hbound2` — field C² sup bound, produced by compactness (banked engine).
  obtain ⟨M₂, _hM₂0, hbound2⟩ := geodesicField_snd_fderiv_bddOn_compact g gi hC hcomp
  -- `hLip` — field Lipschitz on `S`, produced by compactness (brick (1)).
  obtain ⟨K₀, hLip⟩ := geodesicField_lipschitzOnWith_compact g gi hC hconv hcomp
  -- `hKb`/`hK0` — Jacobi-coefficient bound, produced by compactness + base-trajectory containment.
  obtain ⟨K, hK0, hKbnd⟩ := geodesicField_fst_fderiv_bddOn_compact g gi hC hcomp
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K :=
    fun τ hτ => hKbnd (Y 0 τ) (hmem 0 τ hτ)
  exact geodesicVariation_exists_uncond g gi hC hK0 ht hconv hbound2 hLip
    hYode hVode hV0 hIC hKb hmem

/-- **cp466 witness — the consumer wire at a closed-ball region.**  Instantiates
    `geodesicVariation_exists_uncond_compact` at the convex compact `Metric.closedBall c r` in the
    finite-dimensional state space `Point n × Point n`, matching the curved-witness closedBall
    pattern.  All regularity is produced by compactness of the ball; the carried data is the geodesic
    ODE, the supplied Jacobi solution, and the flow tube containment in the ball. -/
theorem geodesicVariation_exists_uncond_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {w : Point n}
    (c : Point n × Point n) (r : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (Y 0 τ) (V τ)) τ)
    (hV0 : V 0 = ((0, w) : Point n × Point n))
    (hIC : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ((0, w) : Point n × Point n))
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ Metric.closedBall c r) :
    HasDerivAt (fun s => Y s t) (V t) 0 :=
  geodesicVariation_exists_uncond_compact g gi hC ht (convex_closedBall c r)
    (isCompact_closedBall c r) hYode hVode hV0 hIC hmem

end QIQTH.ExpMap
