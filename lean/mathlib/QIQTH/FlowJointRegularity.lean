/-
  FlowJointRegularity — J4-149: the JOINT base-point flow-regularity AUDIT + the first brick of the
  campaign against the last structural wall (the base-point `q`-regularity of the `.choose`-built
  uniform geodesic flow).  ONE brick of the a₁=R/6 campaign; **NOT a₁=R/6 itself**.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE AUDIT REPORT (the bankable intelligence — read before the FIREWALL).

  ### (1) Construction type of `uniformFlowExp`  —  **opaque `.choose` over an EXPOSED geodesic ODE**
      (CASE C in the campaign taxonomy, i.e. an ODE flow reached through `Classical.choose`, NOT a
      Picard iterate `T^[n]`, NOT a `tsum`/`HasSum` power series).

      Definition chain (`QIQTH/UniformFlowNondeg.lean`):
        `uniformFlowExp g gi hC hK q  :=  fun w => (uniformFlowTube g gi hC hK q w 1).1`
        `uniformFlowTube g gi hC hK q w  :=  (uniformFlow_tube_exists g gi hC hK q w).choose`
        `uniformFlow_tube_exists`  is proved by `by_cases (q ∈ K ∧ ‖w‖ ≤ ρ_K)`:
          • on-domain it hands back the Skolem curve of `uniformFlow_family`
            (`= geodesic_apriori_confinement_uniform … .choose_spec.2.choose_spec.2`),
          • off-domain the harmless total default `fun _ => (q, w)`.

      So the flow map is a `Classical.choose` of a phase-space curve `Y : ℝ → Point n × Point n`.  What
      IS exposed about that curve (`uniformFlowTube_spec`, for `q ∈ K`, `‖w‖ ≤ ρ_K`):
        • IC          `Y 0 = (q, w)`                                        (`…_spec_ic`)
        • the ODE     `∀ t ∈ (-2,2), HasDerivAt Y (geodesicField g gi (Y t)) t`  (`…_spec_ode`)
        • confinement `∀ t ∈ [0,1], ‖Y t − (q,0)‖ ≤ C₀·‖w‖`                (`…_spec_conf`).
      Hence the DEFINING INTEGRAL EQUATION is retrievable (nonlinear autonomous field `geodesicField`,
      IC `(q,w)`), and uniqueness is available (`expMap_eq_flow_endpoint`).  ⟹ CASE C: a stability
      (two-solution Grönwall) route to base-point continuity is available IN PRINCIPLE — but it needs a
      **uniform Lipschitz constant for `geodesicField` over the compact confinement region** and both
      tubes confined there; that is a genuine multi-brick chunk (the nonlinear analogue of
      `BasepointJetModulus.linODE_twopoint_diff_bound`), NOT landed here.

  ### (2) `BasepointJetModulus` modulus classification  —  **per-`v`, base-only (`q` vs `q'` at the
      SAME `v`); NOT genuinely joint `(q,v)` vs `(q',v')`.**  Verbatim target (`BasepointJetModulus.lean`
      header, `hunif`):
        `∀ ε>0 ∃ δ>0 ∀ q q'∈K, dist q q'<δ → ∀ v∈B̄(0,r),
            |‖fderiv²(exp_q) v‖ − ‖fderiv²(exp_{q'}) v‖| ≤ ε`.
      The two evaluation points share the SAME `v`; only the base moves.  The genuine joint continuity in
      `(q,v)` is assembled DOWNSTREAM (`BasepointSecondJet`) by welding this base modulus to the
      `v`-continuity.  And this modulus is about the SECOND JET operator norm, NOT the flow map itself.

  ### (3) Joint-in-`(q,v)` facts the tower exposes about `uniformFlowExp`  —  **only the second-jet
      operator-norm joint continuity on `K ×ˢ B̄` (`BasepointJetModulus.expMap_second_jet_joint_cont_of_*`),
      which is a fact about `fderiv²`, NOT about the point-value flow `uniformFlowExp g gi hC hK q v`.**
      There is NO `ContinuousOn`/`ContDiff` fact about the joint map `(q,v) ↦ uniformFlowExp … q v`
      anywhere (grep: every `ContDiffAt`/`fderiv` regularity of `uniformFlowExp` is in the VELOCITY slot
      at FIXED `q`, e.g. `contDiffAt2_uniformFlowExp … q hq v`).  This is exactly the gap the
      `InverseChartDisplacement` FIREWALL names: "the tower has NO base-point (`q`) regularity of the
      flow".

  ### (4) P/Q consumer classification  —  the live consumer of base-point flow regularity is
      **`hWmeas₀`** (`ChartWrapperConcrete.chartGauss_concrete_sub_plain_tendsto` and the sliver
      `InverseChartDisplacement.chartW0_l1_sub_plain_of_meas`), which needs the DIAGONAL / origin map
        `z ↦ W₀ z := uniformInverseChart g gi hC hK z 0`
      (the normal coordinate of the ORIGIN seen from base `z`) to be a.e.-strongly measurable — i.e. the
      consumer needs `z ↦ W z 0` (moving BASE `z`, FIXED velocity-slot argument `0`), NOT a full
      moving-base-and-velocity object.  `hWmeas₀` is CARRIED labelled everywhere it appears.

  ### (5) Geodesic-reversal feasibility (STEP-2 check)  —  **NOT feasible off the current tower.**  The
      only structural lemmas on `uniformFlowExp` are the ODE spec + the ApproximatesLinearOn / displacement
      jets; there is NO flow-group / time-reversal / `neg`/`symm` lemma (`uniformFlowTube` is a
      one-parameter `.choose` curve on `(-2,2)`, its `t ↦ -t` reversal is not identified with any tube of
      another seed).  So `W z 0 = −(D_v exp₀)(W 0 z)[W 0 z]` does NOT fall out; deriving it would first
      need the geodesic flow group law (absent).  Reported, not attempted.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## HONEST FIREWALL — what LANDS here (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`; NOT a₁=R/6).

    * `uniformFlowExp_antilipschitz_lower` — **the quantitative INVERSE-STABILITY (lower-Lipschitz) of the
      forward flow**, extracted directly from the tower's `uniformFlowExp_approximatesLinearOn`:
      on `ball 0 δ₀`, `‖x − y‖ ≤ (1−c)⁻¹·‖φ_q x − φ_q y‖` (single base `q`), `c < 1`.  This is the
      quantitative-inverse content the campaign flagged as derivable from the ApproximatesLinearOn jet.

    * `chart_joint_velocity_modulus` — **★ THE TRANSFER LEMMA.**  The joint modulus of the velocity
      coordinate reduces, via the antilipschitz above, to the base-flow difference at a FIXED velocity:
        `‖w − w'‖ ≤ (1−c)⁻¹·(‖φ_q w − φ_{q'} w'‖ + ‖φ_{q'} w' − φ_q w'‖)`.
      The first term is the endpoint separation you control; the second `‖φ_{q'} w' − φ_q w'‖` is exactly
      the base-point (`q` vs `q'`) difference of the forward flow at a FIXED velocity — the ONE residue
      the whole joint-regularity question reduces to (and the honest content of the bridge below).
      Valuable independent of the flow question.

    * `hWmeas₀_of_continuousOn` — **the conditional discharge of the carried consumer `hWmeas₀`.**  From
      the narrower, more reusable labelled bridge `hW0 : ContinuousOn (z ↦ W₀ z) S` (base-point continuity
      of the origin coordinate — per audit §4 this is precisely what the consumer needs, narrower than the
      whole flow residue) plus `MeasurableSet S`, we discharge
        `∀ τ, AEStronglyMeasurable (z ↦ gaussDdim τ (W₀ z)) (volume.restrict S)` — i.e. `hWmeas₀`.
      Route: `gaussDdim τ` continuous (product of 1-D heat kernels) ∘ `hW0` on `S`, then
      `ContinuousOn.aestronglyMeasurable` with the measurable set.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, never a conclusion):
    * `hW0 : ContinuousOn (z ↦ uniformInverseChart g gi hC hK z 0) S` — the base-point continuity of the
      origin coordinate.  A GENUINE geometric fact of the honest chart (true), but NOT exposed by the
      `.choose`-built tower (audit §3).  Carried as the focused API-gap bridge.
    * The forward-flow base difference `‖φ_{q'} w' − φ_q w'‖ → 0` (residue isolated by the transfer
      lemma).  Recommended next brick: derive it via the nonlinear two-solution Grönwall over the compact
      confinement region (CASE C, audit §1) — the geodesic analogue of `linODE_twopoint_diff_bound`.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.UniformChartRadius

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatKernelA1 QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### Brick A — the quantitative inverse-stability (lower-Lipschitz) of the forward flow. -/

/-- **Brick A — `uniformFlowExp_antilipschitz_lower`.**  Extracts the quantitative INVERSE stability of
    the forward flow `φ_q = uniformFlowExp g gi hC hK q` from the tower's `ApproximatesLinearOn` jet
    (`uniformFlowExp_approximatesLinearOn`, constant `c < 1`, source `ball 0 δ₀`).  On the ball, for a
    single base `q`,
        `‖x − y‖ ≤ (1 − c)⁻¹ · ‖φ_q x − φ_q y‖`.
    Proof: with `f' = id`, `ApproximatesLinearOn` gives `‖φ_q x − φ_q y − (x−y)‖ ≤ c‖x−y‖`; the reverse
    triangle inequality turns this into the lower bound `(1−c)‖x−y‖ ≤ ‖φ_q x − φ_q y‖`. -/
theorem uniformFlowExp_antilipschitz_lower (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ q ∈ K,
      ∀ x ∈ Metric.ball (0 : Point n) δ₀, ∀ y ∈ Metric.ball (0 : Point n) δ₀,
        ‖x - y‖ ≤ (1 - c)⁻¹ * ‖uniformFlowExp g gi hC hK q x - uniformFlowExp g gi hC hK q y‖ := by
  obtain ⟨δ₀, hδ₀, c, hc1, hAL⟩ := uniformFlowExp_approximatesLinearOn g gi hC hK
  refine ⟨δ₀, hδ₀, (c : ℝ), c.2, hc1, ?_⟩
  intro q hq x hx y hy
  have hc0 : (0 : ℝ) < 1 - (c : ℝ) := by linarith
  -- ApproximatesLinearOn at `(x,y)`, with `f' = id` simplified.
  have hA := hAL q hq x hx y hy
  have hrefl : (ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n) (x - y) = x - y := by
    simp
  rw [hrefl] at hA
  set a : Point n := uniformFlowExp g gi hC hK q x - uniformFlowExp g gi hC hK q y with ha
  -- reverse triangle: `‖x−y‖ − ‖a‖ ≤ ‖(x−y) − a‖ = ‖a − (x−y)‖ ≤ c‖x−y‖`.
  have h1 : ‖x - y‖ - ‖a‖ ≤ ‖(x - y) - a‖ := norm_sub_norm_le _ _
  have h2 : ‖(x - y) - a‖ = ‖a - (x - y)‖ := norm_sub_rev _ _
  have hkey : (1 - (c : ℝ)) * ‖x - y‖ ≤ ‖a‖ := by
    rw [sub_mul, one_mul]
    have := hA           -- `‖a − (x−y)‖ ≤ c * ‖x − y‖`
    rw [← h2] at this
    linarith [h1, this]
  rw [le_inv_mul_iff₀ hc0]
  linarith [hkey]

/-! ### Brick B (★) — the transfer lemma: joint velocity modulus ⟶ base-flow difference. -/

/-- **★ Brick B — `chart_joint_velocity_modulus` (THE TRANSFER LEMMA).**  The joint modulus of the
    velocity coordinate `w` reduces, via the inverse-stability of Brick A, to the base-point difference
    of the forward flow at a FIXED velocity.  For `q, q' ∈ K` and `w, w' ∈ ball 0 δ₀`,
        `‖w − w'‖ ≤ C_inv · (‖φ_q w − φ_{q'} w'‖ + ‖φ_{q'} w' − φ_q w'‖)`,   `C_inv := (1−c)⁻¹ ≥ 0`.
    The first term is the ENDPOINT separation (data one controls); the second `‖φ_{q'} w' − φ_q w'‖` is
    the pure BASE-point (`q` vs `q'`) flow difference at fixed velocity `w'` — the sole residue the joint
    regularity question reduces to (isolated here; its `→0` control is the recommended next brick,
    audit §1/CASE C). -/
theorem chart_joint_velocity_modulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∃ C_inv : ℝ, 0 ≤ C_inv ∧ ∀ q ∈ K, ∀ q' ∈ K,
      ∀ w ∈ Metric.ball (0 : Point n) δ₀, ∀ w' ∈ Metric.ball (0 : Point n) δ₀,
        ‖w - w'‖ ≤ C_inv *
          (‖uniformFlowExp g gi hC hK q w - uniformFlowExp g gi hC hK q' w'‖
            + ‖uniformFlowExp g gi hC hK q' w' - uniformFlowExp g gi hC hK q w'‖) := by
  obtain ⟨δ₀, hδ₀, c, hc0, hc1, hlow⟩ := uniformFlowExp_antilipschitz_lower g gi hC hK
  have hCinv0 : (0 : ℝ) ≤ (1 - c)⁻¹ := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  refine ⟨δ₀, hδ₀, (1 - c)⁻¹, hCinv0, ?_⟩
  intro q hq q' hq' w hw w' hw'
  -- inverse stability at base `q`, evaluation points `w`, `w'`.
  have hstab := hlow q hq w hw w' hw'
  -- split the same-base endpoint difference through `φ_{q'} w'`.
  set A : Point n := uniformFlowExp g gi hC hK q w with hAdef
  set B : Point n := uniformFlowExp g gi hC hK q w' with hBdef
  set C : Point n := uniformFlowExp g gi hC hK q' w' with hCdef
  have hsplit : ‖A - B‖ ≤ ‖A - C‖ + ‖C - B‖ := by
    have he : A - B = (A - C) + (C - B) := by abel
    calc ‖A - B‖ = ‖(A - C) + (C - B)‖ := by rw [he]
      _ ≤ ‖A - C‖ + ‖C - B‖ := norm_add_le _ _
  -- `‖C − B‖ = ‖φ_{q'} w' − φ_q w'‖`  (the base-flow difference at fixed velocity `w'`).
  calc ‖w - w'‖ ≤ (1 - c)⁻¹ * ‖A - B‖ := hstab
    _ ≤ (1 - c)⁻¹ * (‖A - C‖ + ‖C - B‖) := by
        exact mul_le_mul_of_nonneg_left hsplit hCinv0

/-! ### Brick C — continuity of the Gaussian argument and the `hWmeas₀` discharge. -/

/-- `heatKernel1D t` is continuous (re-derived locally to avoid a heavy import). -/
theorem heatKernel1D_cont (t : ℝ) : Continuous (fun y : ℝ => heatKernel1D t y) := by
  simp only [heatKernel1D]; fun_prop

/-- `gaussDdim τ` is continuous in the spatial variable — a finite product of 1-D heat kernels of the
    coordinate projections. -/
theorem gaussDdim_cont (t : ℝ) : Continuous (fun x : Point n => gaussDdim t x) := by
  simp only [gaussDdim]
  exact continuous_finsetProd _ (fun k _ => (heatKernel1D_cont t).comp (continuous_apply k))

/-- **★ Brick C — `hWmeas₀_of_continuousOn` (conditional discharge of the carried `hWmeas₀`).**  Given
    the narrower, reusable base-point-continuity bridge `hW0 : ContinuousOn (z ↦ W₀ z) S` for the origin
    coordinate `W₀ z = uniformInverseChart g gi hC hK z 0` (per audit §4 exactly what the consumer needs),
    and `MeasurableSet S`, the consumer input `hWmeas₀` holds:
        `∀ τ, AEStronglyMeasurable (z ↦ gaussDdim τ (W₀ z)) (volume.restrict S)`.
    Route: `gaussDdim τ` continuous ∘ `hW0` on `S`, then `ContinuousOn.aestronglyMeasurable`. -/
theorem hWmeas₀_of_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {S : Set (Point n)} (hS : MeasurableSet S)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) S) :
    ∀ τ : ℝ, AEStronglyMeasurable
      (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) (volume.restrict S) := by
  intro τ
  have hcomp : ContinuousOn
      (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) S :=
    (gaussDdim_cont τ).comp_continuousOn hW0
  exact hcomp.aestronglyMeasurable hS

end QIQTH.HeatResidualBound
