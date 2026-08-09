/-
  HbaseJ2Gronwall — J4-482: the two-point GRÖNWALL on the `.2`-component ODE of the second variation —
  the wall-felling step toward the base-slot second-jet modulus `hbaseJ2` and THE CONVERGENT WALL of
  the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-481).  `SecondVariationModulus` (J4-481) exposed the endpoint second-variation
  operator (`uniformFlowExp_secondVar_spec`) and landed the `.2`-component INHOMOGENEOUS scalar-Jacobi
  ODE (`secondVar_snd_hasDerivAt`):
        `(V·).2' = DF(geo)(Ybase)·(V·).2  +  D²F(geo)(Ybase)·(V·).1·Jbase`,
  the second summand a genuine `δ·b`-bilinear curvature SOURCE (driven by the base-velocity slot `(V·).1`
  ∝ `δ` and the base Jacobi field `Jbase` ∝ `b`).  This file builds the TWO-POINT Grönwall on that
  `.2`-component ODE between two nearby bases `q, q'` — the endpoint difference bound the base-slot
  modulus `hbaseJ2` consumes (exactly as `jacobi_twopoint_diff_bound` fed the first-jet `hbaseJ`, one
  order up).

  ── THE NON-OBVIOUS FINDING (J4-481, honoured here).  A naive FULL-doubled-norm Grönwall FAILS
  `hbaseJ2`: the full norm `‖Vf δ 1‖` is dominated by the `.1`-slot (∝ `δ`, independent of `b`), losing
  the `∝‖b‖` factor the double operator norm `‖B₂ − B₂'‖ = sup_{‖δ‖,‖b‖≤1} ‖((B₂−B₂')δ)b‖` requires.
  The FIX is precisely the `.2`-component inhomogeneous ODE, whose SOURCE carries the `δ·b` bilinearity.
  This brick's Grönwall is on the `.2`-component — not the full doubled field.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `clm2_apply_telescope` — the pure-CLM trilinear telescope: for `T T' : E →L (E →L E)` and
      `u u' w w' : E`,
        `‖T u w − T' u' w'‖ ≤ ‖T−T'‖·‖u‖·‖w‖ + ‖T'‖·‖u−u'‖·‖w‖ + ‖T'‖·‖u'‖·‖w−w'‖`.
      This is the exact decomposition that separates the curvature SOURCE `D²F·(V·).1·Jbase` between two
      bases into (coefficient) + (`.1`-slot) + (base-Jacobi) parts.

    * `secondVar_fst_hasDerivAt` — the `.1`-component HOMOGENEOUS Jacobi ODE (companion to J4-481's
      `secondVar_snd_hasDerivAt`).  The base-velocity slot `t ↦ (V t).1` solves the pure first-variation
      Jacobi ODE `(V·).1' = DF(geo)(Ybase)·(V·).1` — decoupled from the `.2`-slot — via
      `doubledField_fderiv_fst_apply`.  Supplies the `.1`-slot bounds/separation the source telescope needs.

    * `geodesicField_fderiv2_diff_bound` — the **M₃ compactness / D²F two-point separation.**  On a convex
      compact `S`, a single `M₃ ≥ 0` (sup of the THIRD derivative `‖D³F‖`) gives
        `‖D²F x − D²F y‖ ≤ M₃·‖x − y‖`   for `x, y ∈ S`,
      the C³ MVT (`Convex.norm_image_sub_le_of_norm_fderiv_le` on `D²F = fderiv (fderiv geodesicField)`,
      `D³F` sup bounded by compactness of `contDiff_fderiv2_geodesicField`) — the source coefficient
      separation, one order up from the M₂ pattern.

    * `linODE_growth_bound` — the inhomogeneous single-solution growth bound (zero seed): `X' = A·X + b`,
      `‖A‖ ≤ K`, `‖b‖ ≤ Bsrc`, `X 0 = 0` ⟹ `‖X t‖ ≤ Bsrc·exp K`.  Bounds the `.2`-slot field `(V·).2`
      (which is NOT a homogeneous Jacobi field) — the `Xb` hypothesis of the two-point engine.

    * `secondVar_snd_twopoint_diff_bound` — **★ THE GRÖNWALL (the wall-felling step).**  The two-point
      endpoint bound on the `.2`-component ODE between two base doubled curves (same `.2`-seed):
        `‖S₁ t − S₂ t‖ ≤ (Dc·Xb + (DD·Pb·Jbb + M₂·DP·Jbb + M₂·Pb·DJb))·exp Kf`,
      `S_i = (V_i·).2`, via `BasepointJetModulus.linODE_twopoint_diff_bound` on the INHOMOGENEOUS
      `.2`-component ODE with the SOURCE separation supplied by `clm2_apply_telescope`.  The three source
      terms are the (coefficient `DD` via M₃) + (`.1`-slot separation `DP`) + (base-Jacobi separation
      `DJb`) parts — each carrying the geometric two-point smallness `∝‖q−q'‖` a full-doubled-norm bound
      would lose.  NOT `a₁ = R/6`.

  ⚠ WHAT REMAINS for full `hbaseJ2` / `hFwd2` / the wall (future J4-483; NOT here):
    * THE CONCRETE WIRING: instantiate `secondVar_snd_twopoint_diff_bound` at the two exposures
      `uniformFlowExp_secondVar_spec q`, `… q'`, discharging its hypotheses from the banked tube
      separation (`uniformTube_twopoint_diff_bound`), the M₂/M₃ bounds, and `jacobi_twopoint_diff_bound`
      / `jacobi_growth_bound` on the `.1`-slot (`secondVar_fst_hasDerivAt`) and the base Jacobi field.
    * THE BRIDGE + DOUBLE opNORM: `fderiv²(uniformFlowExp q) v δ b = (Vf_q δ 1).2.1` (the `apply b`
      composition, from the C² flow) ⊕ the double `opNorm_le_bound` over `(δ,b)` ⟹ `hbaseJ2`.
    * THE WELD: the `z₀`-anchored triangle (the J4-435 pattern one order up) welding VELOCITY
      (`Flow3Regularity.forward2_velocitySlot`) + BASE (`hbaseJ2`) into `hFwd2` ⟹
      `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` UNCONDITIONAL ⟹ THE CONVERGENT WALL FALLS.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SecondVariationModulus
import QIQTH.UniformFlowHessianDiag
import QIQTH.ExpMapContDiff2

open Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open scoped Topology NNReal

namespace QIQTH.HbaseJ2Gronwall

variable {n : ℕ}

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 6

/-! ###############################################################################
    ### ★ THE TRILINEAR TELESCOPE — pure-CLM source separation.
    ############################################################################### -/

/-- **`clm2_apply_telescope` — the pure-CLM trilinear telescope.**  For `T T' : E →L[ℝ] (E →L[ℝ] E)`
    and `u u' w w' : E`,
      `‖T u w − T' u' w'‖ ≤ ‖T − T'‖·‖u‖·‖w‖ + ‖T'‖·‖u − u'‖·‖w‖ + ‖T'‖·‖u'‖·‖w − w'‖`.
    The exact three-way decomposition (coefficient / middle-slot / right-slot) that separates the
    second-variation curvature source `D²F·(V·).1·Jbase` between two bases.  NOT `a₁ = R/6`. -/
theorem clm2_apply_telescope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T T' : E →L[ℝ] (E →L[ℝ] E)) (u u' w w' : E) :
    ‖T u w - T' u' w'‖
      ≤ ‖T - T'‖ * ‖u‖ * ‖w‖ + ‖T'‖ * ‖u - u'‖ * ‖w‖ + ‖T'‖ * ‖u'‖ * ‖w - w'‖ := by
  have hsplit : T u w - T' u' w'
      = ((T - T') u) w + (T' (u - u')) w + T' u' (w - w') := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  have hA : ‖((T - T') u) w‖ ≤ ‖T - T'‖ * ‖u‖ * ‖w‖ := by
    calc ‖((T - T') u) w‖
        ≤ ‖(T - T') u‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖T - T'‖ * ‖u‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖T - T'‖ * ‖u‖ * ‖w‖ := by ring
  have hB : ‖(T' (u - u')) w‖ ≤ ‖T'‖ * ‖u - u'‖ * ‖w‖ := by
    calc ‖(T' (u - u')) w‖
        ≤ ‖T' (u - u')‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖T'‖ * ‖u - u'‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖T'‖ * ‖u - u'‖ * ‖w‖ := by ring
  have hCc : ‖T' u' (w - w')‖ ≤ ‖T'‖ * ‖u'‖ * ‖w - w'‖ := by
    calc ‖T' u' (w - w')‖
        ≤ ‖T' u'‖ * ‖w - w'‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖T'‖ * ‖u'‖) * ‖w - w'‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖T'‖ * ‖u'‖ * ‖w - w'‖ := by ring
  rw [hsplit]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hCc)

/-! ###############################################################################
    ### ★ THE `.1`-COMPONENT ODE — the pure first-variation Jacobi ODE.
    ############################################################################### -/

/-- **`secondVar_fst_hasDerivAt` — the `.1`-component homogeneous Jacobi ODE.**  If a doubled
    second-variation field `V` solves the doubled-linearized ODE `V' = DF(doubledField)(Ybase,Jbase)·V`
    along a base doubled curve `(Ybase, Jbase)`, then its base-velocity slot `t ↦ (V t).1` solves the
    pure (homogeneous) first-variation Jacobi ODE
        `(V·).1' = DF(geodesicField)(Ybase)·(V·).1`,
    decoupled from the `.2`-slot.  Companion to J4-481's `secondVar_snd_hasDerivAt`, via
    `doubledField_fderiv_fst_apply`.  NOT `a₁ = R/6`. -/
theorem secondVar_fst_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {V : ℝ → (Point n × Point n) × (Point n × Point n)} {Ybase Jbase : ℝ → Point n × Point n} {τ : ℝ}
    (hV : HasDerivAt V
      (fderiv ℝ (doubledField g gi)
        ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)) τ) :
    HasDerivAt (fun t => (V t).1)
      (fderiv ℝ (geodesicField g gi) (Ybase τ) ((V τ).1)) τ := by
  have hfst : HasDerivAt (fun t => (V t).1)
      ((fderiv ℝ (doubledField g gi)
        ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)).1) τ := by
    have h := (ContinuousLinearMap.fst ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ hV
    simpa using h
  rwa [doubledField_fderiv_fst_apply g gi hC
    ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)] at hfst

/-! ###############################################################################
    ### ★ THE M₃ SEPARATION — the D²F two-point coefficient separation.
    ############################################################################### -/

/-- **`geodesicField_fderiv2_diff_bound` — the M₃ compactness / D²F two-point separation.**  On a
    convex compact `S ⊆ Point n × Point n`, there is a single `M₃ ≥ 0` (the sup of the THIRD Fréchet
    derivative `‖D³F‖` over `S`) with
        `‖D²F x − D²F y‖ ≤ M₃·‖x − y‖`   for all `x, y ∈ S`,   `D²F = fderiv ℝ (fderiv ℝ (geodesicField g gi))`.
    The C³ mean-value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le` on `D²F`, whose Fréchet
    derivative is `D³F`, sup-bounded by compactness via `contDiff_fderiv2_geodesicField`) — the source
    coefficient separation, one order up from the M₂ pattern.  NOT `a₁ = R/6`. -/
theorem geodesicField_fderiv2_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hScompact : IsCompact S) (hSconv : Convex ℝ S) :
    ∃ M₃ : ℝ, 0 ≤ M₃ ∧ ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) y‖ ≤ M₃ * ‖x - y‖ := by
  have hdiffglob : Differentiable ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    (contDiff_fderiv2_geodesicField g gi hC).differentiable (by simp)
  obtain ⟨M₃, hM₃0, hM₃⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z‖ ≤ Kb := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨0, le_refl _, fun z hz => by rw [hSe] at hz; exact absurd hz (by simp)⟩
    · have hcontr : Continuous
          (fun z => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) z‖) :=
        ((contDiff_fderiv2_geodesicField g gi hC).continuous_fderiv (by simp)).norm
      obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
      exact ⟨‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖,
        norm_nonneg _, fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  refine ⟨M₃, hM₃0, fun x hx y hy => ?_⟩
  exact hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fderiv ℝ (fderiv ℝ (geodesicField g gi))) (fun z _ => hdiffglob z) hM₃ hy hx

/-! ###############################################################################
    ### ★ THE INHOMOGENEOUS GROWTH BOUND — bounding the `.2`-slot field.
    ############################################################################### -/

/-- **`linODE_growth_bound` — inhomogeneous single-solution growth (zero seed).**  A solution `X` of
    `X' = A·X + b` on `[0,1]` with `X 0 = 0`, `‖A t‖ ≤ K`, `‖b t‖ ≤ Bsrc`, grows at most as
        `‖X t‖ ≤ Bsrc·exp K`.
    Specialization of `linODE_twopoint_diff_bound` against the zero solution (`X₂ ≡ 0`, `A₂ = A`,
    `b₂ ≡ 0`).  Bounds the `.2`-slot field `(V·).2` (NOT a homogeneous Jacobi field, so
    `jacobi_growth_bound` does not apply) — the `Xb` hypothesis of the two-point engine.  NOT
    `a₁ = R/6`. -/
theorem linODE_growth_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → (E →L[ℝ] E)} {X b : ℝ → E} {K Bsrc : ℝ} (hK0 : 0 ≤ K)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X (A t (X t) + b t) t)
    (h0 : X 0 = 0)
    (hKb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ K)
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖b t‖ ≤ Bsrc) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖X t‖ ≤ Bsrc * Real.exp K := by
  have hbnd := linODE_twopoint_diff_bound (E := E)
    (A₁ := A) (A₂ := A) (X₁ := X) (X₂ := fun _ => 0) (b₁ := b) (b₂ := fun _ => 0)
    (K := K) (Dcoef := 0) (Xb := 0) (Dsrc := Bsrc) hK0 hX
    (fun t _ => by
      have hz : A t (0 : E) + (0 : E) = 0 := by rw [map_zero, add_zero]
      rw [hz]; exact hasDerivAt_const t (0 : E))
    (by rw [h0])
    hKb
    (fun t _ => by simp)
    (fun t _ => by simp)
    (fun t ht => by simpa using hbd t ht)
  intro t ht
  simpa using hbnd t ht

/-! ###############################################################################
    ### ★ THE GRÖNWALL — the two-point endpoint bound on the `.2`-component ODE.
    ############################################################################### -/

/-- **★ `secondVar_snd_twopoint_diff_bound` — THE GRÖNWALL (the wall-felling step).**  For two base
    doubled curves `(Y₁, ·)`, `(Y₂, ·)` (bases `q, q'`), let `S₁ = (V₁·).2`, `S₂ = (V₂·).2` be the
    `.2`-component fields solving the INHOMOGENEOUS scalar-Jacobi ODE (J4-481's `secondVar_snd_hasDerivAt`)
        `Sᵢ' = DF(geo)(Yᵢ)·Sᵢ + D²F(geo)(Yᵢ)·Pᵢ·Jbᵢ`,   `Pᵢ = (Vᵢ·).1`, `Jbᵢ` = the base Jacobi field,
    with the SAME `.2`-seed `S₁ 0 = S₂ 0`.  Given the field bound `‖DF(Y₁)‖ ≤ Kf`, the coefficient
    separation `‖DF(Y₁) − DF(Y₂)‖ ≤ Dc`, the `.2`-slot bound `‖S₂‖ ≤ Xb`, the D²F bound `‖D²F(Y₂)‖ ≤ M₂`
    and separation `‖D²F(Y₁) − D²F(Y₂)‖ ≤ DD`, the `.1`-slot bounds `‖P₁‖,‖P₂‖ ≤ Pb`, the base-Jacobi
    bound `‖Jb₁‖ ≤ Jbb`, and the two-point separations `‖P₁ − P₂‖ ≤ DP`, `‖Jb₁ − Jb₂‖ ≤ DJb`, then
        `‖S₁ t − S₂ t‖ ≤ (Dc·Xb + (DD·Pb·Jbb + M₂·DP·Jbb + M₂·Pb·DJb))·exp Kf`   on `[0,1]`.
    The source separation `‖b₁ − b₂‖ ≤ DD·Pb·Jbb + M₂·DP·Jbb + M₂·Pb·DJb` is `clm2_apply_telescope`
    (coefficient + `.1`-slot + base-Jacobi parts, each carrying the `∝‖q−q'‖` smallness a
    full-doubled-norm bound would lose); `linODE_twopoint_diff_bound` on the `.2`-component ODE closes it.
    NOT `a₁ = R/6`. -/
theorem secondVar_snd_twopoint_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ P₁ P₂ Jb₁ Jb₂ S₁ S₂ : ℝ → Point n × Point n}
    {Kf Dc Xb M₂ DD Pb Jbb DP DJb : ℝ} (hKf0 : 0 ≤ Kf)
    (hS1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt S₁
      (fderiv ℝ (geodesicField g gi) (Y₁ τ) (S₁ τ)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ) (P₁ τ) (Jb₁ τ)) τ)
    (hS2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt S₂
      (fderiv ℝ (geodesicField g gi) (Y₂ τ) (S₂ τ)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (P₂ τ) (Jb₂ τ)) τ)
    (h0 : S₁ 0 = S₂ 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y₁ τ)‖ ≤ Kf)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y₁ τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Dc)
    (hXb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖S₂ τ‖ ≤ Xb)
    (hD2Y2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ ≤ M₂)
    (hD2sep : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
        - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ ≤ DD)
    (hP1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖P₁ τ‖ ≤ Pb)
    (hP2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖P₂ τ‖ ≤ Pb)
    (hJ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jb₁ τ‖ ≤ Jbb)
    (hPd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖P₁ τ - P₂ τ‖ ≤ DP)
    (hJd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jb₁ τ - Jb₂ τ‖ ≤ DJb) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖S₁ t - S₂ t‖
      ≤ (Dc * Xb + (DD * Pb * Jbb + M₂ * DP * Jbb + M₂ * Pb * DJb)) * Real.exp Kf := by
  set Dsrc : ℝ := DD * Pb * Jbb + M₂ * DP * Jbb + M₂ * Pb * DJb with hDsrcdef
  -- nonnegativity of the constants (from `0 ≤ ‖·‖ ≤ bound`).
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hD2Y2 0 h0mem)
  have hDD0 : 0 ≤ DD := le_trans (norm_nonneg _) (hD2sep 0 h0mem)
  have hPb0 : 0 ≤ Pb := le_trans (norm_nonneg _) (hP1 0 h0mem)
  have hJbb0 : 0 ≤ Jbb := le_trans (norm_nonneg _) (hJ1 0 h0mem)
  -- THE SOURCE SEPARATION via the trilinear telescope.
  have hbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ) (P₁ τ) (Jb₁ τ)
        - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (P₂ τ) (Jb₂ τ)‖ ≤ Dsrc := by
    intro τ hτ
    refine (clm2_apply_telescope
      (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ))
      (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ))
      (P₁ τ) (P₂ τ) (Jb₁ τ) (Jb₂ τ)).trans ?_
    rw [hDsrcdef]
    have hT1 : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ * ‖P₁ τ‖ * ‖Jb₁ τ‖
        ≤ DD * Pb * Jbb :=
      mul_le_mul (mul_le_mul (hD2sep τ hτ) (hP1 τ hτ) (norm_nonneg _) hDD0)
        (hJ1 τ hτ) (norm_nonneg _) (mul_nonneg hDD0 hPb0)
    have hT2 : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ * ‖P₁ τ - P₂ τ‖ * ‖Jb₁ τ‖
        ≤ M₂ * DP * Jbb :=
      mul_le_mul (mul_le_mul (hD2Y2 τ hτ) (hPd τ hτ) (norm_nonneg _) hM₂0)
        (hJ1 τ hτ) (norm_nonneg _) (mul_nonneg hM₂0 (le_trans (norm_nonneg _) (hPd τ hτ)))
    have hT3 : ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖ * ‖P₂ τ‖ * ‖Jb₁ τ - Jb₂ τ‖
        ≤ M₂ * Pb * DJb :=
      mul_le_mul (mul_le_mul (hD2Y2 τ hτ) (hP2 τ hτ) (norm_nonneg _) hM₂0)
        (hJd τ hτ) (norm_nonneg _) (mul_nonneg hM₂0 hPb0)
    exact add_le_add (add_le_add hT1 hT2) hT3
  -- THE TWO-POINT GRÖNWALL on the `.2`-component ODE.
  have hmain := linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := fun τ => fderiv ℝ (geodesicField g gi) (Y₁ τ))
    (A₂ := fun τ => fderiv ℝ (geodesicField g gi) (Y₂ τ))
    (X₁ := S₁) (X₂ := S₂)
    (b₁ := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ) (P₁ τ) (Jb₁ τ))
    (b₂ := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (P₂ τ) (Jb₂ τ))
    (K := Kf) (Dcoef := Dc) (Xb := Xb) (Dsrc := Dsrc) hKf0
    hS1 hS2 h0 hKb hAd hXb hbd
  exact hmain

end QIQTH.HbaseJ2Gronwall

/-! ## THE GRÖNWALL LEDGER (post J4-482).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE CONVERGENT WALL.  Both a₁=R/6 consumer chains bottom out on the chart SECOND field-jet at the │
  │  field centre; J4-479 (`ChartSecondJet`) reduced it to the atom `hFwd2`; J4-480 (`Flow3Regularity`)│
  │  discharged the VELOCITY slot (`forward2_velocitySlot`); J4-481 (`SecondVariationModulus`) exposed  │
  │  the endpoint second-variation operator and landed the `.2`-component inhomogeneous Jacobi ODE      │
  │  (`secondVar_snd_hasDerivAt`).  REMAINING for `hFwd2`: the BASE slot `hbaseJ2` — this brick's       │
  │  Grönwall is its wall-felling step.                                                                 │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (i) THE TELESCOPE — `clm2_apply_telescope` (DERIVED, pure CLM).  Separates the trilinear source    │
  │  `D²F·P·Jb` between two bases into (coefficient `‖T−T'‖`) + (mid-slot `‖u−u'‖`) + (right-slot        │
  │  `‖w−w'‖`) parts — the fix for the `∝‖b‖`-loss of the naive full-doubled-norm bound.                │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (ii) THE `.1`-ODE — `secondVar_fst_hasDerivAt` (DERIVED).  `(V·).1' = DF(geo)(Ybase)·(V·).1` — the │
  │  pure first-variation Jacobi ODE (decoupled), via `doubledField_fderiv_fst_apply`.  Companion to    │
  │  J4-481's `.2`-ODE; supplies the `.1`-slot bounds/separation the source telescope consumes.         │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (iii) THE M₃ SEPARATION — `geodesicField_fderiv2_diff_bound` (DERIVED).  `‖D²F x − D²F y‖ ≤ M₃‖x−y‖`│
  │  on convex compact `S`, the C³ MVT with `M₃ = sup‖D³F‖` (`contDiff_fderiv2_geodesicField` +         │
  │  compactness) — the coefficient-separation constant, one order up from the M₂ pattern.              │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (iv) THE GROWTH BOUND — `linODE_growth_bound` (DERIVED).  `‖X t‖ ≤ Bsrc·exp K` for the             │
  │  inhomogeneous zero-seed `.2`-slot field (NOT a homogeneous Jacobi field) — the `Xb` input.         │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (v) ★ THE GRÖNWALL — `secondVar_snd_twopoint_diff_bound` (DERIVED, the star).  The two-point       │
  │  endpoint bound on the `.2`-component ODE:                                                          │
  │      `‖S₁ t − S₂ t‖ ≤ (Dc·Xb + (DD·Pb·Jbb + M₂·DP·Jbb + M₂·Pb·DJb))·exp Kf`,                        │
  │  `linODE_twopoint_diff_bound` on the INHOMOGENEOUS `.2`-component ODE with the source separation     │
  │  from `clm2_apply_telescope`.  Each source term carries a two-point smallness `∝‖q−q'‖` (via Dc =   │
  │  M₂·exp Lsep·‖q−q'‖ tube-sep, DD = M₃·exp Lsep·‖q−q'‖, DP/DJb = `jacobi_twopoint_diff_bound`).       │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT.  The `.1`/`.2` doubled-field projection lemmas (`doubledField_fderiv_fst_apply`
  in `UniformFlowHessianDiag`, `doubledField_fderiv_snd_apply` in `JacobiOperatorFDeriv`), the generic
  two-point Grönwall engine `linODE_twopoint_diff_bound` (any CLM coefficients + inhomogeneous sources)
  and the `jacobi_twopoint_diff_bound` / `jacobi_growth_bound` first-order kit were ALL ALREADY BANKED;
  the C³ third-derivative regularity `contDiff_fderiv2_geodesicField` was banked (J4 tower).  So this
  brick is a SOURCE-SEPARATION telescope + a two-point Grönwall assembly, NOT a new ODE-existence effort.
  ⚠ The honest wall-felling FINDING (J4-481): the naive full-doubled-norm Grönwall FAILS `hbaseJ2` (loses
  the `∝‖b‖` factor); the `.2`-component inhomogeneous ODE — whose SOURCE `clm2_apply_telescope` separates
  — is the fix, and this brick lands exactly that two-point `.2`-component endpoint bound.

  ── WHAT REMAINS (J4-483): instantiate `secondVar_snd_twopoint_diff_bound` at the two exposures
  `uniformFlowExp_secondVar_spec q / q'` (discharging its hypotheses from the banked tube separation,
  M₂/M₃, and `jacobi_twopoint_diff_bound`/`jacobi_growth_bound` on the `.1`/base-Jacobi slots); then the
  bridge `fderiv²(uniformFlowExp q) v δ b = (Vf_q δ 1).2.1` ⊕ the double `opNorm_le_bound` over `(δ,b)`
  ⟹ `hbaseJ2`; then the `z₀`-anchored weld (VELOCITY `forward2_velocitySlot` + BASE `hbaseJ2`) ⟹ `hFwd2`
  ⟹ `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` UNCONDITIONAL ⟹ THE CONVERGENT WALL FALLS.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.HbaseJ2Gronwall
#print axioms clm2_apply_telescope
#print axioms secondVar_fst_hasDerivAt
#print axioms geodesicField_fderiv2_diff_bound
#print axioms linODE_growth_bound
#print axioms secondVar_snd_twopoint_diff_bound
end AxiomChecks
