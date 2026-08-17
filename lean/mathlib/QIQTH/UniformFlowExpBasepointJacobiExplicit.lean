/-
  UniformFlowExpBasepointJacobiExplicit — Task A (plan v2): wire the ALREADY-EXISTING generic
  Jacobi-field engine at the BASE slot for the CONCRETE uniform flow, exactly mirroring how it is
  already wired at the VELOCITY slot (`UniformFlowFDeriv.uniformFlowExp_hasFDerivAt`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is pure
  ODE / variational-regularity plumbing: the EXPLICIT base-point Jacobi field of the concrete geodesic
  flow, and its endpoint's identification with the base-slot Fréchet derivative `∂_q uniformFlowExp`.
  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE ADDS.

  The base-slot Fréchet derivative of `q ↦ uniformFlowExp g gi hC hK q v` already exists as
  `BaseFlowHderFamily.baseFlow_hder_family` (J4-731), but that theorem only EXPOSES the existence of the
  derivative CLM `L` (plus a near-identity bound) — it hides the Jacobi-field REPRESENTATION `L u = (V u 1).1`
  inside its proof.  The downstream second-jet consumer (`ChartMixedThirdJetBasepoint`) needs the
  EXPLICIT base-Jacobi field itself (its ODE, its seed, its endpoint), not merely the derivative's
  existence.  This file supplies it, at the live concrete witness:

  * `uniformFlowExp_basepoint_jacobi_explicit` — ★ THE EXPLICIT BASE-JACOBI FIELD.  For `q` in the
    σ-interior of the compact base set `K` and `‖v‖ ≤ ρ_K`, and any base-perturbation DIRECTION `u`, there
    is an explicit field `J : ℝ → Point n × Point n` and a base-slot derivative CLM `L` with
      - `J 0 = (u, 0)`                                    (the BASE-POINT seed, mirror of the velocity `(0,w)`);
      - `∀ τ ∈ [0,1], HasDerivAt J (DF(uniformFlowTube q v τ)(J τ)) τ`   (the Jacobi ODE along the tube);
      - `∃ Jb, 0 ≤ Jb ∧ ∀ τ ∈ [0,1], ‖J τ‖ ≤ Jb`         (the compact-interval sup bound `hJb`);
      - `HasFDerivAt (fun q' => uniformFlowExp g gi hC hK q' v) L q`   (the base-slot Fréchet derivative);
      - `L u = (J 1).1`                                   (the endpoint IDENTIFICATION — `∂_q exp` in the
                                                            direction `u` is exactly the Jacobi endpoint).
    The field `J` is produced by the generic Jacobi engine `geodesicJacobi_narrowpad_hasDerivAt_Icc`
    along the concrete base tube `uniformFlowTube q v` at the base seed `(u,0)`, and the identification
    is read off the σ-windowed base-slot capstone `geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists`
    (whose CLM representation `L δ = (V δ 1).1` is exactly the Jacobi endpoint), recentred by the base
    translation `δ ↦ q + δ`.  This is the verbatim base-slot mirror of `uniformFlowExp_hasFDerivAt`.

  * `geodesicFlow_secondOrder_base_remainder_gen`, `secondFieldJet_harem_discharge_gen`,
    `source_hbrem_discharge_gen`, `secondFieldJet_basepoint_hasDerivAt_remaindersDischarged_gen` —
    Task A point (6): the seed-GENERALISED versions of the `ChartMixedThirdJetBasepointRemainder`
    theorems.  Those banked theorems hardcode the VELOCITY seed `(0,w)`, but per their own proof the seed
    enters ONLY through the identity `h0 : Y s 0 = X2 0`, so the very same proof goes through for an
    ARBITRARY seed vector `ξ : Point n × Point n` — in particular the BASE seed `(u,0)`.  These are exact
    copies of the banked proofs with `(0,w)` replaced by a general `ξ`.  (The banked files are NOT edited;
    the generalisation is a fresh, additive theorem.)

  The σ-interior-of-`K` hypothesis (`hKσ`: `q` has a σ-ball inside `K`) is an honest geometric input (the
  base point must not touch `∂K`) — the identical premise `baseFlow_hder_family` carries.  This file does
  NOT build the second-field-jet's own variational equation, NOT the Fréchet upgrade of the third jet,
  NOT `hCConv`, NOT Raychaudhuri, NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseFlowHderFamily
import QIQTH.ChartMixedThirdJetBasepointRemainder

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

variable {n : ℕ}

set_option maxHeartbeats 2000000

/-! ### Part 1 — seed-generalised second-order base remainder (Task A point 6).

    Verbatim copies of `ChartMixedThirdJetBasepointRemainder`'s theorems with the hardcoded velocity
    seed `(0,w)` replaced by an ARBITRARY seed vector `ξ`.  The seed enters only through `h0 : Y s 0 = X2 0`,
    so the proofs are unchanged.  In particular they now cover the BASE seed `ξ = (u,0)`. -/

/-- ★ **Seed-generalised** `geodesicFlow_secondOrder_base_remainder`.  For an ARBITRARY seed vector `ξ`
    (`hseed : Y s 0 − Y 0 0 = s • ξ`, `hJ0 : J 0 = ξ`), the geodesic flow's C² base residual is quadratic:
        `‖Y s τ − Y 0 τ − s • J τ‖ ≤ (M₂·L²·exp K)·s²`.
    Identical proof to the banked velocity-seed version; the seed only enters via `h0 : Y s 0 = X2 0`.
    NOT `a₁ = R/6`. -/
theorem geodesicFlow_secondOrder_base_remainder_gen (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K L Yb Jb : ℝ} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hJ0 : J 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb) :
    ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Y s τ - Y 0 τ - s • J τ‖ ≤ (M₂ * L ^ 2 * Real.exp K) * s ^ 2 := by
  intro s τ hτ
  set A0 : ℝ → ((Point n × Point n) →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Y 0 τ) with hA0def
  set X2 : ℝ → Point n × Point n := fun τ => Y 0 τ + s • J τ with hX2def
  set b1 : ℝ → Point n × Point n := fun τ => geodesicField g gi (Y s τ) - A0 τ (Y s τ) with hb1def
  set b2 : ℝ → Point n × Point n := fun τ => geodesicField g gi (Y 0 τ) - A0 τ (Y 0 τ) with hb2def
  have hX1' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Y s) (A0 τ (Y s τ) + b1 τ) τ := by
    intro τ hτ
    have hv : A0 τ (Y s τ) + b1 τ = geodesicField g gi (Y s τ) := by simp only [hb1def]; abel
    rw [hv]; exact hYode s τ hτ
  have hX2' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X2 (A0 τ (X2 τ) + b2 τ) τ := by
    intro τ hτ
    have hd : HasDerivAt X2 (geodesicField g gi (Y 0 τ) + s • (A0 τ (J τ))) τ :=
      (hYode 0 τ hτ).add ((hJode τ hτ).const_smul s)
    have hv : geodesicField g gi (Y 0 τ) + s • (A0 τ (J τ)) = A0 τ (X2 τ) + b2 τ := by
      simp only [hX2def, hb2def, map_add, map_smul]
      abel
    rwa [hv] at hd
  have h0 : Y s 0 = X2 0 := by
    simp only [hX2def, hJ0]
    have := hseed s; rw [sub_eq_iff_eq_add] at this; rw [this]; abel
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ)))
      (hbound2 (Y 0 τ) (hmem 0 τ hτ))
  have hbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b1 τ - b2 τ‖ ≤ M₂ * L ^ 2 * s ^ 2 := by
    intro τ hτ
    have hsplit : b1 τ - b2 τ
        = geodesicField g gi (Y s τ) - geodesicField g gi (Y 0 τ)
          - fderiv ℝ (geodesicField g gi) (Y 0 τ) (Y s τ - Y 0 τ) := by
      simp only [hb1def, hb2def, hA0def, map_sub]
      abel
    rw [hsplit]
    have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2
      (hmem s τ hτ) (hmem 0 τ hτ)
    refine hrem.trans ?_
    have hLs := hL s τ hτ
    have hLsnn : 0 ≤ L * |s| := le_trans (norm_nonneg _) hLs
    have hsq : ‖Y s τ - Y 0 τ‖ ^ 2 ≤ L ^ 2 * s ^ 2 := by
      have hmm := mul_le_mul hLs hLs (norm_nonneg _) hLsnn
      calc ‖Y s τ - Y 0 τ‖ ^ 2 = ‖Y s τ - Y 0 τ‖ * ‖Y s τ - Y 0 τ‖ := by ring
        _ ≤ (L * |s|) * (L * |s|) := hmm
        _ = L ^ 2 * s ^ 2 := by rw [← sq_abs s]; ring
    calc M₂ * ‖Y s τ - Y 0 τ‖ ^ 2 ≤ M₂ * (L ^ 2 * s ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hnn
      _ = M₂ * L ^ 2 * s ^ 2 := by ring
  have hX2b : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X2 τ‖ ≤ Yb + |s| * Jb := by
    intro τ hτ
    simp only [hX2def]
    refine (norm_add_le _ _).trans (add_le_add (hYb τ hτ) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hJb τ hτ) (abs_nonneg _)
  have hmain := linODE_twopoint_diff_bound (E := Point n × Point n)
    (A₁ := A0) (A₂ := A0) (X₁ := Y s) (X₂ := X2) (b₁ := b1) (b₂ := b2)
    (K := K) (Dcoef := 0) (Xb := Yb + |s| * Jb) (Dsrc := M₂ * L ^ 2 * s ^ 2)
    hK0 hX1' hX2' h0 hKb (fun τ _ => by simp) hX2b hbd
  have := hmain τ hτ
  rw [zero_mul, zero_add] at this
  have hXt : Y s τ - X2 τ = Y s τ - Y 0 τ - s • J τ := by simp only [hX2def]; abel
  rw [hXt] at this
  have heq : M₂ * L ^ 2 * s ^ 2 * Real.exp K = M₂ * L ^ 2 * Real.exp K * s ^ 2 := by ring
  rwa [heq] at this

/-- ★ **Seed-generalised** `secondFieldJet_harem_discharge` (arbitrary seed `ξ`). -/
theorem secondFieldJet_harem_discharge_gen (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K L Yb Jb : ℝ} {Kl : NNReal} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hlip2 : LipschitzOnWith Kl (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hJ0 : J 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s : ℝ,
      ‖fderiv ℝ (geodesicField g gi) (Y s τ) - fderiv ℝ (geodesicField g gi) (Y 0 τ)
          - s • (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ))‖
        ≤ ((Kl : ℝ) * L ^ 2 + M₂ * (M₂ * L ^ 2 * Real.exp K)) * s ^ 2 := by
  have hDF : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ (geodesicField g gi)) x :=
    fun x _ => (hDF.differentiable (by simp)) x
  have hCyall := geodesicFlow_secondOrder_base_remainder_gen g gi hC hK0 hconv hbound2
    hYode hJode hseed hJ0 hKb hmem hL hYb hJb
  intro s
  exact family_secondOrder_remainder (fderiv ℝ (geodesicField g gi)) hconv hdiff hlip2
    hbound2 (fun s => hmem s τ hτ) (hmem 0 τ hτ)
    (fun s => hL s τ hτ) (fun s => hCyall s τ hτ) s

/-- ★ **Seed-generalised** `source_hbrem_discharge` (arbitrary seed `ξ`). -/
theorem source_hbrem_discharge_gen (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (φ : Point n × Point n → Point n × Point n)
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ Mφ1 K L Yb Jb : ℝ} {Kφ : NNReal} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hφdiff : ∀ x ∈ S, DifferentiableAt ℝ φ x)
    (hφlip : LipschitzOnWith Kφ (fderiv ℝ φ) S)
    (hφb1 : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ Mφ1)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hJ0 : J 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hL : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s : ℝ,
      ‖φ (Y s τ) - φ (Y 0 τ) - s • (fderiv ℝ φ (Y 0 τ) (J τ))‖
        ≤ ((Kφ : ℝ) * L ^ 2 + Mφ1 * (M₂ * L ^ 2 * Real.exp K)) * s ^ 2 := by
  have hCyall := geodesicFlow_secondOrder_base_remainder_gen g gi hC hK0 hconv hbound2
    hYode hJode hseed hJ0 hKb hmem hL hYb hJb
  intro s
  exact family_secondOrder_remainder φ hconv hφdiff hφlip hφb1
    (fun s => hmem s τ hτ) (hmem 0 τ hτ)
    (fun s => hL s τ hτ) (fun s => hCyall s τ hτ) s

/-- ★ **Seed-generalised** `secondFieldJet_basepoint_hasDerivAt_remaindersDischarged` (arbitrary seed `ξ`).
    The base-point derivative of the second field-jet exists and equals `R t`, with `harem`/`hbrem`
    replaced by standard geometric/ODE data, now valid for ANY seed `ξ` — in particular the base seed
    `ξ = (u,0)`.  NOT `a₁ = R/6`. -/
theorem secondFieldJet_basepoint_hasDerivAt_remaindersDischarged_gen
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (φ : Point n × Point n → Point n × Point n)
    {Y : ℝ → ℝ → Point n × Point n} {J : ℝ → Point n × Point n} {ξ : Point n × Point n}
    {X : ℝ → ℝ → Point n × Point n} {R : ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ Mφ1 K L Yb Jb Kad Xb Lx Rb : ℝ} {Kl Kφ : NNReal}
    (hK0 : 0 ≤ K) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hlip2 : LipschitzOnWith Kl (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    (hφdiff : ∀ x ∈ S, DifferentiableAt ℝ φ x)
    (hφlip : LipschitzOnWith Kφ (fderiv ℝ φ) S)
    (hφb1 : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ Mφ1)
    (hYode : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y s) (geodesicField g gi (Y s τ)) τ)
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y 0 τ) (J τ)) τ)
    (hseed : ∀ s : ℝ, Y s 0 - Y 0 0 = s • ξ)
    (hJ0 : J 0 = ξ)
    (hKbY : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (hmem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y s τ ∈ S)
    (hLY : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y s τ - Y 0 τ‖ ≤ L * |s|)
    (hYb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Y 0 τ‖ ≤ Yb)
    (hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb)
    (hX : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (X s)
        (fderiv ℝ (geodesicField g gi) (Y s τ) (X s τ) + φ (Y s τ)) τ)
    (hR : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt R
        (fderiv ℝ (geodesicField g gi) (Y 0 τ) (R τ)
          + (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ) (X 0 τ)
            + fderiv ℝ φ (Y 0 τ) (J τ))) τ)
    (hseedX : ∀ s : ℝ, X s 0 - X 0 0 = s • R 0)
    (hXb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ‖ ≤ Xb)
    (hXlip : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ - X 0 τ‖ ≤ Lx * |s|)
    (hRb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖R τ‖ ≤ Rb)
    (hKad : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ)‖ ≤ Kad)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => X s t) (R t) 0 := by
  refine secondFieldJet_basepoint_hasDerivAt g gi
    (Y := Y)
    (Ad := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y 0 τ) (J τ))
    (X := X) (b := fun s τ => φ (Y s τ))
    (bd := fun τ => fderiv ℝ φ (Y 0 τ) (J τ)) (R := R)
    (K := K) (Ca := (Kl : ℝ) * L ^ 2 + M₂ * (M₂ * L ^ 2 * Real.exp K))
    (Cb := (Kφ : ℝ) * L ^ 2 + Mφ1 * (M₂ * L ^ 2 * Real.exp K))
    (Xb := Xb) (Kad := Kad) (Lx := Lx) (Rb := Rb) hK0 hX hR hseedX hKbY ?harem hKad hXb hXlip hRb
    ?hbrem ht
  case harem =>
    intro s τ hτ
    exact secondFieldJet_harem_discharge_gen g gi hC hK0 hconv hbound2 hlip2 hYode hJode hseed hJ0
      hKbY hmem hLY hYb hJb hτ s
  case hbrem =>
    intro s τ hτ
    exact source_hbrem_discharge_gen g gi hC φ hK0 hconv hφdiff hφlip hφb1 hbound2 hYode hJode hseed hJ0
      hKbY hmem hLY hYb hJb hτ s

/-! ### Part 2 — the EXPLICIT base-point Jacobi field of the concrete uniform flow.

    Verbatim base-slot mirror of `UniformFlowFDeriv.uniformFlowExp_hasFDerivAt` (the velocity slot):
    the generic Jacobi engine `geodesicJacobi_narrowpad_hasDerivAt_Icc` is instantiated along the
    concrete base tube `uniformFlowTube q v` at the BASE seed `(u,0)`, and its endpoint is identified with
    the base-slot Fréchet derivative `∂_q uniformFlowExp` via the σ-windowed base-slot capstone
    `geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists`, recentred by `δ ↦ q + δ`. -/

/-- ★ **THE EXPLICIT BASE-POINT JACOBI FIELD (base-slot mirror of `uniformFlowExp_hasFDerivAt`).**

    Fix the compact base set `K`, a velocity `v` with `‖v‖ ≤ ρ_K`, a base point `q` in the σ-interior of
    `K` (`hKσ`: every `δ` with `‖δ‖ ≤ σ` keeps `q+δ ∈ K`), and a base-perturbation DIRECTION `u`.  Then
    there is an EXPLICIT Jacobi field `J` and a base-slot derivative CLM `L` with:
      * `J 0 = (u, 0)`                                            — the base-point seed;
      * `∀ τ ∈ [0,1], HasDerivAt J (DF(uniformFlowTube q v τ)(J τ)) τ`  — the Jacobi ODE along the tube;
      * `∃ Jb, 0 ≤ Jb ∧ ∀ τ ∈ [0,1], ‖J τ‖ ≤ Jb`                — the compact-interval sup bound;
      * `HasFDerivAt (fun q' => uniformFlowExp g gi hC hK q' v) L q`   — the base-slot Fréchet derivative;
      * `L u = (J 1).1`                                          — endpoint identification.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_basepoint_jacobi_explicit (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (q v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (σ : ℝ) (hσ : 0 < σ) (hKσ : ∀ δ : Point n, ‖δ‖ ≤ σ → q + δ ∈ K)
    (u : Point n) :
    ∃ (J : ℝ → Point n × Point n) (L : Point n →L[ℝ] Point n),
      J 0 = ((u, 0) : Point n × Point n) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt J
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (J τ)) τ) ∧
      (∃ Jb : ℝ, 0 ≤ Jb ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖J τ‖ ≤ Jb) ∧
      HasFDerivAt (fun q' => uniformFlowExp g gi hC hK q' v) L q ∧
      L u = (J 1).1 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hqK : ∀ δ : Point n, ‖δ‖ ≤ σ → q + δ ∈ K := hKσ
  -- the phase-space confinement ball `S`, centred at `(q,0)`.
  set Rphase : ℝ := C₀ * ‖v‖ + σ with hRphasedef
  have hRphase0 : 0 ≤ Rphase := by
    rw [hRphasedef]; have := mul_nonneg hC₀nn (norm_nonneg v); linarith [hσ.le]
  set S : Set (Point n × Point n) := Metric.closedBall ((q, 0) : Point n × Point n) Rphase with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hSne : S.Nonempty := ⟨(q, 0), by rw [hSdef]; exact Metric.mem_closedBall_self hRphase0⟩
  -- window-uniform field constants on `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  -- perturbed base tubes `Wf δ := uniformFlowTube (q+δ) v`.
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK (q + δ) v with hWfdef
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK (q + δ) (hqK δ hδ) v hv τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    have hconf : ‖Wf δ τ - ((q + δ, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK (q + δ) (hqK δ hδ) v hv τ hτ
    have hb1 : ‖((q + δ, 0) : Point n × Point n) - (q, 0)‖ ≤ σ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]
      simp only [norm_zero]
      rw [max_eq_left (norm_nonneg _), show q + δ - q = δ from by abel]
      exact hδ
    calc ‖Wf δ τ - ((q, 0) : Point n × Point n)‖
        = ‖(Wf δ τ - (q + δ, 0)) + ((q + δ, 0) - (q, 0))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Wf δ τ - ((q + δ, 0) : Point n × Point n)‖
            + ‖((q + δ, 0) : Point n × Point n) - (q, 0)‖ := norm_add_le _ _
      _ ≤ C₀ * ‖v‖ + σ := add_le_add hconf hb1
      _ = Rphase := by rw [hRphasedef]
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((δ, 0) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = ((q + δ, v) : Point n × Point n) :=
      uniformFlowTube_spec_ic g gi hC hK (q + δ) (hqK δ hδ) v hv
    have h2 : Wf 0 0 = ((q + 0, v) : Point n × Point n) :=
      uniformFlowTube_spec_ic g gi hC hK (q + 0) (hqK 0 h0σ) v hv
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  -- base-tube continuity on the narrow pad; base-tube Jacobi solutions at the position seed.
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK (q + 0) (hqK 0 h0σ) v hv τ hτoo).continuousAt).continuousWithinAt
  set V : Point n → ℝ → Point n × Point n :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose with hVdef
  have hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n) :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose_spec.1
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (Wf 0 τ) (V δ τ)) τ :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose_spec.2
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  -- the σ-windowed base-slot endpoint-position Fréchet derivative, with its Jacobi representation.
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  obtain ⟨L₀, hLeq, hFD⟩ := geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists g gi hC
    hKf0 hσ ht1 hSconv hM₂ hLip hWode hVode hV0 hIC hKb hmem
  -- the base curve `Wf 0 = uniformFlowTube (q+0) v` agrees with `uniformFlowTube q v`.
  have hbaseeq : Wf 0 = uniformFlowTube g gi hC hK q v := by
    funext τ; simp only [hWfdef, add_zero]
  -- recentre `L₀` (a derivative at `δ = 0` of `δ ↦ (Wf δ 1).1`) to a derivative at `q`.
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK (q + δ) v) := by
    funext δ; show (Wf δ 1).1 = uniformFlowExp g gi hC hK (q + δ) v; rw [uniformFlowExp_eq]
  rw [hfun] at hFD
  have hshift : HasFDerivAt (fun q' : Point n => q' - q) (ContinuousLinearMap.id ℝ (Point n)) q :=
    (hasFDerivAt_id q).sub_const q
  have hFD0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK (q + δ) v) L₀ (q - q) := by
    rw [sub_self]; exact hFD
  have hcomp : HasFDerivAt (fun q' => uniformFlowExp g gi hC hK (q + (q' - q)) v)
      (L₀.comp (ContinuousLinearMap.id ℝ (Point n))) q :=
    hFD0.comp (f := fun q' : Point n => q' - q) q hshift
  have hfun2 : (fun q' => uniformFlowExp g gi hC hK (q + (q' - q)) v)
      = (fun q' => uniformFlowExp g gi hC hK q' v) := by
    funext q'; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  -- the explicit field: `J := V u` (the base-slot Jacobi field at the direction seed `(u,0)`).
  refine ⟨V u, L₀, hV0 u, ?_, ?_, hcomp, ?_⟩
  · -- Jacobi ODE along `uniformFlowTube q v`.
    intro τ hτ
    have := hVode u τ hτ
    rwa [hbaseeq] at this
  · -- compact-interval sup bound on `‖V u τ‖`.
    have hcont : ContinuousOn (fun τ => ‖V u τ‖) (Set.Icc (0 : ℝ) 1) := by
      intro τ hτ
      exact ((hVode u τ hτ).continuousAt.norm).continuousWithinAt
    obtain ⟨x, hxmem, hx⟩ :=
      (isCompact_Icc).exists_isMaxOn (⟨0, Set.left_mem_Icc.mpr zero_le_one⟩) hcont
    refine ⟨‖V u x‖, norm_nonneg _, fun τ hτ => (isMaxOn_iff.mp hx) τ hτ⟩
  · -- endpoint identification `L₀ u = (V u 1).1`.
    exact hLeq u

end QIQTH.ExpMap
