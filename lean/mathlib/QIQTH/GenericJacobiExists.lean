/-
  GenericJacobiExists — J4-42: the GENERIC `[0,1]` linear-ODE (Jacobi-field) EXISTENCE over an
  ARBITRARY base curve.

  ## Context

  The CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`)
  proves the compact-uniform local exp-nondegeneracy gate `(J)` FROM a doubled-family SUPPLY whose
  `hYode`/`hVode` binders are integral curves of `doubledField`/the linearized field on `[0,1]`.  Per
  `DoubledFamilyConstruction.lean` (J4-40), the SOLE hard residual in constructing that supply is a
  GENERIC linear-ODE (Jacobi field) existence over an ARBITRARY confined base curve on `[0,1]` — the
  repo's `expJet…Fund` linear solvers are welded to `expTube`, not a generic base.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled supply)

  * `linODE_exists_on_Icc` — **the key residual.**  For a time-dependent bounded operator
    `A : ℝ → (E →L[ℝ] E)` continuous on `[0,1]` and a seed `w₀ : E`, there is `J : ℝ → E` with
    `J 0 = w₀` solving the homogeneous linear ODE `J' τ = A τ (J τ)` on `[0,1]`
    (`HasDerivWithinAt` form).  The field `f τ y = A τ y` is GLOBALLY Lipschitz in `y` (constant
    `sup_{[0,1]} ‖A τ‖ < ∞` by continuity on the compact `[0,1]`) and continuous in `τ`, so each short
    subinterval satisfies Mathlib's `IsPicardLindelof`.  Because the Mathlib PL structure carries the
    interval constraint `L·max(tmax−t₀, t₀−tmin) ≤ a − r` — which a SINGLE application over `[0,1]`
    cannot meet once the Lipschitz constant is `≥ 1` — existence is obtained by CONCATENATING `N`
    single-subinterval PL solutions (`N > 2·sup‖A‖`), glued at the nodes via `glue_Icc_hasDerivWithinAt`.

  * `linODE_exists_hasDerivAt_Icc` — the two-sided upgrade: solving on the padded interval `[-1,2]`
    (seed at the interior `0`, forward+backward), for `τ ∈ [0,1] ⊆ Ioo (-1) 2` the within-derivative
    upgrades to a genuine two-sided `HasDerivAt J (A τ (J τ)) τ` (matching the bridge's `hYode` shape).

  * `geodesicJacobi_exists_on_Icc` — the geodesic specialization: for the phase base curve
    `Ybase : ℝ → Point n × Point n` continuous on `[0,1]`, the Jacobi field `J' = DF(Ybase τ)·J`
    (`A τ = fderiv ℝ (geodesicField g gi) (Ybase τ)`) exists on `[0,1]` with two-sided `HasDerivAt`.
    Continuity of `A` is DERIVED from `geodesicField ∈ C^∞` (`contDiff_geodesicField`) ⇒ `fderiv`
    continuous, composed with the continuous base curve.

  ## HONEST CHECKPOINT (binding)

  This is the generic linear-ODE (Jacobi) existence analysis lemma — the identified hard residual of
  the doubled-family supply.  It is a GENUINE existence result (Picard–Lindelöf per subinterval +
  concatenation), fully self-contained: its hypotheses are only `ContinuousOn A [0,1]` (resp. the
  geometric `hC` + continuous base curve) and a seed.  It does NOT by itself assemble the full doubled
  family `Y`/`Vf` of the bridge (that also needs the paired geodesic phase-flow `P`, the confinement
  set `S`, the first-jet link `hlink`, and the `Zf` second-variation data), does NOT discharge `(J)`,
  does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.JacobiDoubledFamily
import QIQTH.DoubledFamilyConstruction
import QIQTH.BoundedGeometryConfine
import QIQTH.VelocitySecondJetId
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 1000000

section GlueHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Glue two curves at a node `b`: use `u` up to `b`, `v` after. -/
noncomputable def glueAt (b : ℝ) (u v : ℝ → E) : ℝ → E :=
  fun t => if t ≤ b then u t else v t

/-- Left subinterval is a neighbourhood within the big interval, at an interior-left point. -/
lemma Icc_left_mem_nhdsWithin_Icc {a b c t : ℝ} (ht : t < b) :
    Set.Icc a b ∈ 𝓝[Set.Icc a c] t := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)]
    with y hyac hylt
  exact ⟨hyac.1, le_of_lt hylt⟩

/-- Right subinterval is a neighbourhood within the big interval, at an interior-right point. -/
lemma Icc_right_mem_nhdsWithin_Icc {a b c t : ℝ} (ht : b < t) :
    Set.Icc b c ∈ 𝓝[Set.Icc a c] t := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)]
    with y hyac hygt
  exact ⟨le_of_lt hygt, hyac.2⟩

/-- **Gluing lemma.**  Two ODE solutions to the same field `F`, one on `[a,b]` and one on `[b,c]`
    matching at `b`, glue to a solution on `[a,c]`. -/
lemma glue_Icc_hasDerivWithinAt {F : ℝ → E → E} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {u v : ℝ → E} (hmatch : u b = v b)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivWithinAt u (F t (u t)) (Set.Icc a b) t)
    (hv : ∀ t ∈ Set.Icc b c, HasDerivWithinAt v (F t (v t)) (Set.Icc b c) t) :
    ∀ t ∈ Set.Icc a c,
      HasDerivWithinAt (glueAt b u v) (F t (glueAt b u v t)) (Set.Icc a c) t := by
  intro t ht
  set w := glueAt b u v with hw
  have hw_left : ∀ y ∈ Set.Icc a b, w y = u y := by
    intro y hy; simp [hw, glueAt, hy.2]
  have hw_right : ∀ y ∈ Set.Icc b c, w y = v y := by
    intro y hy
    by_cases hyb : y ≤ b
    · have hy_eq : y = b := le_antisymm hyb hy.1
      subst y; simp [hw, glueAt, hmatch]
    · simp [hw, glueAt, hyb]
  by_cases hlt : t < b
  · -- strictly left of the node
    have ht_left : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt hlt⟩
    have hloc : HasDerivWithinAt w (F t (w t)) (Set.Icc a b) t := by
      have h0 := (hu t ht_left).congr hw_left (hw_left t ht_left)
      rwa [← hw_left t ht_left] at h0
    exact hloc.mono_of_mem_nhdsWithin (Icc_left_mem_nhdsWithin_Icc hlt)
  · have hbt : b ≤ t := le_of_not_gt hlt
    by_cases hgt : b < t
    · -- strictly right of the node
      have ht_right : t ∈ Set.Icc b c := ⟨le_of_lt hgt, ht.2⟩
      have hloc : HasDerivWithinAt w (F t (w t)) (Set.Icc b c) t := by
        have h0 := (hv t ht_right).congr hw_right (hw_right t ht_right)
        rwa [← hw_right t ht_right] at h0
      exact hloc.mono_of_mem_nhdsWithin (Icc_right_mem_nhdsWithin_Icc hgt)
    · -- the node `t = b`
      have ht_eq : t = b := le_antisymm (le_of_not_gt hgt) hbt
      subst t
      have hb_left : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
      have hb_right : b ∈ Set.Icc b c := ⟨le_rfl, hbc⟩
      have hleft : HasDerivWithinAt w (F b (w b)) (Set.Icc a b) b := by
        have h0 := (hu b hb_left).congr hw_left (hw_left b hb_left)
        rwa [← hw_left b hb_left] at h0
      have hright : HasDerivWithinAt w (F b (w b)) (Set.Icc b c) b := by
        have h0 := (hv b hb_right).congr hw_right (hw_right b hb_right)
        rwa [← hw_right b hb_right] at h0
      have hboth := hleft.union hright
      rwa [Set.Icc_union_Icc_eq_Icc hab hbc] at hboth

end GlueHelpers

section LinODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Single-subinterval Picard–Lindelöf for a linear field.**  On `[k/N, (k+1)/N] ⊆ [0,1]`, with a
    global operator-norm bound `M ≥ 0` on `A` over `[0,1]` and step size chosen via `2·M ≤ N`, the
    linear ODE `V' = A τ (V τ)` with seed `x` at `k/N` has a solution on the subinterval. -/
lemma linODE_onestep (A : ℝ → (E →L[ℝ] E)) (M : ℝ) (hM0 : 0 ≤ M)
    (hMbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ M)
    (hAcont : ContinuousOn A (Set.Icc (0 : ℝ) 1))
    (N : ℕ) (hNpos : 0 < N) (hN : 2 * M ≤ (N : ℝ))
    (k : ℕ) (hk : k < N) (x : E) :
    ∃ V : ℝ → E, V ((k : ℝ) / N) = x ∧
      ∀ t ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N),
        HasDerivWithinAt V (A t (V t)) (Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) t := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set b : ℝ := (k : ℝ) / N with hbdef
  set c : ℝ := ((k : ℝ) + 1) / N with hcdef
  have hbc : b ≤ c := by rw [hbdef, hcdef]; gcongr; linarith
  have hcb : c - b = 1 / N := by rw [hbdef, hcdef, div_sub_div_same]; congr 1; ring
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hNr]
    have hkN : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
    linarith
  have hsub : Set.Icc b c ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc hb0 hc1
  -- radius/bound parameters
  set a : ℝ := max ‖x‖ 1 with hadef
  have ha1 : (1 : ℝ) ≤ a := le_max_right _ _
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha1
  have haxle : ‖x‖ ≤ a := le_max_left _ _
  set ann : ℝ≥0 := ⟨a, ha0.le⟩ with hanndef
  set Mnn : ℝ≥0 := ⟨M, hM0⟩ with hMnndef
  set Lnn : ℝ≥0 := ⟨2 * M * a, by positivity⟩ with hLnndef
  have haC : (ann : ℝ) = a := rfl
  have hMC : (Mnn : ℝ) = M := rfl
  have hLC : (Lnn : ℝ) = 2 * M * a := rfl
  have ht0mem : b ∈ Set.Icc b c := ⟨le_refl b, hbc⟩
  have hpl : IsPicardLindelof (fun t (y : E) => A t y)
      (tmin := b) (tmax := c) ⟨b, ht0mem⟩ x ann 0 Lnn Mnn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `y` with constant `M`
      intro t ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro p _ q _
      simp only [dist_eq_norm, hMC]
      calc ‖A t p - A t q‖ = ‖A t (p - q)‖ := by rw [← map_sub]
        _ ≤ ‖A t‖ * ‖p - q‖ := (A t).le_opNorm _
        _ ≤ M * ‖p - q‖ := by gcongr; exact hMbd t (hsub ht)
    · -- continuity in `t`
      intro y _
      exact (hAcont.mono hsub).clm_apply continuousOn_const
    · -- norm bound `L = 2·M·a`
      intro t ht y hy
      have hyx : ‖y - x‖ ≤ a := by
        rw [← dist_eq_norm]; simpa [haC] using Metric.mem_closedBall.mp hy
      have hynorm : ‖y‖ ≤ 2 * a := by
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ a + a := add_le_add hyx haxle
          _ = 2 * a := by ring
      calc ‖A t y‖ ≤ ‖A t‖ * ‖y‖ := (A t).le_opNorm _
        _ ≤ M * (2 * a) := mul_le_mul (hMbd t (hsub ht)) hynorm (norm_nonneg _) hM0
        _ = (Lnn : ℝ) := by rw [hLC]; ring
    · -- interval constraint `L·(c−b) ≤ a`
      have hmax : max (c - b) (b - b) = c - b := by
        rw [sub_self]; exact max_eq_left (by rw [hcb]; positivity : (0 : ℝ) ≤ c - b)
      have key : (Lnn : ℝ) * max (c - b) (b - b) ≤ (ann : ℝ) := by
        rw [hLC, haC, hmax, hcb, mul_one_div, div_le_iff₀ hNr]
        have hle : 2 * M * a ≤ (N : ℝ) * a := by
          have := mul_le_mul_of_nonneg_right hN ha0.le; linarith
        linarith [hle, mul_comm (N : ℝ) a]
      simpa [tsub_zero, sub_zero, NNReal.coe_zero] using key
  obtain ⟨V, hV0, hVd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨V, hV0, hVd⟩

/-- **Generic `[0,1]` linear-ODE (Jacobi-field) existence.**  For a time-dependent bounded operator
    `A` continuous on `[0,1]` and any seed `w₀`, the homogeneous linear ODE `J' τ = A τ (J τ)` has a
    solution `J` on `[0,1]` with `J 0 = w₀`.  Existence is obtained by concatenating `N` single-
    subinterval Picard–Lindelöf solutions (`N > 2·sup_{[0,1]}‖A‖`), glued at the nodes. -/
theorem linODE_exists_on_Icc (A : ℝ → (E →L[ℝ] E))
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt J (A τ (J τ)) (Set.Icc (0 : ℝ) 1) τ := by
  classical
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖A t‖ ≤ M :=
    fun t ht => (hM₀ t ht).trans (le_max_left _ _)
  obtain ⟨N, hNr⟩ := exists_nat_gt (2 * M)
  have hNr0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hNr
  have hNpos : 0 < N := by exact_mod_cast hNr0
  have hN : 2 * M ≤ (N : ℝ) := hNr.le
  set node : ℕ → ℝ := fun j => (j : ℝ) / N with hnode
  have hnodeval : ∀ j : ℕ, node j = (j : ℝ) / N := fun j => rfl
  have hnode0 : node 0 = 0 := by simp [hnodeval]
  have hnodeN : node N = 1 := by rw [hnodeval]; exact div_self (ne_of_gt hNr0)
  have hnode_succ : ∀ j : ℕ, node (j + 1) = ((j : ℝ) + 1) / N := by
    intro j; rw [hnodeval]; push_cast; ring
  have hnode_nonneg : ∀ j : ℕ, 0 ≤ node j := by
    intro j; rw [hnodeval]; positivity
  -- prefix induction
  have hPall : ∀ k, k ≤ N → ∃ J : ℝ → E, J 0 = w₀ ∧
      (k ≠ 0 → ∀ t ∈ Set.Icc (0 : ℝ) (node k),
        HasDerivWithinAt J (A t (J t)) (Set.Icc (0 : ℝ) (node k)) t) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ => w₀, rfl, fun h => absurd rfl h⟩
    | succ k ih =>
      intro hk1
      have hk : k < N := Nat.lt_of_succ_le hk1
      obtain ⟨J, hJ0, hJd⟩ := ih (Nat.le_of_succ_le hk1)
      obtain ⟨V, hVb, hVd⟩ := linODE_onestep A M hM0 hMbd hA N hNpos hN k hk (J (node k))
      rw [← hnodeval k] at hVb hVd
      rw [← hnode_succ k] at hVd
      have hnk0 : 0 ≤ node k := hnode_nonneg k
      have hkk1 : node k ≤ node (k + 1) := by
        rw [hnode_succ k, hnodeval k]; gcongr; linarith
      by_cases hk0 : k = 0
      · subst k
        refine ⟨V, ?_, fun _ => ?_⟩
        · rw [hnode0] at hVb; rw [hVb, hJ0]
        · rw [hnode0] at hVd; exact hVd
      · refine ⟨glueAt (node k) J V, ?_, fun _ t ht => ?_⟩
        · simp only [glueAt]; rw [if_pos hnk0, hJ0]
        · have hmatch : J (node k) = V (node k) := hVb.symm
          have hglue := glue_Icc_hasDerivWithinAt (F := fun t (y : E) => A t y)
            (a := 0) (b := node k) (c := node (k + 1)) hnk0 hkk1 hmatch (hJd hk0) hVd
          exact hglue t ht
  obtain ⟨J, hJ0, hJd⟩ := hPall N le_rfl
  refine ⟨J, hJ0, ?_⟩
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hfin := hJd hNne
  rw [hnodeN] at hfin
  exact hfin

/-- **Forward reparametrization to `[0,T]`.**  Rescaling the `[0,1]` solver by `T` (field
    `Ã s = T • A (T·s)`) yields the linear-ODE solution on `[0,T]` with seed at the left endpoint. -/
lemma linODE_exists_forward (A : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 < T)
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) T)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt J (A τ (J τ)) (Set.Icc (0 : ℝ) T) τ := by
  set Ã : ℝ → (E →L[ℝ] E) := fun s => (T : ℝ) • A (T * s) with hÃ
  have hmapin : Set.MapsTo (fun s => T * s) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) T) := by
    intro s hs
    exact ⟨by nlinarith [hs.1, hT.le], by nlinarith [hs.2, hT.le]⟩
  have hÃcont : ContinuousOn Ã (Set.Icc (0 : ℝ) 1) :=
    (hA.comp ((continuous_const.mul continuous_id).continuousOn) hmapin).const_smul (T : ℝ)
  obtain ⟨J₀, hJ00, hJ0d⟩ := linODE_exists_on_Icc Ã hÃcont w₀
  refine ⟨fun τ => J₀ (τ / T), by simp [hJ00], fun τ hτ => ?_⟩
  have hmapout : Set.MapsTo (fun τ => τ / T) (Set.Icc (0 : ℝ) T) (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hT.le, by rw [div_le_one hT]; exact hs.2⟩
  have hτ1 : τ / T ∈ Set.Icc (0 : ℝ) 1 := hmapout hτ
  have hgd : HasDerivWithinAt (fun τ => τ / T) (1 / T) (Set.Icc (0 : ℝ) T) τ := by
    simpa using (hasDerivWithinAt_id τ (Set.Icc (0 : ℝ) T)).div_const T
  have hcomp := (hJ0d (τ / T) hτ1).scomp τ hgd hmapout
  have hTτ : (T : ℝ) * (τ / T) = τ := by field_simp
  have hval : (1 / T : ℝ) • (Ã (τ / T) (J₀ (τ / T))) = A τ (J₀ (τ / T)) := by
    simp only [hÃ, hTτ, ContinuousLinearMap.smul_apply, smul_smul]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hT), one_smul]
  rw [hval] at hcomp
  exact hcomp

/-- **Backward reparametrization to `[-T,0]`.**  Reflecting the forward solver (field
    `Aref σ = -A(-σ)`) yields the linear-ODE solution on `[-T,0]` with seed at the RIGHT endpoint `0`. -/
lemma linODE_exists_backward (A : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 < T)
    (hA : ContinuousOn A (Set.Icc (-T) 0)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (-T) 0, HasDerivWithinAt J (A τ (J τ)) (Set.Icc (-T) 0) τ := by
  set Aref : ℝ → (E →L[ℝ] E) := fun σ => -A (-σ) with hAref
  have hmapref : Set.MapsTo (fun σ => -σ) (Set.Icc (0 : ℝ) T) (Set.Icc (-T) 0) := by
    intro σ hσ; exact ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hArefcont : ContinuousOn Aref (Set.Icc (0 : ℝ) T) :=
    (hA.comp continuous_neg.continuousOn hmapref).neg
  obtain ⟨K, hK0, hKd⟩ := linODE_exists_forward Aref T hT hArefcont w₀
  refine ⟨fun τ => K (-τ), by simp [hK0], fun τ hτ => ?_⟩
  have hmapout : Set.MapsTo (fun τ => -τ) (Set.Icc (-T) 0) (Set.Icc (0 : ℝ) T) := by
    intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hmem : (-τ) ∈ Set.Icc (0 : ℝ) T := hmapout hτ
  have hneg : HasDerivWithinAt (fun τ => -τ) (-1) (Set.Icc (-T) 0) τ := by
    simpa using (hasDerivWithinAt_id τ (Set.Icc (-T) 0)).neg
  have hcomp := (hKd (-τ) hmem).scomp τ hneg hmapout
  have hval : ((-1 : ℝ)) • (Aref (-τ) (K (-τ))) = A τ (K (-τ)) := by
    simp only [hAref, neg_neg, ContinuousLinearMap.neg_apply, neg_one_smul, neg_neg]
  rw [hval] at hcomp
  exact hcomp

/-- **Two-sided derivative on the CLOSED interval `[0,1]`.**  Solving on the padded interval `[-1,2]`
    with the seed pinned at the interior point `0` (forward on `[0,2]`, backward on `[-1,0]`, glued at
    `0`), every `τ ∈ [0,1] ⊆ Ioo (-1) 2` gets a genuine two-sided `HasDerivAt`.  This is the shape the
    doubled-family supply binder `hYode` consumes.  Requires `A` continuous on the padded `[-1,2]`. -/
theorem linODE_exists_hasDerivAt_Icc (A : ℝ → (E →L[ℝ] E))
    (hA : ContinuousOn A (Set.Icc (-1 : ℝ) 2)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (A τ (J τ)) τ := by
  obtain ⟨Jf, hJf0, hJfd⟩ := linODE_exists_forward A 2 (by norm_num)
    (hA.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)) w₀
  obtain ⟨Jb, hJb0, hJbd⟩ := linODE_exists_backward A 1 (by norm_num)
    (hA.mono (Set.Icc_subset_Icc le_rfl (by norm_num))) w₀
  set J := glueAt 0 Jb Jf with hJdef
  have hmatch : Jb 0 = Jf 0 := by rw [hJb0, hJf0]
  have hglue := glue_Icc_hasDerivWithinAt (F := fun t (y : E) => A t y)
    (a := -1) (b := 0) (c := 2) (by norm_num) (by norm_num) hmatch hJbd hJfd
  refine ⟨J, ?_, fun τ hτ => ?_⟩
  · have hJ0 : J 0 = Jb 0 := by rw [hJdef]; simp only [glueAt]; rw [if_pos (le_refl (0 : ℝ))]
    rw [hJ0, hJb0]
  · have hmem : τ ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact (hglue τ hmem).hasDerivAt (Icc_mem_nhds (by linarith [hτ.1]) (by linarith [hτ.2]))

/-- **Two-sided derivative on the open interior.**  On `Ioo 0 1` the within-derivative of the
    generic linear-ODE solution upgrades to a genuine two-sided `HasDerivAt`, since `Icc 0 1` is a
    neighbourhood of every interior point. -/
theorem linODE_exists_hasDerivAt_Ioo (A : ℝ → (E →L[ℝ] E))
    (hA : ContinuousOn A (Set.Icc (0 : ℝ) 1)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt J (A τ (J τ)) τ := by
  obtain ⟨J, hJ0, hJd⟩ := linODE_exists_on_Icc A hA w₀
  exact ⟨J, hJ0, fun τ hτ =>
    (hJd τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)⟩

end LinODE

section GeodesicJacobi

variable {n : ℕ}

/-- **Geodesic Jacobi-field existence over an arbitrary base curve.**  For a continuous phase base
    curve `Ybase` on `[0,1]`, the Jacobi (linearized-geodesic) field
    `J' τ = DF(Ybase τ)·J = fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)` has a solution on `[0,1]`
    with `J 0 = w₀`.  Continuity of the time-dependent operator `A τ = fderiv (geodesicField)(Ybase τ)`
    is DERIVED from `geodesicField ∈ C^∞` (`contDiff_geodesicField` ⇒ `continuous_fderiv`) composed
    with the continuous base curve.  This is the generic-base specialization of `linODE_exists_on_Icc`
    matching the doubled-family supply's linearized-ODE field. -/
theorem geodesicJacobi_exists_on_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase : ℝ → Point n × Point n) (hYbase : ContinuousOn Ybase (Set.Icc (0 : ℝ) 1))
    (w₀ : Point n × Point n) :
    ∃ J : ℝ → Point n × Point n, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt J (fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ))
          (Set.Icc (0 : ℝ) 1) τ := by
  have hcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  set A : ℝ → (Point n × Point n →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Ybase τ) with hAdef
  have hA : ContinuousOn A (Set.Icc (0 : ℝ) 1) := hcont.comp_continuousOn hYbase
  exact linODE_exists_on_Icc A hA w₀

/-- Geodesic Jacobi-field existence, two-sided `HasDerivAt` on the open interior `Ioo 0 1`. -/
theorem geodesicJacobi_exists_hasDerivAt_Ioo (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase : ℝ → Point n × Point n) (hYbase : ContinuousOn Ybase (Set.Icc (0 : ℝ) 1))
    (w₀ : Point n × Point n) :
    ∃ J : ℝ → Point n × Point n, J 0 = w₀ ∧
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt J (fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)) τ := by
  obtain ⟨J, hJ0, hJd⟩ := geodesicJacobi_exists_on_Icc g gi hC Ybase hYbase w₀
  exact ⟨J, hJ0, fun τ hτ =>
    (hJd τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)⟩

/-- **Geodesic Jacobi-field existence with two-sided `HasDerivAt` on the CLOSED `[0,1]`.**  With the
    base curve continuous on the padded `[-1,2]` (available for the confined geodesic phase-flow,
    which exists on `(-2,2)`), the Jacobi field solves `J' τ = fderiv (geodesicField)(Ybase τ)(J τ)`
    on `[0,1]` with genuine two-sided derivatives.  This is exactly the field/derivative shape of the
    doubled-family supply's linearized-ODE binder. -/
theorem geodesicJacobi_exists_hasDerivAt_Icc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (Ybase : ℝ → Point n × Point n) (hYbase : ContinuousOn Ybase (Set.Icc (-1 : ℝ) 2))
    (w₀ : Point n × Point n) :
    ∃ J : ℝ → Point n × Point n, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt J (fderiv ℝ (geodesicField g gi) (Ybase τ) (J τ)) τ := by
  have hcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  set A : ℝ → (Point n × Point n →L[ℝ] Point n × Point n) :=
    fun τ => fderiv ℝ (geodesicField g gi) (Ybase τ) with hAdef
  have hA : ContinuousOn A (Set.Icc (-1 : ℝ) 2) := hcont.comp_continuousOn hYbase
  exact linODE_exists_hasDerivAt_Icc A hA w₀

end GeodesicJacobi

end QIQTH.ExpMap
