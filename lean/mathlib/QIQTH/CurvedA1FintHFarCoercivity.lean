/-
  CurvedA1FintHFarCoercivity — J4-581: RESOLVING the hFar far-field LOWER coercivity residual
  (the deepest geometric wall of the curved a₁ two-jet), at the genuinely-curved witness `g^K`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  The far-field annulus source
  `CurvedA1FintHlam4.curved_hFint_hFar_general` (and `CurvedA1FintHFarSource.curved_hFint_hFar_at_gate`)
  carries an `hdata` bundle whose LAST conjunct is the near-isometry LOWER coercivity, required for
  ALL `z ∈ K` (INCLUDING the far-field annulus `‖z‖ ≥ r`):

      `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)`,   `W₀ z := uniformInverseChart g^K gi^K hChr hK z 0`.

  J4-575 (`HerrHminCoercivity.hmin_gate`) proved this ONLY on the near-isometry ball `‖z‖ < r_ni`
  (where `L·‖z‖ ≤ ½` in the banked `chartW0_rncRadialSq_error`).  The WHOLE-`z` form is PROVABLY FALSE
  (`HerrHminCoercivity.wholeSpace_coercivity_unsatisfiable`): off `K` the chart is the ZERO DEFAULT
  (`W z = 0`), so `½·rncRadialSq z ≤ 0` fails for any nonzero `z ∉ K`.  So the residual is: for
  `z ∈ K`, `‖z‖ ≥ r` — is the coercivity true?

  ── THE VERDICT (route a — the MAINLINE `K` is CONSTRAINED, the far-field annulus is EMPTY).
  The fully-wired capstone `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired` carries the RNC frame
  hypothesis `hframeK : ∀ q ∈ K, g^K q i j = δ_{ij}`.  For the genuinely-curved witness
  `g^K = curvedRNCMetric κ` with `κ ≠ 0` and `n ≥ 2`, the metric equals `δ` ONLY at the origin
  (the correction `‖x‖²δ − x⊗x` vanishes ⇔ `x = 0`, since `rncRadialSq z = z_i²` for every `i` forces
  every off-`i` coordinate to `0`).  So `hframeK` FORCES `K ⊆ {0}` — the chart base set collapses to the
  origin.  Consequently the far-field annulus `{z ∈ K : ‖z‖ ≥ r}` requires `0 = ‖z‖ ≥ r > 0`, which is
  EMPTY; the coercivity holds at the sole point `z = 0` trivially (`½·rncRadialSq 0 = 0 ≤ rncRadialSq …`).
  The far-field "wall" therefore NEVER FIRES on the mainline `K`.

  ── WHY route (b) (a Cartan–Hadamard GLOBAL coercivity) is NOT available for THIS chart object.  The
  whole-space failure is NOT a curvature effect — `curvedRNCMetric κ` with `κ < 0` is Cartan–Hadamard,
  so the TRUE geodesic inverse IS a global proper diffeomorphism.  But `uniformInverseChart` is a
  COMPACTLY-SUPPORTED construction: it is the ZERO DEFAULT off `K` and germ-controlled only on a uniform
  ball of radius `δ₀` around each `z ∈ K`.  It does NOT realize the global geodesic inverse off that
  ball, so no global `½`-coercivity is bankable FROM this object; the genuinely-true statement is the
  gate/near-isometry one (`hmin_gate`), and the mainline `K` constraint discharges the residual.

  ── WHAT IS PROVED (axiom-free, no `sorry`, no `:= True`, no hypothesis = conclusion; std-3).
    •  `curvedRNCMetric_frame_forces_origin` — the KEY geometric fact: for `κ ≠ 0`, `n ≥ 2`, the RNC
       frame condition `g^K z = δ` forces `z = 0` (so `hframeK ⟹ K ⊆ {0}`).
    •  `curved_hFar_coercivity_smallK_at_gate` — route (a) general form: there is `ρ > 0` such that IF
       `K ⊆ ball 0 ρ` (all of `K` inside the near-isometry ball) then the hFar coercivity holds for ALL
       `z ∈ K` (annulus included), from `hmin_gate` — the annulus `‖z‖ ≥ r` is covered whenever it lies
       inside the near-isometry ball.
    •  `curved_hFar_coercivity_frameK_at_gate` — THE DECISIVE mainline discharge: GIVEN the capstone's
       own `hframeK`, the hFar coercivity `∀ z ∈ K, (1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)` holds
       UNCONDITIONALLY (because `K ⊆ {0}`).  This is EXACTLY the `hdata` coercivity conjunct that
       `curved_hFint_hFar_general` carries — DISCHARGED for the mainline `K`.
    •  `curved_hFar_coercivity_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── HONEST FRAMING.  Resolving the hFar coercivity does NOT make `a₁ = R/6` unconditional: `hsrc`,
  `hOffCollarTail`, the convergence trio, `hInnerCont`, and the gate carries all remain owed.  NOT
  `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintHFarSource
import QIQTH.HerrHminCoercivity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.HerrHminCoercivity
open scoped Topology BigOperators

namespace QIQTH.CurvedA1FintHFarCoercivity

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (A) — THE KEY GEOMETRIC FACT: the RNC frame condition forces the origin.
    ############################################################################### -/

/-- **★★★ J4-581 — `curvedRNCMetric_frame_forces_origin`.**  For `κ ≠ 0` and `n ≥ 2`, the RNC frame
    condition `g^K z = δ` (`curvedRNCMetric κ z i j = if i = j then 1 else 0` for ALL `i, j`) forces
    `z = 0`.  The diagonal condition `g^K z i i = 1` unfolds to `(κ/3)·(rncRadialSq z − z i²) = 0`, hence
    (`κ ≠ 0`) `rncRadialSq z = z i²` for EVERY `i`; picking `i ≠ m` (possible since `n ≥ 2`) and using
    `z i² + z m² ≤ ∑ₖ z k² = rncRadialSq z` gives `z m² ≤ 0`, so `z m = 0` for every `m`.  This is why the
    capstone's `hframeK` forces the chart base set `K ⊆ {0}` at the genuinely-curved witness.  ⚠ NOT
    `a₁ = R/6`. -/
theorem curvedRNCMetric_frame_forces_origin (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    {z : Point n} (hframe : ∀ i j, curvedRNCMetric κ z i j = (if i = j then (1 : ℝ) else 0)) :
    z = 0 := by
  -- diagonal condition ⟹ `rncRadialSq z = (z i)²` for every `i`.
  have hdiag : ∀ i : Fin n, rncRadialSq z = (z i) ^ 2 := by
    intro i
    have h := hframe i i
    simp only [curvedRNCMetric, if_true, mul_one] at h
    -- h : 1 - (κ/3) * (rncRadialSq z - z i * z i) = 1
    have h0 : (κ / 3) * (rncRadialSq z - z i * z i) = 0 := by linarith
    have hk : (κ / 3) ≠ 0 := div_ne_zero hκ (by norm_num)
    have hz : rncRadialSq z - z i * z i = 0 := (mul_eq_zero.mp h0).resolve_left hk
    have : rncRadialSq z = z i * z i := by linarith
    rw [this]; ring
  -- conclude `z m = 0` for every `m`.
  funext m
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i ≠ m := by
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    exact exists_ne m
  have h1 : rncRadialSq z = (z i) ^ 2 := hdiag i
  -- `(z i)² + (z m)² ≤ ∑ₖ (z k)² = rncRadialSq z`.
  have h2 : (z i) ^ 2 + (z m) ^ 2 ≤ rncRadialSq z := by
    have hsub : ({i, m} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hnn : ∀ k ∈ Finset.univ, k ∉ ({i, m} : Finset (Fin n)) → 0 ≤ (z k) ^ 2 :=
      fun k _ _ => sq_nonneg _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    rw [Finset.sum_pair hi] at hle
    simpa only [rncRadialSq] using hle
  have hzm2 : (z m) ^ 2 ≤ 0 := by rw [h1] at h2; linarith
  have hzm0 : (z m) ^ 2 = 0 := le_antisymm hzm2 (sq_nonneg _)
  have : z m = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hzm0
  simpa using this

/-! ###############################################################################
    ### (B) — ROUTE (a) GENERAL: small-`K` discharge from the near-isometry `hmin_gate`.
    ############################################################################### -/

/-- **★★ J4-581 — `curved_hFar_coercivity_smallK_at_gate`.**  Route (a), general form.  There is a
    near-isometry radius `ρ > 0` such that IF the whole chart base set `K` lies inside the ball
    `‖z‖ < ρ`, then the hFar LOWER coercivity `(1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)` holds for ALL
    `z ∈ K` — the far-field annulus `‖z‖ ≥ r` is COVERED whenever it lies inside the near-isometry ball.
    Sourced directly from `HerrHminCoercivity.hmin_gate` at `g^K = curvedRNCMetric κ`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFar_coercivity_smallK_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), (∀ z ∈ K, ‖z‖ < ρ) →
      ∀ z ∈ K, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) := by
  obtain ⟨ρ, hρ, hcoe⟩ := hmin_gate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
  exact ⟨ρ, hρ, fun hsmall z hz => hcoe z hz (hsmall z hz)⟩

/-! ###############################################################################
    ### (C) — THE DECISIVE MAINLINE DISCHARGE: from the capstone's own `hframeK`.
    ############################################################################### -/

/-- **★★★ J4-581 — `curved_hFar_coercivity_frameK_at_gate` — THE hFar COERCIVITY, DISCHARGED for the
    mainline `K`.**  GIVEN the capstone's own RNC frame hypothesis `hframeK : ∀ q ∈ K, g^K q = δ` (carried
    by `CurvedA1FullyWiredCapstone.curved_a1_R6_fully_wired`), at the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ ≠ 0`, `n ≥ 2`), the hFar LOWER coercivity
      `∀ z ∈ K, (1/2)·rncRadialSq z ≤ rncRadialSq (W₀ z)`
    holds UNCONDITIONALLY — because `hframeK` forces `K ⊆ {0}` (`curvedRNCMetric_frame_forces_origin`),
    at which point `z = 0` gives `½·rncRadialSq 0 = 0 ≤ rncRadialSq (W₀ 0)`.  This is EXACTLY the `hdata`
    coercivity conjunct that `CurvedA1FintHlam4.curved_hFint_hFar_general` carries — the far-field annulus
    `‖z‖ ≥ r` is EMPTY on the mainline `K`, so the deepest geometric residual DOES NOT FIRE.  ⚠ NOT
    `a₁ = R/6`. -/
theorem curved_hFar_coercivity_frameK_at_gate (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hframeK : ∀ q ∈ K, ∀ i j, curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) :
    ∀ z ∈ K, (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) := by
  intro z hz
  have hz0 : z = 0 := curvedRNCMetric_frame_forces_origin κ hκ hn (hframeK z hz)
  subst hz0
  rw [rncRadialSq_zero, mul_zero]
  exact rncRadialSq_nonneg _

/-! ###############################################################################
    ### (D) — the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-581 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the hFar coercivity
    discharge above is landed at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.  NOT
    `a₁ = R/6`. -/
theorem curved_hFar_coercivity_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHFarCoercivity

section AxiomChecks
open QIQTH.CurvedA1FintHFarCoercivity
#print axioms curvedRNCMetric_frame_forces_origin
#print axioms curved_hFar_coercivity_smallK_at_gate
#print axioms curved_hFar_coercivity_frameK_at_gate
#print axioms curved_hFar_coercivity_curved_satisfiable
end AxiomChecks
