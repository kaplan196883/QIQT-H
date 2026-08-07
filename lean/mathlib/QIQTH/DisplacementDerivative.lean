/-
  QIQTH / HeatResidualBound — DisplacementDerivative.lean   (J4-357, the hdisp campaign)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It discharges `hdisp` — the ONE
  genuinely-new geometric carry of the Sol-#13 matched-pair sliver campaign (J4-354/355/356): the
  BASE-SIDE derivative control of the chart-centre displacement `b(z) := (W z 0) + z`, namely
      `‖Db(z)‖ ≤ C'·‖z‖`   on a gate ball,
  which feeds (a) the O4 conditional `SliverOffCollarMatched.cubic_contact_gradient_bound` (its `hu`/`hw`
  contraction hypotheses) and (b) the collar Lipschitz `Lip(ρ·A_chart)`.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ THE D1 RECON VERDICT (the carry was NEARLY BANKED — it is now closed unconditionally).

  Write `Wbv z := uniformInverseChart g gi hC hK z 0` (the base-varying chart at the centre) and the
  displacement `b(z) := Wbv z + z`.  Three banked facts assemble the derivative bound with NO new
  regularity input beyond the standing geometry `(hC, hK, K ∈ 𝓝 0)`:

    (i)  ★ THE 1-JET, BANKED.  `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center`:
             `HasFDerivAt Wbv (−id) 0`   (derivative `ContinuousLinearEquiv.neg ℝ`, i.e. `−id`),
         DERIVED unconditionally from the banked quadratic displacement `‖Wbv z + z‖ ≤ C_W‖z‖²`
         (`chartW0_displacement`) — literally the little-o statement of `HasFDerivAt Wbv (−id) 0`.
         Hence `Db(0) = fderiv Wbv 0 + id = (−id) + id = 0` — the displacement is a genuine `o(‖z‖)`.

    (ii) ★ THE C², BANKED.  `TerminalVelC2.terminalVel0_contDiffAt_two` (route (a): geodesic
         homogeneity, `terminalVel0 v = fderiv(uniformFlowExp 0) v [v]`, `C⁴→C³→C²`) feeds
         `GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt` (the reversal identity
         `Wbv =ᶠ −T₀∘(U 0 ·)`), giving `ContDiffAt ℝ 2 Wbv 0` — hence `ContDiffAt ℝ 2 b 0`.

    (iii) THE C²-MODULUS.  `ContDiffAt ℝ 2 b 0` ⟹ `fderiv b` is `ContDiffAt ℝ 1` at `0`
         (`ContDiffAt.fderiv_right`) ⟹ `fderiv b` is locally Lipschitz
         (`ContDiffAt.exists_lipschitzOnWith`): `∃ K r>0, ∀ z∈ball 0 r, dist (Db z)(Db 0) ≤ K·dist z 0`.
         With `Db 0 = 0` (i) this is `‖Db z‖ ≤ K·‖z‖`.  ✓

  So the "was never established" base-side C¹ residue flagged in `SliverOffCollarMatched`'s O4 verdict
  is in fact CLOSED: the 1-jet `Db(0) = 0` is banked, and the linear-in-`‖z‖` derivative modulus is the
  standard C²-Lipschitz-derivative fact.  `hdisp` is RESOLVED.  ⚠ NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  DELIVERABLES.
    (D1) `contDiffAt_two_fderiv_sub_zero_bound` — the abstract C²-modulus: `ContDiffAt ℝ 2 f 0` ⟹
         `‖fderiv f z − fderiv f 0‖ ≤ K·‖z‖` on a ball (the genuine new analytic content).
         `displacement_deriv_bound` — ★ the concrete `hdisp`: `‖Db(z)‖ ≤ C'·‖z‖` on a gate ball, with
         `Db(0) = 0` supplied by the banked 1-jet.
    (D2) `cubic_contact_gradient_concrete` — the O4 conditional lemma's conclusion with the `hu`/`hw`
         contraction hypotheses DISCHARGED from a linear-operator bound `‖A‖ ≤ C_E·‖z‖` (the shape D1
         produces): `‖∇(r_z − r_{W z 0})‖ ≤ (2C_W + 2C_E + 2C_E C_W r₀)·‖z‖²`.
    (D3) `collar_product_lipschitz_increment` — the algebraic core of Sol's `Lip(ρ·A_chart)` formula
         `Lip(f·g) ≤ M_f·L_g + M_g·L_f` (honest partial; the A_chart Lipschitz constant `L_g` is the
         remaining named data carry).

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.TerminalVelC2
import QIQTH.SliverOffCollarMatched

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound
open QIQTH.SliverOffCollarMatched
open scoped Topology

namespace QIQTH.DisplacementDerivative

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    (D1a) — the abstract C²-modulus (the derivative is Lipschitz-at-0).
    ############################################################################### -/

/-- **(D1a) `contDiffAt_two_fderiv_sub_zero_bound`.**  THE C²-MODULUS.  For any `f : E → F` that is
    `ContDiffAt ℝ 2` at `0`, the Fréchet derivative `fderiv f` is locally Lipschitz at `0`
    (`ContDiffAt.exists_lipschitzOnWith`, since `fderiv f` is `ContDiffAt ℝ 1` at `0` via
    `ContDiffAt.fderiv_right`), so on some ball
      `‖fderiv f z − fderiv f 0‖ ≤ K·‖z‖`.
    This is the standard "second-order Taylor ⟹ derivative is Lipschitz" fact, the analytic core of the
    displacement-derivative bound.  ⚠ NOT `a₁ = R/6`. -/
theorem contDiffAt_two_fderiv_sub_zero_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ r > (0 : ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖z‖ < r →
      ‖fderiv ℝ f z - fderiv ℝ f 0‖ ≤ K * ‖z‖ := by
  have hg1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := hg1.exists_lipschitzOnWith
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨r, hr, (K : ℝ), K.coe_nonneg, ?_⟩
  intro z hz
  have hzt : z ∈ t := hrsub (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have h0t : (0 : E) ∈ t := hrsub (Metric.mem_ball_self hr)
  have hd := hlip.dist_le_mul z hzt 0 h0t
  rwa [dist_eq_norm, dist_zero_right] at hd

/-! ###############################################################################
    (D1) — ★ the concrete displacement-derivative bound `hdisp`.
    ############################################################################### -/

/-- **(D1) ★★★ `displacement_deriv_bound` — the `hdisp` carry, CLOSED.**  For the base-varying chart
    displacement `b(z) := uniformInverseChart g gi hC hK z 0 + z` there is a gate ball and constant
    `C' ≥ 0` with
      `‖fderiv b z‖ ≤ C'·‖z‖`   for `‖z‖ < r`.
    Route: `b` is `ContDiffAt ℝ 2` at `0` (`terminalVel0_contDiffAt_two` ⟹
    `hbaseC2_of_terminalVel_contDiffAt`, plus `contDiffAt_id`), so `fderiv b` is Lipschitz-at-`0`
    (D1a); and the banked 1-jet `baseVaryingChart_hasFDerivAt_center` gives `fderiv Wbv 0 = −id`, hence
    `fderiv b 0 = (−id) + id = 0`, turning the increment `‖Db z − Db 0‖ ≤ C'‖z‖` into `‖Db z‖ ≤ C'‖z‖`.
    This is exactly the derivative-level displacement control demanded by the O4 verdict of
    `SliverOffCollarMatched`.  ⚠ NOT `a₁ = R/6`. -/
theorem displacement_deriv_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ z : Point n, ‖z‖ < r →
      ‖fderiv ℝ (fun w => uniformInverseChart g gi hC hK w 0 + w) z‖ ≤ C' * ‖z‖ := by
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  set b : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 + z with hbdef
  -- (ii) `Wbv` is `C²` at `0`, hence `b = Wbv + id` is `C²` at `0`.
  have hWbvC2 : ContDiffAt ℝ 2 Wbv 0 :=
    QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem
      (QIQTH.TerminalVelC2.terminalVel0_contDiffAt_two g gi hC hK (mem_of_mem_nhds h0Kmem))
  have hbC2 : ContDiffAt ℝ 2 b 0 := hWbvC2.add contDiffAt_id
  -- (i) the banked 1-jet ⟹ `fderiv b 0 = 0`.
  have hWbv' : HasFDerivAt Wbv
      ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n) 0 :=
    QIQTH.BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hsum : ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      + ContinuousLinearMap.id ℝ (Point n) = 0 := by
    ext x; simp
  have hb' : HasFDerivAt b (0 : Point n →L[ℝ] Point n) 0 := by
    have h := hWbv'.add (hasFDerivAt_id (0 : Point n))
    rwa [hsum] at h
  have hfderiv0 : fderiv ℝ b 0 = 0 := hb'.fderiv
  -- (iii) the C²-modulus, specialised with `fderiv b 0 = 0`.
  obtain ⟨r, hr, C', hC'nn, hbound⟩ := contDiffAt_two_fderiv_sub_zero_bound b hbC2
  refine ⟨r, hr, C', hC'nn, ?_⟩
  intro z hz
  have := hbound z hz
  rwa [hfderiv0, sub_zero] at this

/-! ###############################################################################
    (D2) — the O4 cubic-contact gradient, discharged from the D1 operator bound.
    ############################################################################### -/

/-- **(D2) `cubic_contact_gradient_concrete`.**  The O4 conditional lemma
    `SliverOffCollarMatched.cubic_contact_gradient_bound`, with its abstract `hu`/`hw` contraction
    hypotheses DISCHARGED from a single linear-operator bound `‖A‖ ≤ C_E·‖z‖` — exactly the shape that
    (D1) `displacement_deriv_bound` produces for `A = Db(z)` (or its transpose).  With the exact O4
    gradient decomposition `grad = 2•b + 2•(A z) + 2•(A b)` (the roles `u := A z`, `w := A b` of the
    van-Vleck radial-defect gradient `∇(r_z − r_{W z 0}) = 2b + 2(Db)ᵀz − 2(Db)ᵀb`, signs absorbed
    into `A`), the operator-norm inequality `‖A x‖ ≤ ‖A‖·‖x‖` gives `‖A z‖ ≤ C_E‖z‖·‖z‖` and
    `‖A b‖ ≤ C_E‖z‖·‖b‖`, so the cubic contact follows:
      `‖grad‖ ≤ (2C_W + 2C_E + 2C_E C_W r₀)·‖z‖²`.
    Non-vacuous (constrains `grad`), satisfiable (`A = 0`, `b = grad = 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem cubic_contact_gradient_concrete (z b grad : Point n) (A : Point n →L[ℝ] Point n)
    (C_W C_E r₀ : ℝ) (hCW : 0 ≤ C_W) (hCE : 0 ≤ C_E) (hr0 : 0 ≤ r₀) (hzr : ‖z‖ ≤ r₀)
    (hb : ‖b‖ ≤ C_W * ‖z‖ ^ 2) (hA : ‖A‖ ≤ C_E * ‖z‖)
    (hgrad : grad = (2 : ℝ) • b + (2 : ℝ) • (A z) + (2 : ℝ) • (A b)) :
    ‖grad‖ ≤ (2 * C_W + 2 * C_E + 2 * C_E * C_W * r₀) * ‖z‖ ^ 2 := by
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hu : ‖A z‖ ≤ C_E * ‖z‖ * ‖z‖ := by
    calc ‖A z‖ ≤ ‖A‖ * ‖z‖ := A.le_opNorm z
      _ ≤ C_E * ‖z‖ * ‖z‖ := by gcongr
  have hw : ‖A b‖ ≤ C_E * ‖z‖ * ‖b‖ := by
    calc ‖A b‖ ≤ ‖A‖ * ‖b‖ := A.le_opNorm b
      _ ≤ C_E * ‖z‖ * ‖b‖ := by gcongr
  exact cubic_contact_gradient_bound z b (A z) (A b) grad C_W C_E r₀
    hCW hCE hr0 hzr hb hu hw hgrad

/-! ###############################################################################
    (D3) — the collar product-Lipschitz increment (Sol's `Lip(ρ·A_chart)` core).
    ############################################################################### -/

/-- **(D3) `collar_product_lipschitz_increment`.**  THE ALGEBRAIC CORE of Sol's collar-Lipschitz
    formula `Lip(ρ·A_chart) ≤ M_ρ·L_A + M_A·L_ρ`.  For real-valued `f, g` (the roles of `ρ` and the
    chart amplitude `A_chart`) with `|f z| ≤ M_f`, `|g w| ≤ M_g` and Lipschitz increments
    `|f z − f w| ≤ L_f·dist z w`, `|g z − g w| ≤ L_g·dist z w`,
      `|f z·g z − f w·g w| ≤ (M_f·L_g + M_g·L_f)·dist z w`.
    Route: `f z g z − f w g w = f z (g z − g w) + (f z − f w) g w` + triangle + `mul_le_mul`.  The
    remaining named DATA carry for the concrete collar is `L_g = L_{A_chart}` (the chart-amplitude
    Lipschitz constant on the compact gate, from the banked `C¹` amplitude jets); `L_f = L_ρ` is Sol's
    `K·C_r·c²/4` (from the D2 gradient bound via `ρ = e^{Δr/(4τ)}`).  Honest partial for D3.
    ⚠ NOT `a₁ = R/6`. -/
theorem collar_product_lipschitz_increment
    (f g : Point n → ℝ) (M_f M_g L_f L_g : ℝ) (z w : Point n)
    (hMfnn : 0 ≤ M_f) (hMgnn : 0 ≤ M_g)
    (hMf : |f z| ≤ M_f) (hMg : |g w| ≤ M_g)
    (hLf : |f z - f w| ≤ L_f * dist z w) (hLg : |g z - g w| ≤ L_g * dist z w) :
    |f z * g z - f w * g w| ≤ (M_f * L_g + M_g * L_f) * dist z w := by
  have h1 : |f z| * |g z - g w| ≤ M_f * (L_g * dist z w) :=
    mul_le_mul hMf hLg (abs_nonneg _) hMfnn
  have h2 : |f z - f w| * |g w| ≤ (L_f * dist z w) * M_g :=
    mul_le_mul hLf hMg (abs_nonneg _) (le_trans (abs_nonneg _) hLf)
  calc |f z * g z - f w * g w|
      ≤ |f z * (g z - g w)| + |(f z - f w) * g w| := by
        rw [show f z * g z - f w * g w = f z * (g z - g w) + (f z - f w) * g w from by ring]
        exact abs_add_le _ _
    _ = |f z| * |g z - g w| + |f z - f w| * |g w| := by rw [abs_mul, abs_mul]
    _ ≤ M_f * (L_g * dist z w) + (L_f * dist z w) * M_g := add_le_add h1 h2
    _ = (M_f * L_g + M_g * L_f) * dist z w := by ring

end QIQTH.DisplacementDerivative

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DisplacementDerivative.contDiffAt_two_fderiv_sub_zero_bound
#print axioms QIQTH.DisplacementDerivative.displacement_deriv_bound
#print axioms QIQTH.DisplacementDerivative.cubic_contact_gradient_concrete
#print axioms QIQTH.DisplacementDerivative.collar_product_lipschitz_increment
