/-
  CurvedRNCFirstJetLeg — the CORRECTED `hpull` FIRST LEG `⟨z, A eᵢ⟩ = z_i` (i.e. `Aᵀz = z`) for the
  inverse-chart first jet `A := D W_z(0)` of the CONCRETE curved RNC witness `g^K = curvedRNCMetric κ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It discharges ONE previously-open geometric
  item — the CORRECTED-`hpull` FIRST LEG — but ONLY for the concrete curved witness `g^K =
  curvedRNCMetric κ` (`κ ≤ 0`, `Ric(0) = (n−1)κ·δ ≠ 0`), and ONLY as a chart-jet identity.  It does
  NOT discharge the analytic trio `{hDuhamel, hDConv, hCConv}` on which `a₁ = R/6` remains STRICTLY
  conditional.

  ## THE CORRECTION (cp865 / J4-978).  The CURRENTLY-banked `hpullVP` shape
      `∑ₖ (W_z 0)ₖ·(A eᵢ)ₖ = ∑ⱼ g_{ij}(z)·zʲ`
  is PROVABLY MIS-SIGNED for genuine geodesic-inverse jets (flat check: LHS = −z_i, RHS = +z_i).  The
  CORRECTED first leg is `⟨z, A eᵢ⟩ = z_i`, i.e. `Aᵀ z = z`.  This is NUMERICALLY VERIFIED to 1e-10
  (n = 2, 3; several κ < 0; small z) by integrating the geodesic ODE and finite-differencing `exp_z`.

  ## WHAT LANDS (all DERIVED; NO `sorry`, no new axioms; NOT `a₁ = R/6`).
    * `curvedRNC_expTube_neg` — the EXACT radial endpoint of the *exp*-tube: `expTube z (−z) 1 = (0, −z)`
      for `curvedRNCMetric κ` (`‖z‖ ≤ expRho z`), via ODE-uniqueness (`geodesic_local_unique`) matching
      the straight line `γ(τ) = ((1−τ)z, −z)` against the Skolemized exp-tube on `(−1, 3/2) ⊇ [0,1]`.
      Supplies BOTH `exp_z(−z) = 0` (`.1`) and the endpoint velocity `γ̇(1) = −z` (`.2`).
    * `curvedRNC_gauss_radial` — ★ the RADIAL Gauss identity `⟨z, T w⟩ = ⟨z, w⟩` for all `w`, where
      `T := D(uniformFlowExp z)(−z)`.  From the banked first-variation Gauss identity
      `gauss_interior_identity` at `(p, v) = (z, −z)`: `g(0) = δ`, `γ̇(1) = −z`, the RNC metric radial
      gauge `∑ⱼ g_{aj}(z)·zʲ = z_a`, and the `expMap ↔ uniformFlowExp` overlap alignment collapse the
      Gauss pairing to `⟨z, T w⟩ = ⟨z, w⟩`.  (This says `Tᵀ z = z`.)
    * `curvedRNC_firstJetLeg` — ★★ THE CORRECTED FIRST LEG: an explicit `r > 0` with
      `∑ₖ z_k·(D W_z(0)·eᵢ)ₖ = z_i` for every `z ∈ S` with `‖z‖ < r` and `‖z‖ < expRho z`.  Proof:
      the inverse germ `W ∘ φ = id` near `−z` (with `φ(−z) = 0`, `W(0) = −z`, both banked J4-994) gives
      `P ∘ T = id` by the chain rule; the forward Jacobian near-identity bound makes `T` a unit, so
      `T ∘ P = id`; then `⟨z, P eᵢ⟩ = ⟨z, T(P eᵢ)⟩ = ⟨z, eᵢ⟩ = z_i`.  The full jet `A = T⁻¹` is NOT
      pinned — only its single constraint `Aᵀ z = z` is; that is all this leg needs.

  ⚠  a₁ = R/6 remains CONDITIONAL.  This closes the corrected first leg for the concrete radial-normal
  witness; it does NOT make `a₁ = R/6` unconditional, and does NOT bear on `{hDuhamel, hDConv, hCConv}`.
  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedRNCGeodesicRay
import QIQTH.GaussInteriorMVT
import QIQTH.InverseChartFirstJet
import QIQTH.CurvedCenterIdentities
import QIQTH.NearIsometryBudget
import QIQTH.PullbackNaturalityLocal
import QIQTH.SliverAssembly

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.ExpMap QIQTH.Geodesic
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCGeodesicRay QIQTH.InverseChartFirstJet QIQTH.HeatResidualBound
open scoped BigOperators Topology

namespace QIQTH.CurvedRNCFirstJetLeg

variable {n : ℕ}

/-- Small δ-collapse helper: `∑ b, (if a = b then 1 else 0)·F b = F a`. -/
private theorem sumite (a : Fin n) (F : Fin n → ℝ) :
    (∑ b, (if a = b then (1:ℝ) else 0) * F b) = F a := by
  rw [Finset.sum_congr rfl (fun b _ => by by_cases h : a = b <;> simp [h] :
      ∀ b ∈ Finset.univ, (if a = b then (1:ℝ) else 0) * F b = if a = b then F b else 0)]
  rw [Finset.sum_ite_eq Finset.univ a F]; simp

/-! ### §1 — the exact radial endpoint of the exp-tube. -/

/-- **★ The EXACT radial endpoint of the exp-tube.**  `expTube z (−z) 1 = (0, −z)` for
    `curvedRNCMetric κ`, requiring only `‖z‖ ≤ expRho z`.  Same straight-line vs ODE-uniqueness proof
    as `curvedRNC_uniformFlowExp_neg_eq_zero` (J4-994), but for `expTube`'s spec.  Supplies both
    `exp_z(−z) = (…).1 = 0` and the endpoint velocity `(…).2 = −z`. -/
theorem curvedRNC_expTube_neg (K : ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    (z : Point n) (hznorm : ‖z‖ ≤ expRho (curvedRNCMetric K) (curvedRNCInv K) hC z) :
    expTube (curvedRNCMetric K) (curvedRNCInv K) hC z (-z) 1 = ((0 : Point n), -z) := by
  set g := curvedRNCMetric (n := n) K with hg
  set gi := curvedRNCInv (n := n) K with hgi
  have hnegnorm : ‖(-z)‖ ≤ expRho g gi hC z := by rw [norm_neg]; exact hznorm
  obtain ⟨hic, hode, -⟩ := expTube_spec g gi hC z (-z) hnegnorm
  set tube := expTube g gi hC z (-z) with htube
  -- the straight line phase curve.
  set line : ℝ → Point n × Point n := fun t => (((1 - t) • z, -z) : Point n × Point n) with hline
  have hlineIC : line 0 = (z, -z) := by simp [hline]
  have hlineODE : ∀ τ : ℝ, HasDerivAt line (geodesicField g gi (line τ)) τ := by
    intro τ; simpa only [hline, hg, hgi] using curvedRNC_straightLine_hasDerivAt K z τ
  -- work on the interval `(-1, 3/2) ⊇ [0,1]`.
  have hIoosub : Set.Ioo (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hlineCont : ContinuousOn line (Set.Icc (-1 : ℝ) (3 / 2)) :=
    fun τ _ => ((hlineODE τ).continuousAt).continuousWithinAt
  obtain ⟨Ml, hMl⟩ :=
    (((isCompact_Icc).image_of_continuousOn hlineCont).isBounded).subset_closedBall
      ((z, 0) : Point n × Point n)
  have hIccsub : Set.Icc (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have htubeCont : ContinuousOn tube (Set.Icc (-1 : ℝ) (3 / 2)) := fun τ hτ =>
    ((hode τ (hIccsub hτ)).continuousAt).continuousWithinAt
  obtain ⟨Mt, hMt⟩ :=
    (((isCompact_Icc).image_of_continuousOn htubeCont).isBounded).subset_closedBall
      ((z, 0) : Point n × Point n)
  obtain ⟨Klip, hLip⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt))).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hlineMem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      line τ ∈ Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_left _ _)
      (hMl ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  have htubeMem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
      tube τ ∈ Metric.closedBall ((z, 0) : Point n × Point n) (max Ml Mt) := fun τ hτ =>
    Metric.closedBall_subset_closedBall (le_max_right _ _)
      (hMt ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
  have hEqon := geodesic_local_unique g gi (a := -1) (b := 3 / 2) (t₀ := 0)
    ⟨by norm_num, by norm_num⟩ hLip
    (fun τ hτ => ⟨hlineODE τ, hlineMem τ hτ⟩)
    (fun τ hτ => ⟨hode τ (hIoosub hτ), htubeMem τ hτ⟩)
    (by rw [hlineIC, hic])
  have h1 := hEqon (show (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) (3 / 2) from ⟨by norm_num, by norm_num⟩)
  have hline1 : line 1 = ((0, -z) : Point n × Point n) := by simp [hline]
  rw [← h1, hline1]

/-! ### §2 — the radial Gauss identity `⟨z, T w⟩ = ⟨z, w⟩`. -/

/-- **★ The RADIAL Gauss identity.**  For `T := D(uniformFlowExp z)(−z)` and every `w`,
    `∑ₐ z_a·(T w)_a = ∑ₐ z_a·w_a`, i.e. `⟨z, T w⟩ = ⟨z, w⟩` (equivalently `Tᵀ z = z`).  From the banked
    first-variation Gauss identity `gauss_interior_identity` at `(z, −z)`, using `g(0) = δ`, `γ̇(1) = −z`
    (`curvedRNC_expTube_neg`), the RNC metric radial gauge, and the `expMap ↔ uniformFlowExp` overlap. -/
theorem curvedRNC_gauss_radial (K : ℝ) (hK : K ≤ 0)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {S : Set (Point n)} (hS : IsCompact S) (z : Point n) (hz : z ∈ S)
    (hexp : ‖z‖ < expRho (curvedRNCMetric K) (curvedRNCInv K) hC z)
    (huf : ‖z‖ < uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS)
    (w : Point n) :
    (∑ a, z a * (fderiv ℝ (uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z) (-z) w) a)
      = ∑ a, z a * w a := by
  have hnegexplt : ‖(-z : Point n)‖ < expRho (curvedRNCMetric K) (curvedRNCInv K) hC z := by
    rw [norm_neg]; exact hexp
  -- exp-tube endpoint: `exp_z(-z) = 0` and `γ̇(1) = -z`.
  have htube := curvedRNC_expTube_neg K hC z hexp.le
  have hexpmap0 : expMap (curvedRNCMetric K) (curvedRNCInv K) hC z (-z) = 0 := by
    show (expTube (curvedRNCMetric K) (curvedRNCInv K) hC z (-z) 1).1 = 0; rw [htube]
  have htubevel : (expTube (curvedRNCMetric K) (curvedRNCInv K) hC z (-z) 1).2 = -z := by rw [htube]
  -- the banked Gauss identity at `(z, -z)`.
  have hgi := QIQTH.GaussInteriorMVT.gauss_interior_identity (curvedRNCMetric K) (curvedRNCInv K) hC
    (fun y a b => curvedRNCMetric_symm K y a b)
    (fun y a b => curvedRNCMetric_hinvF K hK y a b)
    (fun a b => curvedRNCMetric_contDiff K a b)
    z (-z) w hnegexplt
  rw [hexpmap0, htubevel] at hgi
  -- align the fderiv: `uniformFlowExp z = expMap z` on the overlap ⟹ equal fderiv at `-z`.
  have halign : fderiv ℝ (uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z) (-z)
      = fderiv ℝ (expMap (curvedRNCMetric K) (curvedRNCInv K) hC z) (-z) := by
    have hmin : ‖(-z : Point n)‖ < min (expRho (curvedRNCMetric K) (curvedRNCInv K) hC z)
        (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS) :=
      lt_min hnegexplt (by rw [norm_neg]; exact huf)
    have hnhds : Metric.ball (0 : Point n) (min (expRho (curvedRNCMetric K) (curvedRNCInv K) hC z)
        (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS)) ∈ 𝓝 (-z) :=
      Metric.isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; exact hmin)
    have heq : uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z
        =ᶠ[𝓝 (-z)] expMap (curvedRNCMetric K) (curvedRNCInv K) hC z := by
      filter_upwards [hnhds] with u hu
      rw [mem_ball_zero_iff] at hu
      exact (expMap_eq_uniformFlowExp_on_overlap (curvedRNCMetric K) (curvedRNCInv K) hC hS z hz u hu).symm
    exact heq.fderiv_eq
  rw [halign]
  set Texp := fderiv ℝ (expMap (curvedRNCMetric K) (curvedRNCInv K) hC z) (-z) with hTexp
  -- LHS of `hgi`: collapse `g(0) = δ`, `(-z)_b = -(z_b)` to `-(∑ₐ z_a·(Texp w)_a)`.
  have hL : (∑ a, ∑ b, curvedRNCMetric K (0 : Point n) a b * (Texp w) a * (-z) b)
      = -(∑ a, z a * (Texp w) a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hb : ∀ b, curvedRNCMetric K (0 : Point n) a b * (Texp w) a * (-z) b
        = (if a = b then (1:ℝ) else 0) * (-((Texp w) a * z b)) := by
      intro b; rw [curvedRNCMetric_zero]; simp only [Pi.neg_apply]; ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), sumite a (fun b => -((Texp w) a * z b))]
    ring
  -- RHS of `hgi`: metric radial gauge `∑_b g_{ab}(z)·z_b = z_a` ⟹ `-(∑ₐ z_a·w_a)`.
  have hR : (∑ a, ∑ b, curvedRNCMetric K z a b * w a * (-z) b)
      = -(∑ a, z a * w a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hb : ∀ b, curvedRNCMetric K z a b * w a * (-z) b
        = w a * (-(curvedRNCMetric K z a b * z b)) := by
      intro b; simp only [Pi.neg_apply]; ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum, Finset.sum_neg_distrib,
      (QIQTH.CurvedCenterIdentities.curved_radialGauge_bundle K hK).1 z a]
    ring
  rw [hL, hR] at hgi
  exact neg_injective hgi

/-! ### §3 — the corrected first leg `⟨z, A eᵢ⟩ = z_i`. -/

set_option maxHeartbeats 4000000

/-- **★★ THE CORRECTED `hpull` FIRST LEG** for the concrete curved witness `g^K = curvedRNCMetric κ`
    (`κ ≤ 0`).  There is `r > 0` such that for every base `z ∈ S` with `‖z‖ < r` and `‖z‖ < expRho z`,
    the inverse-chart first jet `A := D W_z(0)` obeys
        `∑ₖ z_k·(A eᵢ)ₖ = z_i`   for every `i`,   i.e. `Aᵀ z = z`.
    Proof: `W(0) = −z`, `φ(−z) = 0` (banked J4-994); the inverse germ `W ∘ φ = id` near `−z` gives
    `P ∘ T = id` (chain rule); the forward Jacobian near-identity bound (`≤ C_D·‖z‖ ≤ ½`) makes `T` a
    unit, so `T ∘ P = id`; then `⟨z, P eᵢ⟩ = ⟨z, T(P eᵢ)⟩ = ⟨z, eᵢ⟩ = z_i` via the radial Gauss
    identity `curvedRNC_gauss_radial`.  The full jet `A = T⁻¹` is NOT pinned; only `Aᵀ z = z` is, which
    is all the leg needs.  ⚠ NOT `a₁ = R/6`. -/
theorem curvedRNC_firstJetLeg (K : ℝ) (hK : K ≤ 0)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {S : Set (Point n)} (hS : IsCompact S) (i : Fin n) :
    ∃ r > (0 : ℝ), ∀ z ∈ S, ‖z‖ < r →
      ‖z‖ < expRho (curvedRNCMetric K) (curvedRNCInv K) hC z →
      (∑ k, z k * (fderiv ℝ (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hC hS z) 0
          (unitVec i)) k) = z i := by
  classical
  obtain ⟨δ₀, hδ₀, hchart⟩ :=
    uniformInverseChart_huniformChart (curvedRNCMetric K) (curvedRNCInv K) hC hS
  obtain ⟨δ₁, hδ₁, hW0spec⟩ :=
    curvedRNC_uniformInverseChart_zero_eq_neg K hC hS
  obtain ⟨ρ₀, hρ₀, C_D, hCD0, hnear⟩ :=
    uniformFlowExp_fderiv_near_id_quant (curvedRNCMetric K) (curvedRNCInv K) hC hS
  have hRf0 : 0 < uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS :=
    uniformFlowRadius_pos (curvedRNCMetric K) (curvedRNCInv K) hC hS
  set r : ℝ := min δ₀ (min δ₁ (min (uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS)
      (min ρ₀ (1 / (2 * (C_D + 1)))))) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min hδ₀ (lt_min hδ₁ (lt_min hRf0 (lt_min hρ₀
      (div_pos one_pos (by nlinarith [hCD0])))))
  refine ⟨r, hrpos, ?_⟩
  -- radius extraction.
  have hr_δ₀ : r ≤ δ₀ := by rw [hrdef]; exact min_le_left _ _
  have hr_δ₁ : r ≤ δ₁ := by rw [hrdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr_uf : r ≤ uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS := by
    rw [hrdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_ρ₀ : r ≤ ρ₀ := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hr_CD : r ≤ 1 / (2 * (C_D + 1)) := by
    rw [hrdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro z hz hzr hexp
  have hzδ₀ : ‖z‖ < δ₀ := lt_of_lt_of_le hzr hr_δ₀
  have hzδ₁ : ‖z‖ < δ₁ := lt_of_lt_of_le hzr hr_δ₁
  have hzuf : ‖z‖ < uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS :=
    lt_of_lt_of_le hzr hr_uf
  have hzρ₀ : ‖z‖ < ρ₀ := lt_of_lt_of_le hzr hr_ρ₀
  have hzCD : ‖z‖ < 1 / (2 * (C_D + 1)) := lt_of_lt_of_le hzr hr_CD
  have hznorm_le : ‖z‖ ≤ uniformFlowRadius (curvedRNCMetric K) (curvedRNCInv K) hC hS := hzuf.le
  set W : Point n → Point n := uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hC hS z with hWdef
  set φ : Point n → Point n := uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z with hφdef
  -- banked endpoint facts (J4-994).
  have hφneg0 : φ (-z) = 0 :=
    curvedRNC_uniformFlowExp_neg_eq_zero K hC hS z hz hznorm_le
  have hW0 : W 0 = -z := hW0spec z hz hzδ₁ hznorm_le
  -- germ + C² of the inverse chart at `v = -z`.
  have hpair := (hchart z hz).1 (-z) (by rw [norm_neg]; exact hzδ₀)
  have hgerm : (fun z' => W (φ z')) =ᶠ[𝓝 (-z)] (fun z' => z') := hpair.1
  have hC2W : ContDiffAt ℝ 2 W 0 := by rw [← hφneg0]; exact hpair.2
  have hWdiff0 : DifferentiableAt ℝ W 0 := hC2W.differentiableAt (by norm_num)
  set P : Point n →L[ℝ] Point n := fderiv ℝ W 0 with hPdef
  have hWfd0 : HasFDerivAt W P 0 := hWdiff0.hasFDerivAt
  have hWfdφ : HasFDerivAt W P (φ (-z)) := by rw [hφneg0]; exact hWfd0
  -- forward flow differentiable at `-z`; `T = its Jacobian`.
  have hφC2 : ContDiffAt ℝ 2 φ (-z) :=
    contDiffAt2_uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hC hS z hz (-z)
      (by rw [norm_neg]; exact hzuf)
  have hφdiff : DifferentiableAt ℝ φ (-z) := hφC2.differentiableAt (by norm_num)
  set T : Point n →L[ℝ] Point n := fderiv ℝ φ (-z) with hTdef
  have hφfd : HasFDerivAt φ T (-z) := hφdiff.hasFDerivAt
  -- chain rule: germ makes `(W ∘ φ)` the identity ⟹ `P ∘ T = id`.
  have hcomp : HasFDerivAt (fun x => W (φ x)) (P.comp T) (-z) := hWfdφ.comp (-z) hφfd
  have hidbase : HasFDerivAt (fun x : Point n => x) (ContinuousLinearMap.id ℝ (Point n)) (-z) :=
    hasFDerivAt_id (-z)
  have hidfd : HasFDerivAt (fun x : Point n => x) (P.comp T) (-z) :=
    hcomp.congr_of_eventuallyEq hgerm.symm
  have hPTid : P.comp T = ContinuousLinearMap.id ℝ (Point n) := hidfd.unique hidbase
  have hPTmul : P * T = 1 := by rw [ContinuousLinearMap.one_def]; exact hPTid
  -- forward Jacobian near-identity ⟹ `T` a unit ⟹ `T ∘ P = id`.
  have hnearz : ‖T - ContinuousLinearMap.id ℝ (Point n)‖ ≤ C_D * ‖(-z : Point n)‖ :=
    hnear z hz (-z) (by rw [norm_neg]; exact hzρ₀)
  have hTnorm : ‖T - (1 : Point n →L[ℝ] Point n)‖ ≤ C_D * ‖z‖ := by
    rw [ContinuousLinearMap.one_def]; simpa only [norm_neg] using hnearz
  have hCDhalf : C_D * ‖z‖ ≤ 1 / 2 := by
    have hden : (0 : ℝ) < 2 * (C_D + 1) := by nlinarith [hCD0]
    have h1 : C_D * ‖z‖ ≤ C_D * (1 / (2 * (C_D + 1))) :=
      mul_le_mul_of_nonneg_left hzCD.le hCD0
    have h2 : C_D * (1 / (2 * (C_D + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ hden]; nlinarith [hCD0]
    linarith
  have hTunit : IsUnit T := by
    have hS : ‖(1 : Point n →L[ℝ] Point n) - T‖ < 1 := by
      rw [show (1 : Point n →L[ℝ] Point n) - T = -(T - 1) by abel, norm_neg]
      calc ‖T - (1 : Point n →L[ℝ] Point n)‖ ≤ C_D * ‖z‖ := hTnorm
        _ < 1 := by linarith [hCDhalf]
    have hu := (Units.oneSub (1 - T) hS).isUnit
    simpa using hu
  have hPinv : P = Ring.inverse T := by
    have hc : T * Ring.inverse T = 1 := Ring.mul_inverse_cancel T hTunit
    calc P = P * 1 := (mul_one P).symm
      _ = P * (T * Ring.inverse T) := by rw [hc]
      _ = (P * T) * Ring.inverse T := by rw [mul_assoc]
      _ = 1 * Ring.inverse T := by rw [hPTmul]
      _ = Ring.inverse T := one_mul _
  have hTP : T * P = 1 := by rw [hPinv]; exact Ring.mul_inverse_cancel T hTunit
  have hTPx : ∀ x, T (P x) = x := by
    intro x
    have hx : (T * P) x = (1 : Point n →L[ℝ] Point n) x := by rw [hTP]
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hx
  -- the radial Gauss identity `⟨z, T u⟩ = ⟨z, u⟩` for `T = fderiv φ (-z)`.
  have hgauss := curvedRNC_gauss_radial K hK hC hS z hz hexp hzuf
  rw [← hφdef, ← hTdef] at hgauss
  -- assemble.
  calc (∑ k, z k * (P (unitVec i)) k)
      = ∑ k, z k * (T (P (unitVec i))) k := (hgauss (P (unitVec i))).symm
    _ = ∑ k, z k * (unitVec i) k := by rw [hTPx (unitVec i)]
    _ = z i := sum_mul_single_eq z i

end QIQTH.CurvedRNCFirstJetLeg

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedRNCFirstJetLeg.curvedRNC_expTube_neg
#print axioms QIQTH.CurvedRNCFirstJetLeg.curvedRNC_gauss_radial
#print axioms QIQTH.CurvedRNCFirstJetLeg.curvedRNC_firstJetLeg
