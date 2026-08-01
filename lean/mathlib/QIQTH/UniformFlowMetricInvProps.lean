/-
  UniformFlowMetricInvProps — J4-81: the consumer-shape INVERSE-metric properties for the
  `uniformFlowExp` pullback metric `g̃ = uniformFlowPullbackMetric g gi hC hK q v`.

  ## Context — bridging the uniform bounds to the `hEbound` consumer interface.

  `cutoffResidual_expPullback_hEboundW` (`RecenterCutoffC3.lean:97`) consumes, on the metric side, the
  following per-base-point residue for the OPAQUE `expPullbackMetric`:

    * `hinvT`   : `∀ y i j, ∑ σ, g̃⁻¹(y) i σ · g̃(y) σ j = δ_ij`         (pointwise `g̃⁻¹·g̃ = 1`);
    * `hgisymm` : `∀ w i j, g̃⁻¹(w) i j = g̃⁻¹(w) j i`                     (inverse-metric symmetry);
    * `hgi_ann` : `∀ a b, ∃ Kg ≥ 0, |g̃⁻¹(w) i j| ≤ Kg` on the annulus   (inverse-metric bound);
    * `hLapChi_ann`, `hdev` (annulus `Δ_g̃χ` bound / `O(r²)` deviation).

  This file DELIVERS the `uniformFlowExp` analogues, wired to the already-landed uniform bounds
  `uniformInverseMetric_bound` (`UniformInverseMetric.lean`) and `uniformFlowPullbackMetric_c2_uniform_full`
  (`UniformFlowMetricC2Bound.lean`):

    (D1) `uniformFlowPullbackMetricInv` — the entrywise inverse metric, matching `expPullbackMetricInv`.
    (D2) `uniformFlowPullbackMetricInv_mul_metric` / `..._metric_mul_inv` — BOTH pointwise inverse
         identities (`g̃⁻¹·g̃ = 1` and `g̃·g̃⁻¹ = 1`), on the uniform ball.
    (D3) `uniformFlowPullbackMetricInv_symm` — inverse-metric symmetry, from the genuine metric symmetry
         `hgsymm : ∀ y a b, g y a b = g y b a`.
    (D4) `uniformFlowPullbackMetricInv_entry_uniform_bound` (ball) + `..._annulus` — the uniform entry
         bound in ball and annulus form.
    (D5) `uniformFlowChristoffel_uniform_bound` — a uniform bound on the Christoffel symbols of `g̃`.

  The core reusable device is `matToCLM_invMat`: `matToCLM (g̃⁻¹) = Ring.inverse (matToCLM g̃)`
  (the entrywise inverse operator IS the operator inverse), from which D2/D3 are matrix algebra.

  Hypotheses are ONLY `hg` (metric regularity) + `hC` (Christoffel `C^∞`) + `IsCompact K` + `hgnd`
  (global base-metric nondegeneracy) + `hgsymm` (metric symmetry) — all GENUINE (satisfiable by `g = δ`,
  none is the conclusion).  No `sorry`, no new axioms, no `expRho`.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformInverseMetric
import QIQTH.UniformFlowMetricC2Bound
import QIQTH.UniformFlowPullback
import QIQTH.PullbackMetric
import QIQTH.Curvature
import QIQTH.RadialDistance
import QIQTH.RNCDecay
import QIQTH.CutoffAnnulusBounds
import QIQTH.LaplaceBeltrami
import Mathlib

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.HeatResidualBound QIQTH.LaplaceBeltrami
open Set Filter
open scoped Topology BigOperators Matrix

namespace QIQTH.ExpMap

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-! ### General device: the entrywise inverse matrix IS the operator inverse. -/

/-- **Standard-basis decomposition.**  `v = ∑ b, v b • Pi.single b 1` on `Point n = Fin n → ℝ`. -/
theorem eq_sum_smul_single (v : Point n) :
    v = ∑ b, v b • (Pi.single b (1 : ℝ) : Point n) := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **★ The core device.**  The entrywise "inverse matrix" `Minv a b := (matToCLM M)⁻¹ (e_b) a`
    assembles back to the operator inverse: `matToCLM Minv = Ring.inverse (matToCLM M)`.
    (Both continuous-linear maps agree on the standard basis `Pi.single b 1`, hence everywhere by
    linearity.)  No hypotheses. -/
theorem matToCLM_invMat (M : Fin n → Fin n → ℝ) :
    matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a)
      = Ring.inverse (matToCLM M) := by
  apply ContinuousLinearMap.ext
  intro v
  funext i
  rw [matToCLM_apply]
  conv_rhs => rw [eq_sum_smul_single v, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- **Left inverse identity (entrywise).**  For `matToCLM M` a unit,
    `∑ k, (matToCLM M)⁻¹(e_k) i · M k j = δ_ij`. -/
theorem sum_invMat_mul (M : Fin n → Fin n → ℝ) (hM : IsUnit (matToCLM M)) (i j : Fin n) :
    (∑ k, Ring.inverse (matToCLM M) (Pi.single k (1 : ℝ)) i * M k j) = if i = j then 1 else 0 := by
  have hop : matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a) * matToCLM M
      = 1 := by rw [matToCLM_invMat]; exact Ring.inverse_mul_cancel _ hM
  have happ :
      (matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a) * matToCLM M)
        (Pi.single j (1 : ℝ)) i
      = (1 : Point n →L[ℝ] Point n) (Pi.single j (1 : ℝ)) i := by rw [hop]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at happ
  have hw : matToCLM M (Pi.single j (1 : ℝ)) = (fun b => M b j) := by
    funext b
    rw [matToCLM_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [hw, matToCLM_apply] at happ
  rw [happ, Pi.single_apply]

/-- **Right inverse identity (entrywise).**  For `matToCLM M` a unit,
    `∑ k, M i k · (matToCLM M)⁻¹(e_j) k = δ_ij`. -/
theorem sum_mul_invMat (M : Fin n → Fin n → ℝ) (hM : IsUnit (matToCLM M)) (i j : Fin n) :
    (∑ k, M i k * Ring.inverse (matToCLM M) (Pi.single j (1 : ℝ)) k) = if i = j then 1 else 0 := by
  have hop : matToCLM M * matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a)
      = 1 := by rw [matToCLM_invMat]; exact Ring.mul_inverse_cancel _ hM
  have happ :
      (matToCLM M * matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a))
        (Pi.single j (1 : ℝ)) i
      = (1 : Point n →L[ℝ] Point n) (Pi.single j (1 : ℝ)) i := by rw [hop]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at happ
  have hw : matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a)
      (Pi.single j (1 : ℝ))
      = (fun k => Ring.inverse (matToCLM M) (Pi.single j (1 : ℝ)) k) := by
    funext k
    rw [matToCLM_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [hw, matToCLM_apply] at happ
  rw [happ, Pi.single_apply]

/-- **Symmetry of the entrywise inverse.**  For `matToCLM M` a unit and `M` symmetric,
    `(matToCLM M)⁻¹(e_j) i = (matToCLM M)⁻¹(e_i) j`.  (Inverse of a symmetric matrix is symmetric.) -/
theorem invMat_symm (M : Fin n → Fin n → ℝ) (hM : IsUnit (matToCLM M))
    (hMsymm : ∀ a b, M a b = M b a) (i j : Fin n) :
    Ring.inverse (matToCLM M) (Pi.single j (1 : ℝ)) i
      = Ring.inverse (matToCLM M) (Pi.single i (1 : ℝ)) j := by
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of M with hA
  set P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a) with hP
  have hPA : P * A = 1 := by
    apply matToCLM_injective
    rw [matToCLM_mul, matToCLM_one]
    show matToCLM (fun a b => Ring.inverse (matToCLM M) (Pi.single b (1 : ℝ)) a) * matToCLM M = 1
    rw [matToCLM_invMat]; exact Ring.inverse_mul_cancel _ hM
  have hAsymm : Aᵀ = A := by
    funext a b; simp only [Matrix.transpose_apply, hA, Matrix.of_apply]; exact (hMsymm b a)
  have h1 : A * Pᵀ = 1 := by
    have := congrArg Matrix.transpose hPA
    rw [Matrix.transpose_mul, Matrix.transpose_one, hAsymm] at this
    exact this
  have hPT : Pᵀ = P :=
    calc Pᵀ = (P * A) * Pᵀ := by rw [hPA, Matrix.one_mul]
      _ = P * (A * Pᵀ) := by rw [Matrix.mul_assoc]
      _ = P * 1 := by rw [h1]
      _ = P := Matrix.mul_one P
  have hentry := congrFun (congrFun hPT i) j
  simp only [Matrix.transpose_apply, hP, Matrix.of_apply] at hentry
  exact hentry.symm

/-! ### The uniform-flow pullback metric is symmetric. -/

/-- **The uniform-flow pullback metric is symmetric.**  `g̃_{ij}(v) = g̃_{ji}(v)` for a symmetric ambient
    metric `g`.  (Mirror of `expPullbackMetric_symm`.) -/
theorem uniformFlowPullbackMetric_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hsymm : ∀ y a b, g y a b = g y b a)
    (q v : Point n) (i j : Fin n) :
    uniformFlowPullbackMetric g gi hC hK q v i j = uniformFlowPullbackMetric g gi hC hK q v j i := by
  simp only [uniformFlowPullbackMetric]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsymm (uniformFlowExp g gi hC hK q v) a b]; ring

/-! ### (D1) — the entrywise inverse metric. -/

/-- **(D1) — the entrywise inverse metric of the uniform-flow pullback metric.**  Mirrors
    `expPullbackMetricInv`: the `(i,j)` entry of the operator inverse of `matToCLM g̃(v)`.  (`i` is the
    row/output component, `j` selects the `Pi.single j 1` column — exactly the `expPullbackMetricInv`
    index convention.) -/
noncomputable def uniformFlowPullbackMetricInv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q v : Point n) (i j : Fin n) : ℝ :=
  (Ring.inverse (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
    (Pi.single j (1 : ℝ)) i

/-! ### (D2) — the pointwise inverse identities `g̃⁻¹·g̃ = 1` and `g̃·g̃⁻¹ = 1`. -/

/-- **(D2, left) — `hinvT` shape.**  Where `matToCLM g̃(v)` is a unit,
    `∑ σ, g̃⁻¹(v) i σ · g̃(v) σ j = δ_ij` (matches the consumer's `hinvT`). -/
theorem uniformFlowPullbackMetricInv_mul_metric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q v : Point n)
    (hU : IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
    (i j : Fin n) :
    (∑ σ, uniformFlowPullbackMetricInv g gi hC hK q v i σ
        * uniformFlowPullbackMetric g gi hC hK q v σ j) = if i = j then 1 else 0 := by
  simpa only [uniformFlowPullbackMetricInv] using
    sum_invMat_mul (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b) hU i j

/-- **(D2, right) — reversed order.**  Where `matToCLM g̃(v)` is a unit,
    `∑ σ, g̃(v) i σ · g̃⁻¹(v) σ j = δ_ij`. -/
theorem uniformFlowPullbackMetric_mul_inv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q v : Point n)
    (hU : IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
    (i j : Fin n) :
    (∑ σ, uniformFlowPullbackMetric g gi hC hK q v i σ
        * uniformFlowPullbackMetricInv g gi hC hK q v σ j) = if i = j then 1 else 0 := by
  simpa only [uniformFlowPullbackMetricInv] using
    sum_mul_invMat (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b) hU i j

/-! ### (D3) — inverse-metric symmetry from genuine metric symmetry. -/

/-- **(D3) — `hgisymm` shape.**  Where `matToCLM g̃(v)` is a unit and `g` is symmetric,
    `g̃⁻¹(v) i j = g̃⁻¹(v) j i`. -/
theorem uniformFlowPullbackMetricInv_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hgsymm : ∀ y a b, g y a b = g y b a)
    (q v : Point n)
    (hU : IsUnit (matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b)))
    (i j : Fin n) :
    uniformFlowPullbackMetricInv g gi hC hK q v i j
      = uniformFlowPullbackMetricInv g gi hC hK q v j i := by
  have hMsymm : ∀ a b, uniformFlowPullbackMetric g gi hC hK q v a b
      = uniformFlowPullbackMetric g gi hC hK q v b a :=
    fun a b => uniformFlowPullbackMetric_symm g gi hC hK hgsymm q v a b
  simpa only [uniformFlowPullbackMetricInv] using
    invMat_symm (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b) hU hMsymm i j

/-! ### (D4) — the uniform entry bound (ball + annulus). -/

/-- **(D4, ball) — uniform inverse-metric entry bound.**  From the uniform inverse-metric norm bound
    `uniformInverseMetric_bound`, there is a single radius `r₀ > 0` and constant `Kg ≥ 0` bounding every
    entry `|g̃⁻¹(v) i j|` over `q ∈ K`, `‖v‖ < r₀`.  Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`. -/
theorem uniformFlowPullbackMetricInv_entry_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ r₀ > (0 : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j| ≤ Kg := by
  obtain ⟨r₀, hr₀0, Kinv, hbound⟩ := uniformInverseMetric_bound g gi hg hC hK hgnd
  refine ⟨r₀, hr₀0, max 0 Kinv, le_max_left _ _, ?_⟩
  intro q hq v hv i j
  exact le_trans ((hbound q hq v hv).2.2 i j) (le_max_right _ _)

/-- **(D4, annulus) — the consumer's annulus-friendly form.**  For `0 ≤ b` and `b < r₀`, every point
    `v` of the closed annulus `{v : rncRadialSq v ≤ b²}` lies in `Metric.ball 0 r₀`
    (`‖v‖ ≤ rncRadial v = √(rncRadialSq v) ≤ b < r₀`), so the ball bound applies verbatim.  This matches
    the shape of the consumer's `hgi_ann` (the annulus is a subset of the ball). -/
theorem uniformFlowPullbackMetricInv_entry_uniform_bound_annulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ r₀ > (0 : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (a b : ℝ), 0 ≤ b → b < r₀ → ∀ q ∈ K, ∀ v : Point n,
      a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 → ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j| ≤ Kg := by
  obtain ⟨r₀, hr₀0, Kg, hKg0, hball⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  refine ⟨r₀, hr₀0, Kg, hKg0, ?_⟩
  intro a b hb0 hbr q hq v _ha hub i j
  have hnorm : ‖v‖ < r₀ := by
    have h1 : ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
    have h2 : rncRadial v ≤ b := by
      have : rncRadial v ^ 2 ≤ b ^ 2 := by rw [rncRadial_sq]; exact hub
      have hrnn : 0 ≤ rncRadial v := rncRadial_nonneg v
      nlinarith [this, hrnn, hb0]
    calc ‖v‖ ≤ rncRadial v := h1
      _ ≤ b := h2
      _ < r₀ := hbr
  exact hball q hq v hnorm i j

/-! ### Bundled uniform capstone (D2 + D3 + D4 together on one ball). -/

/-- **★ J4-81 capstone — the bundled consumer-shape inverse-metric properties, uniform over `K`.**
    ONE radius `r₀ > 0` and constant `Kg ≥ 0` such that for every `q ∈ K` and `‖v‖ < r₀`:
    * (`hinvT`, both orders)  `∑ σ, g̃⁻¹ i σ · g̃ σ j = δ_ij` and `∑ σ, g̃ i σ · g̃⁻¹ σ j = δ_ij`;
    * (`hgisymm`)            `g̃⁻¹ i j = g̃⁻¹ j i`;
    * (`hgi_ann`, ball form) `|g̃⁻¹ i j| ≤ Kg`.
    Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`+`hgsymm`, all genuine (satisfiable by `g = δ`,
    none is the conclusion).  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetricInv_props (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a) :
    ∃ r₀ > (0 : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      (∀ i j : Fin n, (∑ σ, uniformFlowPullbackMetricInv g gi hC hK q v i σ
          * uniformFlowPullbackMetric g gi hC hK q v σ j) = if i = j then 1 else 0)
      ∧ (∀ i j : Fin n, (∑ σ, uniformFlowPullbackMetric g gi hC hK q v i σ
          * uniformFlowPullbackMetricInv g gi hC hK q v σ j) = if i = j then 1 else 0)
      ∧ (∀ i j : Fin n, uniformFlowPullbackMetricInv g gi hC hK q v i j
          = uniformFlowPullbackMetricInv g gi hC hK q v j i)
      ∧ (∀ i j : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v i j| ≤ Kg) := by
  obtain ⟨r₀, hr₀0, Kinv, hbound⟩ := uniformInverseMetric_bound g gi hg hC hK hgnd
  refine ⟨r₀, hr₀0, max 0 Kinv, le_max_left _ _, ?_⟩
  intro q hq v hv
  obtain ⟨hU, _hnorm, hentry⟩ := hbound q hq v hv
  refine ⟨fun i j => uniformFlowPullbackMetricInv_mul_metric g gi hC hK q v hU i j,
    fun i j => uniformFlowPullbackMetric_mul_inv g gi hC hK q v hU i j,
    fun i j => uniformFlowPullbackMetricInv_symm g gi hC hK hgsymm q v hU i j,
    fun i j => ?_⟩
  exact le_trans (hentry i j) (le_max_right _ _)

/-! ### (D5) — a uniform bound on the Christoffel symbols of `g̃`. -/

/-- **(D5) — uniform Christoffel bound.**  The Christoffel symbols of the uniform-flow pullback metric
    `g̃` (with its genuine inverse `g̃⁻¹`) are uniformly bounded over `q ∈ K`, `‖v‖ < r₀`:
    `Γ̃ = ½·g̃⁻¹·(∂g̃ + ∂g̃ − ∂g̃)` with `|g̃⁻¹| ≤ Kinv` (`uniformInverseMetric_bound`) and each
    `|∂g̃-entry| = |Dg̃-entry(e)| ≤ M` (`uniformFlowPullbackMetric_c2_uniform_full`, via `pd_eq_fderiv`).
    Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`.  This is the first-derivative layer toward the
    `Δ_g̃χ` annulus bound; NOT `a₁ = R/6`. -/
theorem uniformFlowChristoffel_uniform_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ r₀ > (0 : ℝ), ∃ KΓ : ℝ, 0 ≤ KΓ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ k i j : Fin n,
      |christoffel (fun w a b => uniformFlowPullbackMetric g gi hC hK q w a b)
          (fun w a b => uniformFlowPullbackMetricInv g gi hC hK q w a b) k i j v|
        ≤ KΓ := by
  obtain ⟨r₁, hr₁0, Kinv, hInv⟩ := uniformInverseMetric_bound g gi hg hC hK hgnd
  obtain ⟨r₂, hr₂0, M, hC2⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0,
    (1 / 2) * (n : ℝ) * max 0 Kinv * (3 * max 0 M), by positivity, ?_⟩
  intro q hq v hv k i j
  have hv1 : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  -- inverse-metric entry bound.
  have hGI : ∀ a b : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v a b| ≤ max 0 Kinv :=
    fun a b => le_trans ((hInv q hq v hv1).2.2 a b) (le_max_right _ _)
  -- first-partial bound for every entry / direction (`pd = D(·)(e)`).
  have hpd : ∀ a b e : Fin n,
      |pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v| ≤ max 0 M := by
    intro a b e
    obtain ⟨hfd1, _, _, hM', _⟩ := hC2 q hq v hv2 a b
    rw [pd_eq_fderiv (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v
      hfd1.differentiableAt]
    calc |fderiv ℝ (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) v (Pi.single e 1)|
        = ‖fderiv ℝ (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) v
            (Pi.single e (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) v‖
            * ‖(Pi.single e (1 : ℝ) : Point n)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) v‖ * 1 := by
            rw [Pi.norm_single, norm_one]
      _ = ‖fderiv ℝ (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) v‖ := mul_one _
      _ ≤ max 0 M := le_trans hM' (le_max_right _ _)
  -- per-α term bound.
  have hterm : ∀ α : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v k α
          * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
            + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
            - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
        ≤ max 0 Kinv * (3 * max 0 M) := by
    intro α
    rw [abs_mul]
    set A := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v with hAdef
    set B := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v with hBdef
    set C := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v with hCdef
    have h2 : |A + B - C| ≤ 3 * max 0 M := by
      have htri := abs_add_le (A + B) (-C)
      rw [← sub_eq_add_neg, abs_neg] at htri
      have : |A + B - C| ≤ |A| + |B| + |C| :=
        le_trans htri (by gcongr; exact abs_add_le _ _)
      calc |A + B - C| ≤ |A| + |B| + |C| := this
        _ ≤ max 0 M + max 0 M + max 0 M := by
            gcongr
            · exact hpd α j i
            · exact hpd α i j
            · exact hpd i j α
        _ = 3 * max 0 M := by ring
    exact mul_le_mul (hGI k α) h2 (abs_nonneg _) (le_max_left _ _)
  -- assemble.
  simp only [christoffel]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2 : ℝ)
        * |∑ α, uniformFlowPullbackMetricInv g gi hC hK q v k α
            * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
              + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
              - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
      ≤ (1 / 2 : ℝ) * ∑ α, max 0 Kinv * (3 * max 0 M) := by
        gcongr
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun α _ => hterm α)
    _ = (1 / 2 : ℝ) * (n : ℝ) * max 0 Kinv * (3 * max 0 M) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### (D6) — the annulus `Δ_g̃χ` bound (from D4 + D5, no continuity infrastructure). -/

/-- **Second-partial cutoff bound on the annulus** (companion to `pd_radialCutoff_bound_on_annulus`).
    `|∂ᵢ∂ⱼ(radialCutoff a b) w| ≤ Kpp` on the annulus, uniform over `i j`.  Self-contained: `χ` is `C∞`,
    so `w ↦ ∂ᵢ∂ⱼχ w` is continuous and `exists_bound_on_annulus` applies. -/
theorem pd_pd_radialCutoff_bound_on_annulus (a b : ℝ) :
    ∃ Kpp : ℝ, 0 ≤ Kpp ∧ ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => pd (radialCutoff a b) j y) i w| ≤ Kpp := by
  classical
  have hbd : ∀ i j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => pd (radialCutoff a b) j y) i w| ≤ K :=
    fun i j => exists_bound_on_annulus (fun w => pd (fun y => pd (radialCutoff a b) j y) i w)
      (contDiff_pd_inf (fun y => pd (radialCutoff a b) j y)
        (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) j) i).continuous a b
  choose K hK0 hKbd using hbd
  refine ⟨∑ i, ∑ j, K i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hK0 i j, ?_⟩
  intro w i j h1 h2
  refine (hKbd i j w h1 h2).trans ?_
  calc K i j ≤ ∑ j', K i j' :=
        Finset.single_le_sum (f := fun j' => K i j') (fun j' _ => hK0 i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', K i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', K i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => hK0 i' j') (Finset.mem_univ i)

/-- **(D6) — the uniform annulus `Δ_g̃χ` bound (`hLapChi_ann` shape).**  On any annulus
    `{v : a² ≤ rncRadialSq v ≤ b²}` with `0 ≤ b` and `b < r₀` (so the annulus `⊆ Metric.ball 0 r₀`),
    the `g̃`-Laplacian of the radial cutoff is uniformly bounded over `q ∈ K`.  Assembled DIRECTLY from
    the uniform inverse-metric bound (D4), the uniform Christoffel bound (D5), and the self-contained
    cutoff gradient/Hessian bounds — NO global/annulus continuity of `g̃⁻¹`/`Γ̃` is needed (that was the
    wall for the opaque `expPullback`; the uniform-flow bounds sidestep it).  Hypotheses ONLY
    `hg`+`hC`+`IsCompact K`+`hgnd`.  NOT `a₁ = R/6`. -/
theorem uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b))) :
    ∃ r₀ > (0 : ℝ), ∀ (a b : ℝ), 0 ≤ b → b < r₀ → ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ q ∈ K, ∀ v : Point n,
      a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
      |laplaceBeltrami (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
          (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) (radialCutoff a b) v|
        ≤ Kc2 := by
  obtain ⟨r₁, hr₁0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r₂, hr₂0, KΓ, hKΓ0, hChb⟩ := uniformFlowChristoffel_uniform_bound g gi hg hC hK hgnd
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0, ?_⟩
  intro a b hb0 hbr
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kpp, hKpp0, hPPchi⟩ := pd_pd_radialCutoff_bound_on_annulus (n := n) a b
  refine ⟨(n : ℝ) * (n : ℝ) * (Kg * (Kpp + (n : ℝ) * KΓ * Kc1)), by positivity, ?_⟩
  intro q hq v ha hub
  -- annulus ⊆ ball: `‖v‖ < min r₁ r₂`.
  have hnorm : ‖v‖ < min r₁ r₂ := by
    have h1 : ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
    have h2 : rncRadial v ≤ b := by
      have hsq : rncRadial v ^ 2 ≤ b ^ 2 := by rw [rncRadial_sq]; exact hub
      nlinarith [hsq, rncRadial_nonneg v, hb0]
    exact lt_of_le_of_lt (le_trans h1 h2) hbr
  have hv1 : ‖v‖ < r₁ := lt_of_lt_of_le hnorm (min_le_left _ _)
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hnorm (min_le_right _ _)
  -- entrywise bounds on the annulus point `v`.
  have hGI : ∀ i j : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v i j| ≤ Kg :=
    hGIb q hq v hv1
  have hCh : ∀ k i j : Fin n,
      |christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
          (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v| ≤ KΓ :=
    hChb q hq v hv2
  have hDc : ∀ k : Fin n, |pd (radialCutoff a b) k v| ≤ Kc1 := fun k => hDchi v k ha hub
  have hPP : ∀ i j : Fin n, |pd (fun y => pd (radialCutoff a b) j y) i v| ≤ Kpp :=
    fun i j => hPPchi v i j ha hub
  -- `|x - y| ≤ |x| + |y|`.
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  -- inner-expression bound.
  have hE : ∀ i j : Fin n,
      |pd (fun y => pd (radialCutoff a b) j y) i v
          - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
              (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
              * pd (radialCutoff a b) k v|
        ≤ Kpp + (n : ℝ) * KΓ * Kc1 := by
    intro i j
    refine le_trans (habs_sub _ _) ?_
    refine add_le_add (hPP i j) ?_
    calc |∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
            (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
            * pd (radialCutoff a b) k v|
        ≤ ∑ k, |christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
            (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
            * pd (radialCutoff a b) k v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, KΓ * Kc1 := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hCh k i j) (hDc k) (abs_nonneg _) hKΓ0
      _ = (n : ℝ) * KΓ * Kc1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- assemble the double sum.
  simp only [laplaceBeltrami]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _) ?_
  have hInner : ∀ i j : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v i j
          * (pd (fun y => pd (radialCutoff a b) j y) i v
            - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
                (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
                * pd (radialCutoff a b) k v)|
        ≤ Kg * (Kpp + (n : ℝ) * KΓ * Kc1) := by
    intro i j
    rw [abs_mul]
    exact mul_le_mul (hGI i j) (hE i j) (abs_nonneg _) hKg0
  calc ∑ i, ∑ j, |uniformFlowPullbackMetricInv g gi hC hK q v i j
          * (pd (fun y => pd (radialCutoff a b) j y) i v
            - ∑ k, christoffel (fun w c d => uniformFlowPullbackMetric g gi hC hK q w c d)
                (fun w c d => uniformFlowPullbackMetricInv g gi hC hK q w c d) k i j v
                * pd (radialCutoff a b) k v)|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, Kg * (Kpp + (n : ℝ) * KΓ * Kc1) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hInner i j
    _ = (n : ℝ) * (n : ℝ) * (Kg * (Kpp + (n : ℝ) * KΓ * Kc1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end QIQTH.ExpMap


