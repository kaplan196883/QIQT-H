/-
  GlobalResidualWitness — J4-92: the GLOBAL-chart residual witness and the in-chart RESIDUAL
  TRANSPORT identity + bound for the recentred cutoff parametrix.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file is (the E-identification, landed in-chart).

  The conditional `a₁ = R/6` capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual`
  (`TrueKernelA1Reduced.lean:153`) consumes a GLOBAL width-2 residual bound
      `hEboundW : ∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ C · baseKernelW 2 0 τ p q`,
  where `E := heatOp g gi H = ∂_τ H − Δ_g H` is the parametrix residual in the ORIGINAL chart, `H` a
  function-variable we may CHOOSE, and `baseKernelW 2 0 τ p q = gaussDdim (2τ) (p − q)`.

  The `hunif`-chain's analytic pieces are all in place:
    * `PullbackNaturalityLocal.laplaceBeltrami_uniformFlow_naturality` (L4) — the Laplace–Beltrami
      naturality `Δ_{g̃_q}(f ∘ φ_q)(v) = (Δ_g f)(φ_q v)` at `φ_q = uniformFlowExp g gi hC hK q`, taking
      the far-point regularity/nondegeneracy AS HYPOTHESES;
    * `UniformTauResidual.cutoffResidual_uniformFlow_unconditional_tau` (A) — a single `(a,b,B)`,
      τ-free and uniform over `q ∈ K`, dominating the RECENTRED cutoff residual
      `|χ·∂_τH₀ − Δ_{g̃_q}(χ·H₀(τ))(v)| ≤ B · gaussDdimWide τ v`.

  This file assembles them into the concrete E-IDENTIFICATION for the global witness
      `H_w τ p q := radialCutoff a b (Vmap q p) · heatParametrix 0 Θ u τ (Vmap q p)`
                 = (χ · H₀(τ)) ∘ Vmap_q  ,   `Vmap q = exp_q⁻¹`  (the recentred cutoff parametrix
  transported to the global chart by the inverse chart map).  Concretely it delivers:

    * `heatOp_globalWitness_eq_recentred_inChart` (W2, ★ the RESIDUAL TRANSPORT identity) — for the
      in-chart point `p = φ_q v` (`‖v‖ < r₀`), the GLOBAL-chart heat operator of `H_w` equals the
      RECENTRED cutoff residual bracket of (A):
          `heatOp g gi H_w τ (φ_q v) q
             = χ(v)·∂_τH₀(τ,v) − Δ_{g̃_q}(χ·H₀(τ,·))(v)` .
      The `∂_τ`-part is direct (`Vmap` is τ-independent); the `Δ`-part is L4 naturality applied to
      `f := H_w(τ,·,q)` (reverse direction), whose composition `f ∘ φ_q =ᶠ χ·H₀(τ)` near `0` by the
      left-inverse germ, plus function-germ locality of `Δ` (`VanVleckCancellation.laplaceBeltrami_congr_nhds`).
    * `globalWitness_residual_bound_inChart` (W3, ★ the in-chart per-base-point Gaussian bound) —
      combining W2 with (A): a single `(a,b,B)` such that for every `τ > 0`, `q ∈ K` there is `r₀ > 0`
      with `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdimWide τ v` for the carried in-chart `v`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Honest scope (binding; consulted GPT-5.6-sol high — verdict verbatim below).

  W2/W3 carry, as GENUINE (satisfiable, non-vacuous, load-bearing) hypotheses, exactly the data the
  transport consumes at the in-chart point:
    * `hgerm` — the left-inverse germ `(fun z => Vmap q (φ_q z)) =ᶠ[𝓝 v] id`  (holds for any local
      left inverse of the local diffeo `φ_q`; e.g. `expLocalInverse` at `v = 0`);
    * the L4 naturality preconditions at `φ_q v`: `g` `C¹`, `H_w(τ,·,q)` `C²`, `g` nondegenerate,
      `gi` a two-sided inverse of `g`.
  The `C²` regularity of `H_w(τ,·,q) = (χ·H₀)∘Vmap_q` at `p = φ_q v` is exactly the inverse-chart `C²`
  regularity of `Vmap_q = exp_q⁻¹`; in this repo it is known ONLY at the single point `v = 0` (`p = q`;
  via `to_localInverse`/the strict derivative at `q`), NOT off-diagonal (that needs a fresh IFT at every
  `v` with only `fderiv`-nondegeneracy available — an infrastructure-scale local-diffeomorphism layer).
  Hence W2/W3 are the honest, bankable IN-CHART transport identity/bound; they do NOT discharge the
  GLOBAL (`∀ p`) `hunif` and do NOT build the zero-extension.  The global `hunif` + `hcoord` therefore
  remain CARRIED into the recenter capstone (`RecenterHEboundW.hEboundW_of_perBasePoint_bound` /
  `RecenterA1Capstone.trueKernel_diagonal_a1_recenter`), exactly as before.  NOT `a₁ = R/6`.

  GPT-5.6-sol verdict (high): "The honest current deliverable is a bankable conditional in-chart
  transport identity/bound, not a full discharge of `hunif`; keep `hunif` and `hcoord` as capstone
  hypotheses until a genuine smooth zero-extension/local-diffeomorphism layer is proved."

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.PullbackNaturalityLocal
import QIQTH.UniformTauResidual
import QIQTH.TrueHeatKernel
import QIQTH.VanVleckCancellation

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### W1 — the global-chart witness. -/

/-- **W1 — the GLOBAL-chart cutoff-parametrix witness.**  The recentred cutoff parametrix
    `(χ · H₀(τ))` transported to the global chart via the (q-centred) inverse chart map `Vmap q`:
        `H_w τ p q := radialCutoff a b (Vmap q p) · heatParametrix 0 Θ u τ (Vmap q p)` .
    With `Vmap q = exp_q⁻¹` and `p = exp_q v` this is `(χ·H₀(τ))(v)`.  As a function of `(τ,p,q)` it is
    exactly the `H : ℝ → Point n → Point n → ℝ` slot the global consumer's `heatOp g gi H` expects. -/
noncomputable def globalCutoffParametrixWitness (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (Vmap : Point n → Point n → Point n) (τ : ℝ) (p q : Point n) : ℝ :=
  radialCutoff a b (Vmap q p) * heatParametrix 0 Θ u τ (Vmap q p)

/-! ### W2 — the residual transport identity (in-chart). -/

/-- **★ W2 — THE RESIDUAL TRANSPORT IDENTITY (in-chart).**  For a base point `q ∈ K`, time `τ`, and an
    inverse chart map `Vmap`, the GLOBAL-chart heat operator of the witness `H_w` at the in-chart point
    `p = φ_q v` (`φ_q = uniformFlowExp g gi hC hK q`, `‖v‖ < r₀`) equals the RECENTRED cutoff residual
    bracket dominated by `cutoffResidual_uniformFlow_unconditional_tau`:
        `heatOp g gi H_w τ (φ_q v) q
           = radialCutoff a b v · ∂_τ(heatParametrix 0 Θ u · v)(τ)
             − Δ_{g̃_q}(fun y => radialCutoff a b y · heatParametrix 0 Θ u τ y)(v)` .

    Proof.  `heatOp` splits into `∂_τ` and `−Δ_g`.  The `∂_τ` slot: since `Vmap q (φ_q v) = v`
    (`hgerm` at `v`), `H_w · (φ_q v) q = χ(v)·H₀(·,v)`, so its `τ`-derivative pulls the constant `χ(v)`
    out (`deriv_const_mul_field`).  The `−Δ_g` slot: apply the L4 naturality
    `laplaceBeltrami_uniformFlow_naturality` to `f := H_w(τ,·,q)` in the reverse direction to get
    `Δ_g(H_w(τ,·,q))(φ_q v) = Δ_{g̃_q}(H_w(τ,·,q) ∘ φ_q)(v)`, then rewrite `H_w(τ,·,q) ∘ φ_q =ᶠ χ·H₀(τ)`
    near `v` (left-inverse germ `hgerm`) via function-germ locality of `Δ`
    (`VanVleckCancellation.laplaceBeltrami_congr_nhds`).

    All hypotheses are genuine and load-bearing: `hgerm` (the left-inverse germ), and the four L4
    preconditions at `φ_q v` (`g` `C¹`, `H_w(τ,·,q)` `C²`, `g` nondegenerate, `gi` two-sided inverse).
    None is the conclusion.  This is the E-identification, landed for the in-chart slice. -/
theorem heatOp_globalWitness_eq_recentred_inChart
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) (τ : ℝ) (q : Point n) (hq : q ∈ K) :
    ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
      (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
      (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q v) →
      IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
      (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
      (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
      heatOp g gi (globalCutoffParametrixWitness Θ u a b Vmap) τ
          (uniformFlowExp g gi hC hK q v) q
        = radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
  obtain ⟨r₀, hr₀pos, hnat⟩ := laplaceBeltrami_uniformFlow_naturality g gi hC hK hgsymm
      (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
  refine ⟨r₀, hr₀pos, ?_⟩
  intro v hv hgerm hg1 hf hU hGGi hGiG
  -- the point value of the left-inverse germ at `v`.
  have hpt : Vmap q (uniformFlowExp g gi hC hK q v) = v := by
    simpa using hgerm.eq_of_nhds
  -- the recentred profile germ `H_w(τ,·,q) ∘ φ_q =ᶠ χ·H₀(τ)` near `v`.
  have hprofilegerm :
      (fun z => (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
          (uniformFlowExp g gi hC hK q z))
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : Vmap q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitness, hz']
  -- the `−Δ_g` slot via L4 naturality (reverse) + function-germ locality.
  have hlap : laplaceBeltrami g gi
        (fun p => globalCutoffParametrixWitness Θ u a b Vmap τ p q)
        (uniformFlowExp g gi hC hK q v)
      = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q)
          (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v := by
    have hn := hnat q hq v hv hg1 hf hU hGGi hGiG
    rw [← hn]
    exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
      (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
      _ _ v hprofilegerm
  -- the `∂_τ` slot: `Vmap` is τ-independent, so `χ(v)` pulls out of the time derivative.
  simp only [heatOp]
  have hterm1fun :
      (fun s => globalCutoffParametrixWitness Θ u a b Vmap s (uniformFlowExp g gi hC hK q v) q)
        = (fun s => radialCutoff a b v * heatParametrix 0 Θ u s v) := by
    funext s
    simp only [globalCutoffParametrixWitness, hpt]
  rw [hterm1fun, deriv_const_mul_field, hlap]

/-! ### W3 — the in-chart per-base-point residual Gaussian bound. -/

/-- **★ W3 — THE IN-CHART PER-BASE-POINT RESIDUAL GAUSSIAN BOUND for the global witness.**  Combining
    the residual transport `heatOp_globalWitness_eq_recentred_inChart` (W2) with the τ-uniform recentred
    bound `cutoffResidual_uniformFlow_unconditional_tau` (A): a SINGLE `(a,b,B)` — `τ`-free, uniform over
    `q ∈ K` — such that for every `τ > 0`, every base point `q ∈ K`, and every inverse chart map `Vmap`,
    there is `r₀ > 0` with
        `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdimWide τ v`
    for the in-chart `v` (`‖v‖ < r₀`) carrying the germ + naturality preconditions of W2.  This is the
    honest IN-CHART slice of the capstone's `hunif` (the per-base-point WIDE-Gaussian residual bound),
    for the CONCRETE witness `H_w`.  It does NOT extend to all `p` (see the header's honest scope). -/
theorem globalWitness_residual_bound_inChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧
      ∀ (Vmap : Point n → Point n → Point n) (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          (fun z => Vmap q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) →
          (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
          ContDiffAt ℝ 2 (fun x => globalCutoffParametrixWitness Θ u a b Vmap τ x q)
              (uniformFlowExp g gi hC hK q v) →
          IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
          (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
              * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
          (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
              * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b Vmap) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdimWide τ v := by
  obtain ⟨a, b, B, ha, hab, hB, hAbound⟩ :=
    cutoffResidual_uniformFlow_unconditional_tau g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro Vmap τ q hq hτ
  obtain ⟨r₀, hr₀, htrans⟩ :=
    heatOp_globalWitness_eq_recentred_inChart g gi hC hK hgsymm Θ u a b Vmap τ q hq
  refine ⟨r₀, hr₀, ?_⟩
  intro v hv hgerm hg1 hf hU hGGi hGiG
  rw [htrans v hv hgerm hg1 hf hU hGGi hGiG]
  exact hAbound τ hτ q hq v

end QIQTH.HeatResidualBound
