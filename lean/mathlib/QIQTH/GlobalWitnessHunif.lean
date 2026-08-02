/-
  GlobalWitnessHunif — J4-94: the FINAL far-point discharge of the in-chart residual bound, plus the
  reusable analytic core of the out-of-chart zero-extension.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file lands (H1 + H2-core), and what it firewalls (H2-transfer / H3 / H4 / H5).

  J4-93 (`UniformFlowLocalInverse.globalWitness_residual_bound_inChart_unconditional`, "I4") delivered
  a single `τ`-free `(a,b,B)`, uniform over `q ∈ K`, with
      `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdimWide τ v`   for `‖v‖ < r₀`,
  where `H_w = globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)` — MODULO four
  per-point antecedents evaluated at the FAR point `φ_q v`:
    (hg1)  `∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (φ_q v)`;
    (hU)   `IsUnit (matToCLM (fun a' b' => g (φ_q v) a' b'))`;
    (hGGi) `∀ pp cc, ∑ bb, g (φ_q v) pp bb · gi (φ_q v) bb cc = δ`   (the `g·gi = 1` side), and
    (hGiG) `∀ pp cc, ∑ aa, gi (φ_q v) pp aa · g (φ_q v) aa cc = δ`   (the `gi·g = 1` side).

  ### H1 (LANDED) — `globalWitness_residual_bound_inChart_final`.
  All four far-point antecedents are DISCHARGED from the global hypotheses already present in I4's
  signature — pure plumbing:
    * hg1  : `(hg a' b').contDiffAt.of_le le_top`   (`ContDiff ⊤ ⟹ ContDiffAt 1` anywhere);
    * hU   : `hgnd (φ_q v)`                          (global nondegeneracy instantiated);
    * hGGi : `hinvF (φ_q v)`                         (the global metric-inverse relation instantiated);
    * hGiG : from hGGi via `Matrix.mul_eq_one_comm`  — for SQUARE matrices over a commutative ring a
             one-sided inverse is two-sided, so `g·gi = 1` (entrywise) gives `gi·g = 1` (entrywise) with
             NO extra hypothesis (`metricInv_left_of_right`; `hgsymm`/`hgnd` are NOT even needed for it).

  ### H2-core (LANDED) — `heatOp_eq_zero_of_locally_zero`.
  The analytic heart of any out-of-chart zero-extension: `heatOp g gi H τ p q = 0` whenever the kernel
  section vanishes on a NEIGHBORHOOD of the base point.  `heatOp = ∂_τ(H) − Δ_g(H(τ,·))`; the `∂_τ` slot
  dies because `H(·,p,q)` is `=ᶠ 0` in `t` near `τ` (`EventuallyEq.deriv_eq`), and the `Δ_g` slot dies
  because `Δ_g` is a germ-local (second-order) operator (`laplaceBeltrami_congr_nhds`).  Reusable and
  `Vmap`-agnostic.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## FIREWALL — what is NOT landed, and precisely why (binding, honest).

  ### H2-transfer (the full gated witness).  The mission's design finding, confirmed:
    * `basepointInverseChart … q` is `e.symm` of the base-point IFT partial homeomorph `e` — a TOTAL
      function whose values OFF `e.target` are UNCONTROLLED junk (Mathlib's IFT inverse is unspecified
      off the target).  Hence `radialCutoff a b (e.symm p)` — and so the witness `H_w(τ,p,q)` — need NOT
      vanish for `p` outside the chart: `e.symm p` can be junk landing inside the cutoff annulus.  The
      raw witness therefore has NO clean out-of-chart zero-extension.
    * The FIX is a set-gated witness `H_w' τ p q := if p ∈ S_q then H_w τ p q else 0` gated on the
      COMPACT (hence closed) image `S_q = φ_q '' Metric.closedBall 0 b`.  Off `S_q` (an open complement)
      `H_w'` is locally `0`, so `heatOp_eq_zero_of_locally_zero` gives `heatOp = 0` there — the crux is
      resolved by construction, NOT by any property of the junk inverse.
    * BUT transferring I4's in-chart bound onto `H_w'` requires `H_w' =ᶠ H_w` on a NEIGHBORHOOD of each
      in-chart point `p = φ_q v`, i.e. `p ∈ interior S_q`.  That needs `φ_q` to be an OPEN map at `v`
      (so `φ_q '' (open ball ⊆ source)` is an open subset of `S_q`) — a fact carried only INSIDE the
      base-point IFT partial homeomorph `e`, which `basepointChart_exists` hides behind `.choose`.
      Exposing `e` (or reproving open-ness at `v` from the local inverse germ) is genuine
      local-diffeomorphism infrastructure, deferred.

  ### H4 / H3 / H5 (the coordinate conversion and the capstone) — DECISIVELY BLOCKED.
  The consumer `RecenterReduction.hEboundW_of_uniform_perBasePoint` needs, at the FAR point `p = φ_q v`,
      `B · gaussDdimWide τ v  ≤  C · gaussDdim (2τ) (p − q)`.
  With the repo's definitions `gaussDdimWide τ v = (4πτ)^{−n/2} exp(−‖v‖²/(8τ))` and
  `gaussDdim (2τ) w = (8πτ)^{−n/2} exp(−‖w‖²/(8τ))`, one has EXACTLY
      `gaussDdimWide τ v = 2^{n/2} · gaussDdim (2τ) v` .
  So the two Gaussians share the SAME width `8τ`; the bound reduces to `gaussDdim (2τ) v ≤ C · gaussDdim
  (2τ)(p−q)`, i.e. `exp((‖p−q‖² − ‖v‖²)/(8τ)) ≤ C`.  Uniformity in `τ→0⁺` FORCES `‖p−q‖² ≤ ‖v‖²`, i.e.
  the recentring chart `φ_q` must be DISTANCE-NON-INCREASING from its base point.  For `φ_q` an
  exponential map this is curvature-sign dependent and FALSE in general (transverse geodesic spreading
  under non-positive curvature).  The repo's own `GaussCompare.gaussDdim_le_of_norm_ge` converts a
  near-isometry `c‖w‖ ≤ ‖u‖` (`0 < c ≤ 1`) only into the WIDENED `gaussDdim (2τ/c²)` — a broader
  Gaussian the consumer cannot absorb (an upper bound by the NARROWER `gaussDdim (2τ)` fails whenever
  `c < 1`).  Hence H4 is not a plumbing gap but a genuine width-preservation obstruction, and H5
  (`hunif_final` feeding the capstone) is unreachable regardless of H2.  NOT `a₁ = R/6`.

  No `sorry`, no new axioms, no `expRho` in statements, no vacuous/unsatisfiable hypotheses.
-/
import Mathlib
import QIQTH.UniformFlowLocalInverse
import QIQTH.VanVleckCancellation

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### A tiny linear-algebra helper: a one-sided metric inverse is two-sided. -/

/-- **A right inverse of a square metric is a left inverse.**  If `matToCLM G` is invertible and,
    entrywise, `∑ b, G p b · Gi b c = δ` (i.e. `matToCLM G · matToCLM Gi = 1` as operators), then also
    `∑ a, Gi p a · G a c = δ` (`matToCLM Gi · matToCLM G = 1`).  Pure operator algebra: the given
    relation shows `matToCLM Gi` is a RIGHT inverse of the unit `matToCLM G`, hence its two-sided
    inverse, hence also a LEFT inverse; the entries are read off on the standard basis (the
    `matToCLM_injective` evaluation technique).  No symmetry hypothesis is required. -/
theorem metricInv_left_of_right (G Gi : Fin n → Fin n → ℝ)
    (hU : IsUnit (matToCLM G))
    (hR : ∀ p c, (∑ b, G p b * Gi b c) = if p = c then (1 : ℝ) else 0) :
    ∀ p c, (∑ a, Gi p a * G a c) = if p = c then (1 : ℝ) else 0 := by
  -- Step 1: `matToCLM G · matToCLM Gi = 1`, by evaluation on vectors (uses `hR`).
  have hAB : matToCLM G * matToCLM Gi = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    funext i
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, matToCLM_apply]
    calc (∑ b, G i b * matToCLM Gi v b)
        = ∑ b, ∑ c, G i b * (Gi b c * v c) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [matToCLM_apply, Finset.mul_sum]
      _ = ∑ c, ∑ b, G i b * (Gi b c * v c) := Finset.sum_comm
      _ = ∑ c, (∑ b, G i b * Gi b c) * v c := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ c, (if i = c then (1 : ℝ) else 0) * v c := by
            refine Finset.sum_congr rfl fun c _ => ?_; rw [hR i c]
      _ = v i := by
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  -- Step 2: a right inverse of a unit is a two-sided inverse.
  have hBA : matToCLM Gi * matToCLM G = 1 := by
    obtain ⟨A, hA⟩ := hU
    have hA1 : (↑A : Point n →L[ℝ] Point n) * matToCLM Gi = 1 := by rw [hA]; exact hAB
    have hGi : matToCLM Gi = ↑A⁻¹ := by
      calc matToCLM Gi = (↑A⁻¹ * ↑A) * matToCLM Gi := by rw [A.inv_mul, one_mul]
        _ = ↑A⁻¹ * (↑A * matToCLM Gi) := by rw [mul_assoc]
        _ = ↑A⁻¹ * 1 := by rw [hA1]
        _ = ↑A⁻¹ := mul_one _
    rw [hGi, ← hA]; exact A.inv_mul
  -- Step 3: read the entries off `matToCLM Gi · matToCLM G = 1` on the standard basis.
  intro p c
  have hw : ∀ a, matToCLM G (Pi.single c (1 : ℝ)) a = G a c := by
    intro a
    rw [matToCLM_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hh := congrFun (congrArg (fun T : Point n →L[ℝ] Point n =>
      (T (Pi.single c (1 : ℝ)) : Point n)) hBA) p
  dsimp only at hh
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, matToCLM_apply] at hh
  simp only [hw] at hh
  rw [Pi.single_apply] at hh
  exact hh

/-! ### H2-core — the heat operator vanishes where the kernel section is locally zero. -/

/-- **H2-core — `heatOp` vanishes on a local-zero neighborhood of the base point.**  If the kernel
    `H` satisfies `H(·,p,q) =ᶠ 0` in `t` near `τ` AND `H(τ,·,q) =ᶠ 0` in the base point near `p`, then
    `heatOp g gi H τ p q = 0`.  `heatOp = ∂_τ H − Δ_g(H(τ,·))`: the time slot dies by
    `EventuallyEq.deriv_eq`, the space slot by germ-locality of the Laplace–Beltrami operator
    (`laplaceBeltrami_congr_nhds`).  This is the reusable analytic core of any out-of-chart
    zero-extension; it is `Vmap`-agnostic and makes NO regularity demand beyond the two local-zero
    germs (which hold verbatim for a set-gated witness off its closed support). -/
theorem heatOp_eq_zero_of_locally_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p q : Point n)
    (htau : (fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ)))
    (hspace : (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ))) :
    heatOp g gi H τ p q = 0 := by
  unfold heatOp
  have hd : deriv (fun u => H u p q) τ = 0 := by
    rw [htau.deriv_eq]; exact deriv_const τ 0
  have hl : laplaceBeltrami g gi (fun p' => H τ p' q) p
      = laplaceBeltrami g gi (fun _ => (0 : ℝ)) p :=
    QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds g gi _ _ p hspace
  have hz : laplaceBeltrami g gi (fun _ => (0 : ℝ)) p = 0 := by
    simp only [laplaceBeltrami]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hfun : (fun y => pd (fun _ => (0 : ℝ)) j y) = (fun _ => (0 : ℝ)) := by
      funext y; exact pd_const 0 j y
    rw [hfun, pd_const]
    simp only [pd_const, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [hd, hl, hz, sub_zero]

/-! ### H1 — the in-chart per-base-point residual bound, ALL far-point antecedents discharged. -/

/-- **★ H1 — the in-chart per-base-point residual Gaussian bound, FAR-POINT ANTECEDENTS DISCHARGED.**
    J4-93's `globalWitness_residual_bound_inChart_unconditional` (I4) restated with its four per-point
    antecedents at the far point `φ_q v` (`hg1`, `hU`, `hGGi`, `hGiG`) DISCHARGED from the global
    geometric hypotheses (`hg`, `hgnd`, `hinvF`) already in the signature.  The single `τ`-free `(a,b,B)`
    is uniform over `q ∈ K`, and the bound
        `|heatOp g gi H_w τ (φ_q v) q| ≤ B · gaussDdimWide τ v`   (`‖v‖ < r₀`)
    now carries ONLY genuine geometric/heat-side hypotheses.  Pure plumbing: `hg1` is `ContDiff ⊤ ⟹
    ContDiffAt 1`; `hU`/`hGGi` are the global data at `φ_q v`; `hGiG` is `metricInv_left_of_right`. -/
theorem globalWitness_residual_bound_inChart_final (g gi : Point n → Fin n → Fin n → ℝ)
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
      ∀ (τ : ℝ) (q : Point n), q ∈ K → 0 < τ →
        ∃ r₀ > (0 : ℝ), ∀ v : Point n, ‖v‖ < r₀ →
          |heatOp g gi (globalCutoffParametrixWitness Θ u a b (basepointInverseChart g gi hC hK)) τ
              (uniformFlowExp g gi hC hK q v) q|
            ≤ B * gaussDdimWide τ v := by
  obtain ⟨a, b, B, ha, hab, hB, hbound⟩ :=
    globalWitness_residual_bound_inChart_unconditional g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, ?_⟩
  intro τ q hq hτ
  obtain ⟨r₀, hr₀, hboundinner⟩ := hbound τ q hq hτ
  refine ⟨r₀, hr₀, ?_⟩
  intro v hv
  -- Discharge the four far-point antecedents at `φ_q v`.
  refine hboundinner v hv ?_ ?_ ?_ ?_
  · -- hg1 : `ContDiff ⊤ ⟹ ContDiffAt 1` at any point.
    intro a' b'
    exact (hg a' b').contDiffAt.of_le le_top
  · -- hU : global nondegeneracy instantiated at the far point.
    exact hgnd (uniformFlowExp g gi hC hK q v)
  · -- hGGi : the global metric-inverse relation `g·gi = 1` instantiated at the far point.
    intro pp cc
    exact hinvF (uniformFlowExp g gi hC hK q v) pp cc
  · -- hGiG : the OTHER side `gi·g = 1`, from hGGi via `Matrix.mul_eq_one_comm`.
    exact metricInv_left_of_right
      (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
      (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
      (hgnd (uniformFlowExp g gi hC hK q v))
      (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)

end QIQTH.HeatResidualBound
