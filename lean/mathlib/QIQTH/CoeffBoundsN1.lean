/-
  CoeffBoundsN1 — J4-107: discharging / assessing the `N = 1` capstone's two firewalled coefficient
  inputs (`hCoeffU0`/`hCoeffU1`) and building the gated `N = 1` witness `hEzero`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## What the `N = 1` capstone (`OrderOneGeometry.gatedWitnessN1_hEboundW_le_vanVleck`) demands.

  Two `totalRadialO1_coeff` `O(r²)` bounds at the van-Vleck profile, at the base profile `u` and at the
  SHIFTED profile `u' = fun j => u (j+1)`:
      (hCoeffU0)  |totalRadialO1_coeff g̃_q g̃⁻¹_q (vanVleck g) u v|  ≤ C₀·rncRadialSq v
      (hCoeffU1)  |totalRadialO1_coeff g̃_q g̃⁻¹_q (vanVleck g) u' v| ≤ C₁·rncRadialSq v
  plus (via the `hInt` slot) the vanishing `hEzero` of the gated `N = 1` witness at nonpositive time.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  (K1)  `vanVleck_foldedCoeff_zero_flat` — the van-Vleck RNC FLATNESS `∂_e w₀(0) = 0` for the DeWitt
        leading folded coefficient `w₀ = (vanVleck g)^{−1/2}·u₀` with `u₀ ≡ 1`.  Proved from the genuine
        ambient gauge inputs `∂g(0) = 0` (`hdg0`) and the RNC frame `g(0) = δ` (`hg0`): the entrywise
        `∂g(0)=0` gives (Jacobi's formula, `hasDerivAt_matrix_det`) `∂(det g)(0)=0`, hence via the
        `√`/`⁻¹`/`rpow` chain `∂((vanVleck g)^{−1/2})(0)=0`.  This is EXACTLY the `hw0flat` datum that
        `UniformCoeffBound.uniformCoeff_bound` (J4-87) consumes but J4-101 CARRIED — now DISCHARGED for
        the concrete van-Vleck profile.
  (K1)  `hCoeffU0_vanVleck` — `hCoeffU0` DISCHARGED: `uniformCoeff_bound` at `Θ := vanVleck g`,
        `u := transportCoeff T` with `hw0flat := vanVleck_foldedCoeff_zero_flat`.

  ## K2 verdict (assessment — the load-bearing subtlety; consult gpt-5.6-sol high, confirmed).

  `hCoeffU1` (the `O(r²)` bound at the SHIFTED profile `u'`) is **GENERICALLY FALSE** and CANNOT be
  discharged by the `uniformCoeff_bound` route.  Reason: the `u'`-profile's leading folded coefficient is
  `w₁ = (vanVleck g)^{−1/2}·u₁`, and
      ∂_e w₁(0) = ∂_e((vanVleck g)^{−1/2})(0)·u₁(0) + (vanVleck g)^{−1/2}(0)·∂_e u₁(0) = 0 + 1·∂_e u₁(0),
  while differentiating the transport ODE `(1 + r∂_r)u₁ = T u₀` at `0` gives `2∂_e u₁(0) = ∂_e(T u₀)(0)`,
  generically `≠ 0`.  Hence the `radialDeriv(w₁)(v) = Σ vᵢ ∂ᵢw₁(v)` summand of `totalRadialO1_coeff` at
  `u'` carries a NON-vanishing `O(r)` linear part, so `|totalRadialO1_coeff … u' v| ~ O(r)`, NOT `O(r²)`.
  The `uniformCoeff_bound` route needs `∂w₁(0)=0` (its `hw0flat` at the shifted profile), which is false.

  CHEAPEST SOUND ROUTE (assessed, NOT fully landed here — the re-plumb touches the chain lemma
  `OrderOneTower.T1`, forbidden to edit in this increment): prove the `O(r)` bound at `u'` (a mirror of
  `uniformCoeff_bound` MINUS the flatness term), then in `T1` estimate the `τ·R₀[u']` branch directly via
  the width margin `r·G_a ≤ C·√τ·G_b`, giving `τ·R₀[u'] = O(τ·√τ·gauss)`, and fold with
  `τ·√τ ≤ (1+t)·τ` on `(0,t]` (`tau_mul_sqrt_le_affine` below) into the affine `(B₀+B₁τ)` / `(C·(1+t))`
  capstone shape.  The folding inequality `tau_mul_sqrt_le_affine` — the arithmetic core of the re-fold —
  is landed below as a reusable brick; the `O(r)` shifted-profile coefficient bound and the `T1` re-plumb
  are the remaining follow-on work.

  (K3)  `heatOp_gatedWitnessN1_eq_zero_of_nonpos` — the gated `N = 1` witness `hEzero`: for `1 ≤ n`, at
        `τ ≤ 0` the heat operator of the gated order-1 witness vanishes (the Gaussian kills the profile,
        so the spatial slot is `Δ` of `0`; the `∂_τ` slot is `0` for `τ<0` by local constancy and at
        `τ=0` by the `Set.Iic 0` derivative-uniqueness junk-convention argument — no diagonal case split).

  All hypotheses genuine (satisfiable by `g = δ`, `T` arbitrary); NONE is the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformCoeffBound
import QIQTH.VanVleck
import QIQTH.ParametrixFunction
import QIQTH.JacobiFormula
import QIQTH.OrderNResidual
import QIQTH.GlobalHunifAssembly
import QIQTH.TrueHeatKernel
import QIQTH.HeatTransportRecursion
import QIQTH.ModelIntegrableW

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### K1 — the van-Vleck RNC flatness `∂_e w₀(0) = 0`. -/

/-- **★ J4-107 (K1) — THE VAN-VLECK RNC FLATNESS, DISCHARGED.**  For the DeWitt leading folded
    coefficient `w₀ = foldedCoeff (vanVleck g) (transportCoeff T) 0 = (vanVleck g)^{−1/2}` (`u₀ ≡ 1`),
    every first partial vanishes at the RNC centre:  `∀ e, pd w₀ e 0 = 0`.

    ROUTE (chain rule along the coordinate curve `s ↦ Function.update 0 e s`):
    * the ambient gauge `∂g(0)=0` (`hdg0`) makes each entry-curve `s ↦ g(·) i j` have zero derivative at
      `0`, so the matrix curve has zero derivative, and Jacobi's formula
      (`JacobiFormula.hasDerivAt_matrix_det`) gives `∂(det g)(0) = tr(adj·0) = 0`;
    * the RNC frame `g(0)=δ` (`hg0`) gives `det(g 0)=1>0`, so `√`, `⁻¹`, `rpow(-½)` are all differentiable
      along the curve, and each contributes a factor of the (vanishing) inner derivative.
    Genuine inputs `hg`/`hdg0`/`hg0` (satisfiable by `g = δ`); none is the conclusion. -/
theorem vanVleck_foldedCoeff_zero_flat (g : Point n → Fin n → Fin n → ℝ)
    (T : (Point n → ℝ) → (Point n → ℝ))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∀ e, pd (foldedCoeff (vanVleck g) (transportCoeff T) 0) e (0 : Point n) = 0 := by
  intro e
  set p : ℝ := -(1 : ℝ) / 2 with hp
  -- reduce the folded coefficient to the pure rpow (`u₀ ≡ 1`).
  have hfold : foldedCoeff (vanVleck g) (transportCoeff T) 0
      = fun y => (vanVleck g y) ^ p := by
    funext y; simp only [foldedCoeff, transportCoeff_zero, mul_one, hp]
  rw [hfold]
  -- `det (g 0) = 1`.
  have hdet0 : Matrix.det (g 0) = 1 := by
    have h1 : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      funext i j; rw [hg0 i j, Matrix.one_apply]
    rw [h1, Matrix.det_one]
  -- the coordinate curve.
  set c : ℝ → Point n := Function.update (0 : Point n) e with hc
  have hc0 : c 0 = (0 : Point n) := by
    funext k; simp only [hc, Function.update_apply]; by_cases h : k = e <;> simp [h]
  -- entrywise: the entry curve has zero derivative at `0`.
  have hentry : ∀ i j : Fin n, HasDerivAt (fun s => g (c s) i j) 0 0 := by
    intro i j
    rw [hc]
    have hd : DifferentiableAt ℝ (fun t => g (Function.update (0 : Point n) e t) i j) 0 :=
      PdiffAt_of_contDiff (fun y => g y i j) (hg i j) e 0
    have hval : deriv (fun t => g (Function.update (0 : Point n) e t) i j) 0 = 0 := hdg0 i j e
    have h := hd.hasDerivAt
    rwa [hval] at h
  -- the matrix curve has zero derivative at `0`.
  have hW : HasDerivAt (fun s => (g (c s) : Matrix (Fin n) (Fin n) ℝ))
      (0 : Matrix (Fin n) (Fin n) ℝ) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    have := hentry i j
    simpa [Matrix.zero_apply] using this
  -- Jacobi: `∂(det g)(0) = 0`.
  have hdet : HasDerivAt (fun s => Matrix.det (g (c s))) 0 0 := by
    have hj := QIQTH.JacobiFormula.hasDerivAt_matrix_det
      (fun s => (g (c s) : Matrix (Fin n) (Fin n) ℝ))
      (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) (τ := 0) hW
    simpa [Matrix.mul_zero, Matrix.trace_zero] using hj
  have hdetc0 : Matrix.det (g (c 0)) = 1 := by rw [hc0]; exact hdet0
  -- `√ det`.
  have hsqrt : HasDerivAt (fun s => Real.sqrt (Matrix.det (g (c s)))) 0 0 := by
    have := hdet.sqrt (by rw [hdetc0]; norm_num)
    simpa using this
  have hsqrtc0 : Real.sqrt (Matrix.det (g (c 0))) = 1 := by rw [hdetc0]; exact Real.sqrt_one
  -- `(√ det)⁻¹ = vanVleck g`.
  have hinv : HasDerivAt (fun s => (Real.sqrt (Matrix.det (g (c s))))⁻¹) 0 0 := by
    have := hsqrt.inv (by rw [hsqrtc0]; norm_num)
    simpa using this
  have hvv : HasDerivAt (fun s => vanVleck g (c s)) 0 0 := by
    simpa only [vanVleck] using hinv
  have hvvc0 : vanVleck g (c 0) = 1 := by
    simp only [vanVleck, hc0, hdet0, Real.sqrt_one, inv_one]
  -- `rpow (-½)`.
  have hrpow : HasDerivAt (fun s => (vanVleck g (c s)) ^ p) 0 0 := by
    have := hvv.rpow_const (p := p) (Or.inl (by rw [hvvc0]; norm_num))
    simpa using this
  -- conclude `pd = deriv = 0`.
  simp only [pd, Pi.zero_apply]
  exact hrpow.deriv

/-- **★ J4-107 (K1) — `hCoeffU0` DISCHARGED at the van-Vleck profile.**  The base-profile `O(r²)`
    coefficient bound the `N = 1` capstone consumes, now a theorem from ONLY the geometric data
    (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`), the folded-leading-coefficient smoothness
    `hw0smooth` (`= hw 0` in the capstone), and the genuine ambient RNC gauge inputs `hdg0` (`∂g(0)=0`)
    and `hg0` (`g(0)=δ`).  Fires `UniformCoeffBound.uniformCoeff_bound` (J4-87) with its `hw0flat` slot
    filled by `vanVleck_foldedCoeff_zero_flat`.  NOT `a₁ = R/6`. -/
theorem hCoeffU0_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (T : (Point n → ℝ) → (Point n → ℝ))
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff (vanVleck g) (transportCoeff T) 0))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c0 : ℝ, 0 ≤ C_c0 ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (vanVleck g) (transportCoeff T) v|
        ≤ C_c0 * rncRadialSq v :=
  uniformCoeff_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g) (transportCoeff T)
    hw0smooth (vanVleck_foldedCoeff_zero_flat g T hg hdg0 hg0)

/-! ### K3 — the gated `N = 1` witness `hEzero` (vanishing at nonpositive time). -/

/-- **★ J4-107 (K3) — THE GATED `N = 1` WITNESS `hEzero`.**  For `1 ≤ n`, the heat operator of the
    gated order-`1` global-cutoff witness vanishes at every nonpositive time:
        `∀ τ ≤ 0, ∀ p q, heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)) τ p q = 0`.
    This is the exact `hEzero` slot `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas` (and the
    `hInt`/Levi tower) consumes.  ROUTE: the Gaussian `gaussDdim` vanishes at `τ ≤ 0` for `n ≥ 1`
    (`ModelIntegrableW.gaussDdim_eq_zero_of_nonpos`), so the gated witness kernel is IDENTICALLY `0` for
    every `s ≤ 0` (`hker0`).  The spatial `Δ`-slot is then `Δ` of the zero field (`laplaceBeltrami_const`),
    and the `∂_τ`-slot is `0`: for `τ < 0` the section is locally `0` on `Iio 0` (`EventuallyEq.deriv_eq`),
    and at `τ = 0` the section is `0` on `Set.Iic 0`, so its within-derivative is `0`; if the section is
    differentiable at `0` its full derivative agrees (`uniqueDiffWithinAt_Iic`), and otherwise `deriv = 0`
    by the junk convention — NO diagonal (`Vmap q p = 0`) case split.  Genuine `1 ≤ n`; NOT `a₁ = R/6`. -/
theorem heatOp_gatedWitnessN1_eq_zero_of_nonpos (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 1 ≤ n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)) τ p q = 0 := by
  -- the gated witness vanishes at nonpositive time.
  have hker0 : ∀ s : ℝ, s ≤ 0 → ∀ p' q' : Point n,
      gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) s p' q' = 0 := by
    intro s hs p' q'
    have hwit : globalCutoffParametrixWitnessN 1 Θ u a b Vmap s p' q' = 0 := by
      simp only [globalCutoffParametrixWitnessN, heatParametrix,
        gaussDdim_eq_zero_of_nonpos hn hs, zero_mul, mul_zero]
    simp only [gatedKernel]
    split_ifs <;> simp [hwit]
  intro τ hτ p q
  set Kn : ℝ → Point n → Point n → ℝ :=
    gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) with hKn
  -- the spatial `Δ`-slot: `Δ` of the zero field.
  have hlap : laplaceBeltrami g gi (fun x => Kn τ x q) p = 0 := by
    have hzero : (fun x => Kn τ x q) = (fun _ => (0 : ℝ)) := by
      funext x; exact hker0 τ hτ x q
    rw [hzero]; exact QIQTH.HeatTransportRecursion.laplaceBeltrami_const g gi 0 p
  -- the `∂_τ`-slot.
  have hderiv : deriv (fun s => Kn s p q) τ = 0 := by
    set φ : ℝ → ℝ := fun s => Kn s p q with hφ
    rcases lt_or_eq_of_le hτ with hτ0 | hτ0
    · -- `τ < 0`: locally zero on `Iio 0`.
      have hnbhd : Set.Iio (0 : ℝ) ∈ 𝓝 τ := isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hτ0)
      have heq : φ =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnbhd] with s hs using hker0 s (le_of_lt (Set.mem_Iio.mp hs)) p q
      rw [heq.deriv_eq, deriv_const]
    · -- `τ = 0`: `Set.Iic 0` within-derivative uniqueness.
      subst hτ0
      by_cases hd : DifferentiableAt ℝ φ 0
      · have huniq := uniqueDiffWithinAt_Iic (0 : ℝ)
        have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic (0 : ℝ)) 0 :=
          hasDerivWithinAt_const (0 : ℝ) (Set.Iic (0 : ℝ)) (0 : ℝ)
        have hwithin : HasDerivWithinAt φ 0 (Set.Iic (0 : ℝ)) 0 :=
          hbase.congr (fun s hs => hker0 s hs p q) (hker0 0 le_rfl p q)
        rw [← hd.derivWithin huniq]
        exact hwithin.derivWithin huniq
      · exact deriv_zero_of_not_differentiableAt hd
  -- assemble.
  simp only [heatOp, hderiv, hlap, sub_zero]

/-! ### K2 — the folding-inequality brick for the `τ·√τ` re-fold at the shifted profile. -/

/-- **★ J4-107 (K2) — THE `τ·√τ` FOLDING INEQUALITY.**  For `0 < τ ≤ t`,  `τ·√τ ≤ (1+t)·τ`.  This is the
    arithmetic core that folds the shifted-profile `τ·R₀[u'] = O(τ·√τ·gauss)` residual branch (which the
    `O(r)`-only coefficient bound at `u'` produces via the width margin `r·G_a ≤ C·√τ·G_b`) back into the
    affine `(C·(1+t))` shape the `N = 1` capstone requires.  Proof: `√τ ≤ √t ≤ 1+t`.  Genuine `0<τ≤t`. -/
theorem tau_mul_sqrt_le_affine {t τ : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) :
    τ * Real.sqrt τ ≤ (1 + t) * τ := by
  have ht0 : 0 ≤ t := le_trans hτ.le hτt
  have hsqrtt : Real.sqrt t ≤ 1 + t := by
    rw [show (1 : ℝ) + t = Real.sqrt ((1 + t) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtτ : Real.sqrt τ ≤ 1 + t := le_trans (Real.sqrt_le_sqrt hτt) hsqrtt
  calc τ * Real.sqrt τ ≤ τ * (1 + t) := mul_le_mul_of_nonneg_left hsqrtτ hτ.le
    _ = (1 + t) * τ := by ring

end QIQTH.HeatResidualBound
