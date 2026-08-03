/-
  TransportOpSmoothness — J4-174: discharging (and honestly assessing) the TWO operator premises
  `hT` / `hSolve` to which J4-173 (`QIQTH.GeomPTransportAssess.hu_concrete_of_solve_smooth`) reduced
  the transport-coefficient smoothness carry `hu`.  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity-plumbing brick about the smoothness of the DeWitt transport operator and its ray-integral
  solve.  No conclusion-in-disguise; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── RECAP.  `transportCoeff T k` is the DeWitt recursion `u_0 ≡ 1`, `u_{k+1} = radialTransportSolve
     (k+1) (T u_k)`, and (`HeatTransportRecursion`)
        `transportOp Θ g gi v = fun x ↦ Θ x ^ (−½) · laplaceBeltrami g gi (fun y ↦ Θ y ^ (½) · v y) x`,
     with `Θ = vanVleck g`.  J4-173 reduced `hu : ∀k, ContDiff ℝ ⊤ (transportCoeff (transportOp
     (vanVleck g) g gi) k)` to two operator premises via `hu_concrete_of_solve_smooth`:
       • `hT`    — the source operator `transportOp (vanVleck g) g gi` preserves `C^∞`;
       • `hSolve`— `radialTransportSolve k` preserves `C^∞`.

  ── PART A — `hT` FULLY DISCHARGED.  `transportOp (vanVleck g) g gi` is a composite of purely
     `ContDiff`-preserving building blocks:
       • the van-Vleck prefactors `Θ^{±½}` are `C^∞` wherever `det g > 0` (`vanVleck_contDiffAt`
         + `ContDiffAt.rpow_const_of_ne`, using `vanVleck_pos` for the non-vanishing) — this is the
         `foldedCoeff_vanVleck_contDiff` pattern;
       • `laplaceBeltrami g gi` maps `C^∞` to `C^∞` (`laplaceBeltrami_contDiff`, new here): it is a
         finite algebraic combination of `gi` (`hgi`), Christoffel symbols (`christoffel_contDiff`),
         and first/second partials of the field (`contDiff_pd`, iterated).
     Delivered: `laplaceBeltrami_contDiff`, `transportOp_preserves_contDiff`, and `hT_discharged` in
     the EXACT premise shape of `hu_concrete_of_solve_smooth`.

  ── PART B — `hSolve` : the ray-integral rung + the honest analytic wall.  `radialTransportSolve k f
     v = ∫₀¹ s^{k−1}·f(s•v) ds` is an explicit parametric interval integral, so its regularity is
     differentiation-under-the-integral.  Delivered here:
       • `radialTransportSolve_hasFDerivAt` — the pointwise first-order rung: for `f ∈ C¹`,
         `HasFDerivAt (radialTransportSolve k f)` with derivative the ray integral of the (down-shifted)
         chain-rule integrand.  This IS the induction-step identity `∂(I_m f) = I_{m+1}(∂f)` at order 1.
       • `radialTransportSolve_differentiable`, `radialTransportSolve_fderiv`, and
         `radialTransportSolve_contDiff_one` — the full C¹ rung.
     ★ THE ANALYTIC WALL (why the FULL tower — hence `hu` — is NOT closed here).  In the toolchain's
       `WithTop ℕ∞`, the smoothness level `(⊤ : WithTop ℕ∞) = ω` is the ANALYTIC level (see
       `contDiff_succ_iff_fderiv`'s `n = ω → AnalyticOnNhd` clause).  The van-Vleck/Laplace building
       blocks are all real-analytic, so Part A closes at ω; but the ray INTEGRAL of an analytic family
       is analytic only by a theorem Mathlib does NOT have (parametric analytic integrals).  The
       finite-order differentiation-under-integral induction reaches every `ContDiff ℝ (N : ℕ)` (hence
       `∞`), but NOT `ω`.  So the ω-level `hSolve` premise is a genuine ANALYTIC gap, not mere weight;
       `hu` therefore stays HONESTLY reduced (Part A discharged, `hSolve` carried at the sharpened
       "analyticity of the ray integral" residue).  The C¹ rung below is the first proven step of the
       finite-order tower.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RadialTransport
import QIQTH.ParametrixFunction
import QIQTH.HeatTransportRecursion
import QIQTH.LaplaceBeltrami
import QIQTH.VanVleck
import QIQTH.ChristoffelSmooth

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialTransport
open scoped BigOperators Topology Interval

namespace QIQTH.TransportOpSmoothness

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — `hT` : the DeWitt transport operator preserves `C^∞`.
    ############################################################################### -/

/-- **`laplaceBeltrami_contDiff` — the Laplace–Beltrami operator preserves `C^∞`.**  For `C^∞` metric
    `g` (`hg`) and inverse metric `gi` (`hgi`) and a `C^∞` field `f` (`hf`),
      `Δ_g f = ∑ i ∑ j gi_{ij}·(∂ᵢ∂ⱼ f − ∑ k Γ^k_{ij}·∂_k f)`
    is `C^∞`: a finite algebraic combination of `gi` (`hgi`), Christoffel symbols
    (`christoffel_contDiff` from `hg`/`hgi`), and first/second partials of `f` (`contDiff_pd`,
    iterated).  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (f : Point n → ℝ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => laplaceBeltrami g gi f x) := by
  simp only [laplaceBeltrami]
  refine ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => ?_))
  refine (hgi i j).mul ?_
  refine (contDiff_pd (fun y => pd f j y) (contDiff_pd f hf j) i).sub ?_
  exact ContDiff.sum (fun k _ =>
    (christoffel_contDiff g gi hg hgi k i j).mul (contDiff_pd f hf k))

/-- **★ `transportOp_preserves_contDiff` — the DeWitt transport source preserves `C^∞`.**  For a `C^∞`
    metric/inverse-metric pair with `det g > 0` everywhere, the operator
      `transportOp (vanVleck g) g gi f = Θ^{−½}·Δ_g(Θ^{½}·f)`,   `Θ = vanVleck g`,
    maps `C^∞ f` to `C^∞`.  The prefactors `Θ^{±½}` are `C^∞` via `vanVleck_contDiffAt` +
    `ContDiffAt.rpow_const_of_ne` (non-vanishing from `vanVleck_pos`), the inner conjugated field is
    their product with `f`, and `Δ_g` preserves `C^∞` (`laplaceBeltrami_contDiff`).  NOT `a₁ = R/6`. -/
theorem transportOp_preserves_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (f : Point n → ℝ) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (transportOp (vanVleck g) g gi f) := by
  have hΘpow : ∀ c : ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => (vanVleck g y) ^ c) := by
    intro c
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (vanVleck_contDiffAt g hg v (hgpos v)).rpow_const_of_ne
      (ne_of_gt (vanVleck_pos g v (hgpos v)))
  have hinner : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => (vanVleck g y) ^ ((1 / 2 : ℝ)) * f y) := (hΘpow _).mul hf
  have hlap : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun x => laplaceBeltrami g gi (fun y => (vanVleck g y) ^ ((1 / 2 : ℝ)) * f y) x) :=
    laplaceBeltrami_contDiff g gi hg hgi _ hinner
  unfold transportOp
  exact (hΘpow _).mul hlap

/-- **★★ `hT_discharged` — the `hT` premise of `hu_concrete_of_solve_smooth`, PROVED.**  Delivers the
    exact operator-level `C^∞`-preservation of `transportOp (vanVleck g) g gi` demanded as the `hT`
    input of `QIQTH.GeomPTransportAssess.hu_concrete_of_solve_smooth`, reduced to the banked geometric
    facts `{hg, hgi, hgpos}`.  Fully closes the `hT` half of the `hu` reduction.  NOT `a₁ = R/6`. -/
theorem hT_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∀ f : Point n → ℝ, ContDiff ℝ (⊤ : WithTop ℕ∞) f
        → ContDiff ℝ (⊤ : WithTop ℕ∞) (transportOp (vanVleck g) g gi f) :=
  fun f hf => transportOp_preserves_contDiff g gi hg hgi hgpos f hf

/-! ###############################################################################
    ### PART B — `hSolve` : the ray-integral C¹ rung (differentiation under the integral).
    ############################################################################### -/

/-- **★ `radialTransportSolve_hasFDerivAt` — the first-order rung / induction-step identity.**  For a
    `C^∞` (in particular `C¹`) field `f`, the ray-integral solve `radialTransportSolve k f v =
    ∫₀¹ s^{k−1}·f(s•v) ds` is (Fréchet) differentiable at every `v₀`, with derivative the ray integral
    of the CHAIN-RULE integrand:
      `D(radialTransportSolve k f)(v₀) = ∫₀¹ s^{k−1}·(s·Df(s•v₀)) ds`.
    The extra factor `s` is the tangent of the ray `s•v₀`; this is exactly the operator identity
    `∂(I_m f) = I_{m+1}(∂f)` at order 1.  Proof: Mathlib's dominated-derivative Leibniz rule
    `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, with the `s`-integrand's
    `v`-derivative dominated over the compact ray tube `[0,1] × closedBall v₀ 1` by the continuity of
    `Df` (from `f ∈ C¹`).  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_hasFDerivAt (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (v₀ : Point n) :
    HasFDerivAt (radialTransportSolve k f)
      (∫ s in (0:ℝ)..1, s ^ (k - 1) • (s • fderiv ℝ f (s • v₀))) v₀ := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ f x :=
    fun x => (hf.differentiable (by simp)).differentiableAt
  have hcfd : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv (by simp)
  -- uniform bound on `‖Df‖` over the compact ray tube.
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall v₀ 1)).exists_bound_of_continuousOn
    (f := fun p : ℝ × Point n => fderiv ℝ f (p.1 • p.2))
    ((hcfd.comp (continuous_fst.smul continuous_snd)).continuousOn)
  -- continuity of the integrand and its parameter-derivative (for each base point).
  have hcF : ∀ v : Point n, Continuous (fun s : ℝ => s ^ (k - 1) * f (s • v)) :=
    fun v => (continuous_pow (k - 1)).mul (hf.continuous.comp (continuous_id.smul continuous_const))
  have hcF' : ∀ v : Point n,
      Continuous (fun s : ℝ => s ^ (k - 1) • (s • fderiv ℝ f (s • v))) :=
    fun v => (continuous_pow (k - 1)).smul
      (continuous_id.smul (hcfd.comp (continuous_id.smul continuous_const)))
  -- the dominating bound.
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
      ∀ x ∈ Metric.closedBall v₀ 1,
        ‖s ^ (k - 1) • (s • fderiv ℝ f (s • x))‖ ≤ (fun _ => M) s := by
    refine Filter.Eventually.of_forall (fun s hs x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [norm_smul, norm_smul]
    have hb := hM (s, x) ⟨⟨le_of_lt hs0, hs1⟩, hx⟩
    have h1 : ‖s ^ (k - 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (le_of_lt hs0) hs1
    have h2 : ‖s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs0)]; exact hs1
    calc ‖s ^ (k - 1)‖ * (‖s‖ * ‖fderiv ℝ f (s • x)‖)
        ≤ 1 * (1 * M) :=
          mul_le_mul h1 (mul_le_mul h2 hb (norm_nonneg _) (by norm_num))
            (by positivity) (by norm_num)
      _ = M := by ring
  -- the pointwise `v`-derivative of the integrand (chain rule on the ray).
  have hderiv : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
      ∀ x ∈ Metric.closedBall v₀ 1,
        HasFDerivAt (fun x => s ^ (k - 1) * f (s • x))
          (s ^ (k - 1) • (s • fderiv ℝ f (s • x))) x := by
    refine Filter.Eventually.of_forall (fun s _ x _ => ?_)
    have hray : HasFDerivAt (fun x : Point n => s • x)
        (s • ContinuousLinearMap.id ℝ (Point n)) x := (hasFDerivAt_id x).const_smul s
    have hfd : HasFDerivAt f (fderiv ℝ f (s • x)) (s • x) := (hdiffbl (s • x)).hasFDerivAt
    have hcomp := hfd.comp x hray
    have hcomp_eq : (fderiv ℝ f (s • x)).comp (s • ContinuousLinearMap.id ℝ (Point n))
        = s • fderiv ℝ f (s • x) := by
      ext w
      simp [ContinuousLinearMap.smul_apply]
    rw [hcomp_eq] at hcomp
    have hcm := hcomp.const_smul (s ^ (k - 1))
    simpa only [smul_eq_mul] using hcm
  -- assemble the dominated Leibniz rule.
  have main := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun v s => s ^ (k - 1) * f (s • v))
    (F' := fun v s => s ^ (k - 1) • (s • fderiv ℝ f (s • v)))
    (bound := fun _ => M) (a := 0) (b := 1) (μ := volume)
    (s := Metric.closedBall v₀ 1) (x₀ := v₀)
    (Metric.closedBall_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall (fun v => (hcF v).aestronglyMeasurable))
    ((hcF v₀).intervalIntegrable 0 1)
    ((hcF' v₀).aestronglyMeasurable)
    hbound intervalIntegrable_const hderiv
  exact main

/-- **`radialTransportSolve_differentiable`** — the solve is (Fréchet) differentiable everywhere for
    `C^∞ f`.  Immediate from `radialTransportSolve_hasFDerivAt`.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_differentiable (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    Differentiable ℝ (radialTransportSolve k f) :=
  fun v₀ => (radialTransportSolve_hasFDerivAt k f hf v₀).differentiableAt

/-- **`radialTransportSolve_fderiv`** — the `fderiv` of the solve, read off from
    `radialTransportSolve_hasFDerivAt`.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_fderiv (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (v₀ : Point n) :
    fderiv ℝ (radialTransportSolve k f) v₀
      = ∫ s in (0:ℝ)..1, s ^ (k - 1) • (s • fderiv ℝ f (s • v₀)) :=
  (radialTransportSolve_hasFDerivAt k f hf v₀).fderiv

/-- **★ `radialTransportSolve_contDiff_one` — the C¹ rung of the `hSolve` tower.**  For `C^∞ f`,
    `radialTransportSolve k f` is `C¹`.  Via `contDiff_one_iff_fderiv`: differentiability
    (`radialTransportSolve_differentiable`) plus continuity of the `fderiv`, which by
    `radialTransportSolve_fderiv` is the parametric ray integral of `(v,s) ↦ s^{k−1}·(s·Df(s•v))` —
    continuous by `continuous_parametric_intervalIntegral_of_continuous'` on the jointly continuous
    (CLM-valued) integrand.  This is the first PROVEN step of the finite-order tower; see the header
    ANALYTIC WALL note for why the ω-level `hSolve` (hence `hu`) is not closed by this route.
    NOT `a₁ = R/6`. -/
theorem radialTransportSolve_contDiff_one (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) :
    ContDiff ℝ 1 (radialTransportSolve k f) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨radialTransportSolve_differentiable k f hf, ?_⟩
  have hcfd : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv (by simp)
  have huc : Continuous (Function.uncurry
      (fun (v : Point n) (s : ℝ) => s ^ (k - 1) • (s • fderiv ℝ f (s • v)))) := by
    have he : (Function.uncurry
        (fun (v : Point n) (s : ℝ) => s ^ (k - 1) • (s • fderiv ℝ f (s • v))))
        = fun p : Point n × ℝ => p.2 ^ (k - 1) • (p.2 • fderiv ℝ f (p.2 • p.1)) := rfl
    rw [he]
    exact (continuous_snd.pow (k - 1)).smul
      (continuous_snd.smul (hcfd.comp (continuous_snd.smul continuous_fst)))
  have hcont : Continuous
      (fun v => ∫ s in (0:ℝ)..1, s ^ (k - 1) • (s • fderiv ℝ f (s • v))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huc 0 1
  exact hcont.congr (fun v => (radialTransportSolve_fderiv k f hf v).symm)

end QIQTH.TransportOpSmoothness

section AxiomChecks
open QIQTH.TransportOpSmoothness
#print axioms laplaceBeltrami_contDiff
#print axioms transportOp_preserves_contDiff
#print axioms hT_discharged
#print axioms radialTransportSolve_hasFDerivAt
#print axioms radialTransportSolve_differentiable
#print axioms radialTransportSolve_fderiv
#print axioms radialTransportSolve_contDiff_one
end AxiomChecks
