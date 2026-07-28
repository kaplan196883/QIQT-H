/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# `FrameComponentsSecondDeriv` — the second-order (`C²`) regularity of the frame Jacobi components (`hY2`)

`hY2` is the last deep primitive of the van-Vleck `−Ric` radial ODE
(`vanVleck_ricci_frame_reduced2`): for each `j i`, near `s₀`, the *named first derivative*
`deriv (frameComponent g γ e V j i)` itself has a derivative, i.e. the frame Jacobi component is
`C²`.  Since

  `frameComponent g γ e V j i s = ∑_a ∑_b g(γ s)_{ab} · (V j s).1^a · e_i(s)^b`,

each summand is a TRIPLE PRODUCT of three real factors, and its second derivative exists iff each
factor is `C²`.  This file builds a small, reusable **second-order germ calculus** `C2germ`
(differentiable near `s₀`, with a differentiable derivative near `s₀` — exactly the germ needed for
`hY2`), closed under `+`, `·`, finite `∑`, and produced by `ContDiffAt ℝ 2`; assembles the frame
Jacobi component's `C²` germ from the three factor germs (the **second product rule**,
`frameComponent_c2germ`); and discharges the metric factor `g∘γ` (`C²` via `g` `C^∞` ∘ `expTube` `C²`).

The remaining two factors are the genuine analytic sub-primitives:

* `V.1^a` — `C²` from the coordinate Jacobi ODE (`jacobiVariation_secondOrder_nhds` on the surfaced
  exp-flow `Φ`-data): `frameVarComp_c2germ`;
* `e_i^b` — `C²` from the parallel-transport ODE (`covariantDerivAlong = 0`, `hpar`) differentiated
  once: `parallelFrameComp_c2germ`.

Feeding all three into `frameComponent_c2germ` gives the `hY2` germ unconditionally FROM the frame
construction data `(hg∘γ, Φ, he, hpar)` — see the capstone `frameComponent_hY2_of_frameData`.  The
only obstruction to wiring this into `vanVleck_ricci_frame_reduced2` to make van-Vleck `−Ric`
literally unconditional is that that theorem's `∃ e V` existential does not (yet) SURFACE the frame
parallelism `hpar` (it surfaces `he` and the `Φ`-data, so `V`'s factor IS dischargeable there).

⚠ NOT the heat-kernel `a₁ = R/6` coefficient (which additionally needs the M5/M6 curvature layers).
Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRicciFrameReduced2
import QIQTH.FrameComponentsHexp
import QIQTH.FrameComponentsDeriv
import QIQTH.VanVleckRicciReduced
import QIQTH.CovariantJacobi
import QIQTH.JacobiSecondOrderLocal
import QIQTH.ExpFlowJacobi
import QIQTH.ParallelFrameExpTube
import QIQTH.ExpMapContDiff2
import QIQTH.ExpJacobianRescale

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ### The second-order germ calculus `C2germ` -/

/-- **Second-order germ.**  A real function `f` is `C²` at `s₀` in the germ sense used by `hY2`:
    `f` is differentiable near `s₀` and its (named) derivative `deriv f` is differentiable near `s₀`.
    This is exactly the data needed to conclude `HasDerivAt (deriv f) (deriv (deriv f) τ) τ` for `τ`
    near `s₀`. -/
def C2germ (f : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  (∀ᶠ τ in nhds s₀, DifferentiableAt ℝ f τ) ∧
  (∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (deriv f) τ)

/-- The `hY2`-shaped consequence of a `C²` germ: the named first derivative has a derivative near
    `s₀`, with value the named second derivative. -/
theorem C2germ.hasDerivAt_deriv_ev {f : ℝ → ℝ} {s₀ : ℝ} (h : C2germ f s₀) :
    ∀ᶠ τ in nhds s₀, HasDerivAt (deriv f) (deriv (deriv f) τ) τ :=
  h.2.mono (fun _ hτ => hτ.hasDerivAt)

/-- `ContDiffAt ℝ 2` supplies a `C²` germ. -/
theorem c2germ_of_contDiffAt {f : ℝ → ℝ} {s₀ : ℝ} (hf : ContDiffAt ℝ 2 f s₀) : C2germ f s₀ := by
  obtain ⟨u, hUopen, hs₀u, hcd⟩ := hf.contDiffOn' (le_refl (2 : WithTop ℕ∞)) (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ s₀), Set.univ_inter] at hcd
  have hUnhds : u ∈ nhds s₀ := hUopen.mem_nhds hs₀u
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableOn ℝ f u := hcd.differentiableOn (by norm_num)
    filter_upwards [hUnhds] with s hs using (hd s hs).differentiableAt (hUopen.mem_nhds hs)
  · have hderiv_cdo : ContDiffOn ℝ 1 (deriv f) u := hcd.deriv_of_isOpen hUopen (by norm_num)
    have hd : DifferentiableOn ℝ (deriv f) u := hderiv_cdo.differentiableOn (by norm_num)
    filter_upwards [hUnhds] with s hs using (hd s hs).differentiableAt (hUopen.mem_nhds hs)

/-- The constant-zero function has a `C²` germ. -/
theorem c2germ_zero {s₀ : ℝ} : C2germ (fun _ : ℝ => (0 : ℝ)) s₀ := by
  refine ⟨Filter.Eventually.of_forall (fun _ => differentiableAt_const 0), ?_⟩
  have hderiv : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext s; simp
  rw [hderiv]
  exact Filter.Eventually.of_forall (fun _ => differentiableAt_const 0)

/-- `C²` germs are closed under addition. -/
theorem C2germ.add {f h : ℝ → ℝ} {s₀ : ℝ} (hf : C2germ f s₀) (hh : C2germ h s₀) :
    C2germ (fun s => f s + h s) s₀ := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hh.1] with τ h1 h2 using h1.add h2
  · -- near each `τ`, `deriv (f+h) = deriv f + deriv h`; the RHS is differentiable
    have hpt : ∀ᶠ σ in nhds s₀,
        deriv (fun s => f s + h s) σ = deriv f σ + deriv h σ := by
      filter_upwards [hf.1, hh.1] with σ hfσ hhσ using deriv_add hfσ hhσ
    filter_upwards [eventually_eventually_nhds.2 hpt, hf.2, hh.2]
      with τ heqτ hf2 hh2
    exact (hf2.add hh2).congr_of_eventuallyEq heqτ

/-- `C²` germs are closed under multiplication (the **second product rule**). -/
theorem C2germ.mul {f h : ℝ → ℝ} {s₀ : ℝ} (hf : C2germ f s₀) (hh : C2germ h s₀) :
    C2germ (fun s => f s * h s) s₀ := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hh.1] with τ h1 h2 using h1.mul h2
  · -- near each `τ`, `deriv (f·h) = deriv f · h + f · deriv h`; the RHS is differentiable
    have hpt : ∀ᶠ σ in nhds s₀,
        deriv (fun s => f s * h s) σ = deriv f σ * h σ + f σ * deriv h σ := by
      filter_upwards [hf.1, hh.1] with σ hfσ hhσ using deriv_mul hfσ hhσ
    filter_upwards [eventually_eventually_nhds.2 hpt, hf.1, hf.2, hh.1, hh.2]
      with τ heqτ hf1 hf2 hh1 hh2
    exact ((hf2.mul hh1).add (hf1.mul hh2)).congr_of_eventuallyEq heqτ

/-- `C²` germs are closed under finite sums. -/
theorem C2germ.sum {ι : Type*} {f : ι → ℝ → ℝ} {s₀ : ℝ} (s : Finset ι)
    (h : ∀ i, C2germ (f i) s₀) : C2germ (fun x => ∑ i ∈ s, f i x) s₀ := by
  classical
  induction s using Finset.induction with
  | empty => simpa only [Finset.sum_empty] using (c2germ_zero (s₀ := s₀))
  | insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a).add ih

/-! ### The frame Jacobi component's `C²` germ (assembly / second product rule) -/

/-- **The frame Jacobi component is `C²` from the three factor `C²` germs.**  Given that near `s₀`
    each of the metric factor `g(γ ·)_{ab}`, the variation component `(V j ·).1^a`, and the frame
    component `e_i(·)^b` is `C²`, the frame Jacobi component
    `frameComponent g γ e V j i = ∑_a ∑_b g(γ ·)_{ab} (V j ·).1^a e_i(·)^b` is `C²`.  This is the
    second product rule applied over the double `(a,b)`-sum. -/
theorem frameComponent_c2germ (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n) {s₀ : ℝ} (j i : Fin n)
    (hg : ∀ a b, C2germ (fun s => g (γ s) a b) s₀)
    (hV : ∀ a, C2germ (fun s => (V j s).1 a) s₀)
    (he : ∀ b, C2germ (fun s => e i s b) s₀) :
    C2germ (frameComponent g γ e V j i) s₀ := by
  show C2germ (fun s => ∑ a, ∑ b, g (γ s) a b * (V j s).1 a * e i s b) s₀
  refine C2germ.sum (f := fun a s => ∑ b, g (γ s) a b * (V j s).1 a * e i s b) Finset.univ
    (fun a => ?_)
  refine C2germ.sum (f := fun b s => g (γ s) a b * (V j s).1 a * e i s b) Finset.univ (fun b => ?_)
  exact ((hg a b).mul (hV a)).mul (he b)

/-- **`hY2`, the second-derivative germ of the frame Jacobi component, from the three factor `C²`
    germs.**  This is exactly the `hY2` hypothesis of `vanVleck_ricci_frame_reduced2` for the single
    pair `(j, i)`. -/
theorem frameComponent_hY2germ (g : Point n → Fin n → Fin n → ℝ) (γ : ℝ → Point n)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n) {s₀ : ℝ} (j i : Fin n)
    (hg : ∀ a b, C2germ (fun s => g (γ s) a b) s₀)
    (hV : ∀ a, C2germ (fun s => (V j s).1 a) s₀)
    (he : ∀ b, C2germ (fun s => e i s b) s₀) :
    ∀ᶠ τ in nhds s₀,
      HasDerivAt (deriv (frameComponent g γ e V j i))
        (deriv (deriv (frameComponent g γ e V j i)) τ) τ :=
  (frameComponent_c2germ g γ e V j i hg hV he).hasDerivAt_deriv_ev

/-! ### Factor 1 — the metric factor `g∘γ` is `C²` -/

/-- **The metric factor `g(expTube …)_{ab}` is `C²` near `s₀` (for `|s₀| < 1`).**  Along the ray/tube
    identity `(expTube … s).1 = exp_p(s • v)`, this is `g` (`C^∞`) composed with `exp_p` (`C²` on the
    injectivity ball) composed with the linear ray `s ↦ s • v`, hence `C²`. -/
theorem gComp_expTube_c2germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀ : |s₀| < 1) (a b : Fin n) :
    C2germ (fun s => g (expTube g gi hC p v s).1 a b) s₀ := by
  -- eventual identification of `g∘(expTube).1` with `g∘exp_p(s • v)` near `s₀`
  have hlt1 : ∀ᶠ s in nhds s₀, |s| < 1 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hs₀)
      (fun _ hs => hs)
  have hEq : (fun s => g (expTube g gi hC p v s).1 a b)
      =ᶠ[nhds s₀] (fun s => g (expMap g gi hC p (s • v)) a b) := by
    filter_upwards [hlt1] with s hs
    rw [(expMap_smul_eq_expTube g gi hC p v hv.le hs.le)]
  -- `ContDiffAt ℝ 2` of the `exp_p`-version at `s₀`
  have hnorm : ‖s₀ • v‖ < expRho g gi hC p := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s₀| * ‖v‖ ≤ 1 * ‖v‖ := by
            apply mul_le_mul_of_nonneg_right hs₀.le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < expRho g gi hC p := hv
  have hat : ContDiffAt ℝ 2 (expMap g gi hC p) (s₀ • v) := by
    refine (expMap_contDiffOn_two g gi hC p).contDiffAt (Metric.isOpen_ball.mem_nhds ?_)
    rw [Metric.mem_ball, dist_zero_right]; exact hnorm
  have hray_cdf : ContDiff ℝ (2 : WithTop ℕ∞) (fun s : ℝ => s • v) :=
    contDiff_id.smul contDiff_const
  have hexp : ContDiffAt ℝ 2 (fun s : ℝ => expMap g gi hC p (s • v)) s₀ := by
    simpa only [Function.comp_def] using hat.comp s₀ hray_cdf.contDiffAt
  have hcda : ContDiffAt ℝ 2 (fun s : ℝ => g (expMap g gi hC p (s • v)) a b) s₀ :=
    ((hg a b).contDiffAt.of_le le_top).comp s₀ hexp
  exact c2germ_of_contDiffAt (hcda.congr_of_eventuallyEq hEq)

/-! ### Factor 2 — the variation component `V.1^a` is `C²` (coordinate Jacobi ODE) -/

/-- **The variation component `(V j ·).1^a` is `C²` near an interior `s₀ ∈ (0,1)`.**  From the
    surfaced exp-flow `Φ`-data (`V j s = Φ s (0, e_j)`, `hflow` the first-order geodesic-variation
    system on `[0,1]`), the vector `(Φ · w).1` is differentiable near `s₀` (first-order system) and
    its derivative is differentiable near `s₀` (the coordinate second-order Jacobi ODE
    `jacobiVariation_secondOrder_nhds`, giving `ξ'' = −jacobiOperator`).  Projecting onto the `a`-th
    coordinate gives the `C²` germ. -/
theorem frameVarComp_c2germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hflow : ∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => Φ s z)
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z))
          (Set.Icc (0 : ℝ) 1) t)
    (V : Fin n → ℝ → Point n × Point n)
    (hVeq : ∀ j s, V j s = Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))
    (j a : Fin n) :
    C2germ (fun s => (V j s).1 a) s₀ := by
  set w : Point n × Point n := ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)) with hw
  -- the first-order geodesic-variation system holds `∀ᶠ` near `s₀`
  have hVar_ev : ∀ᶠ τ in nhds s₀,
      IsGeodesicVariationAt g gi (fun s => expTube g gi hC p v s) (fun s => Φ s w) τ := by
    filter_upwards [Ioo_mem_nhds hs₀.1 hs₀.2] with τ hτ
    exact (hflow w τ (Set.mem_Icc.mpr ⟨hτ.1.le, hτ.2.le⟩)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)
  -- rewrite target as the flow-column component
  have hrw : (fun s => (V j s).1 a) = (fun s => (Φ s w).1 a) := by
    funext s; rw [hVeq j s]
  rw [hrw]
  -- projection CLM onto `.1 a`
  have hproj_der : ∀ τ, IsGeodesicVariationAt g gi (fun s => expTube g gi hC p v s)
        (fun s => Φ s w) τ →
      HasDerivAt (fun s => (Φ s w).1 a)
        (((ContinuousLinearMap.proj a).comp (ContinuousLinearMap.fst ℝ (Point n) (Point n)))
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v τ) (Φ τ w))) τ := by
    intro τ hτ
    have h := ((ContinuousLinearMap.proj a).comp
      (ContinuousLinearMap.fst ℝ (Point n) (Point n))).hasFDerivAt.comp_hasDerivAt τ hτ
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply] using h
  -- part 1: `(Φ · w).1 a` differentiable near `s₀`
  have hpart1 : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (fun s => (Φ s w).1 a) τ := by
    filter_upwards [hVar_ev] with τ hτ using (hproj_der τ hτ).differentiableAt
  -- the vector column `(Φ · w).1` differentiable near `s₀` (for the `deriv`↔`proj` swap)
  have hFdiff : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (fun s => (Φ s w).1) τ := by
    filter_upwards [hVar_ev] with τ hτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hτ
    exact (by simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', Prod.fst] using h
      : HasDerivAt (fun s => (Φ s w).1) _ τ).differentiableAt
  -- `deriv (component) = (deriv vector)ᵃ` where the vector is differentiable
  have heq : ∀ᶠ σ in nhds s₀,
      deriv (fun s => (Φ s w).1 a) σ = deriv (fun s => (Φ s w).1) σ a := by
    filter_upwards [hFdiff] with σ hσ
    have hvec : HasDerivAt (fun s => (Φ s w).1) (deriv (fun s => (Φ s w).1) σ) σ := hσ.hasDerivAt
    have hcomp := (ContinuousLinearMap.proj a).hasFDerivAt.comp_hasDerivAt σ hvec
    have : HasDerivAt (fun s => (Φ s w).1 a) (deriv (fun s => (Φ s w).1) σ a) σ := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
    exact this.deriv
  -- part 2: `deriv (component)` differentiable near `s₀`, via the coordinate second-order Jacobi ODE
  have hsecond : ∀ᶠ τ in nhds s₀,
      HasDerivAt (deriv (fun s => (Φ s w).1))
        (-jacobiOperator g gi (expTube g gi hC p v τ).1 (expTube g gi hC p v τ).2
          (Φ τ w).1 (Φ τ w).2) τ := by
    filter_upwards [eventually_eventually_nhds.2 hVar_ev] with τ hτvar
    exact jacobiVariation_secondOrder_nhds g gi hC
      (γ := fun s => expTube g gi hC p v s) (V := fun s => Φ s w) hτvar
  have hpart2 : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (deriv (fun s => (Φ s w).1 a)) τ := by
    filter_upwards [eventually_eventually_nhds.2 heq, hsecond] with τ heqτ hsec
    -- component `a` of the vector second derivative is differentiable
    have hcompsec := (ContinuousLinearMap.proj a).hasFDerivAt.comp_hasDerivAt τ hsec
    have hda : DifferentiableAt ℝ (fun σ => deriv (fun s => (Φ s w).1) σ a) τ := by
      have hdd := hcompsec.differentiableAt
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hdd
    exact hda.congr_of_eventuallyEq heqτ
  exact ⟨hpart1, hpart2⟩

/-! ### Factor 3 — the frame component `e_i^b` is `C²` (parallel-transport ODE) -/

/-- **The geodesic position component `(expTube …).1^j` is `C²` near `s₀` (for `|s₀| < 1`).**  Along
    the ray/tube identity, this is the `j`-th coordinate of `exp_p(s • v)` (`C²` on the ball). -/
theorem expTubePos_c2germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀ : |s₀| < 1) (j : Fin n) :
    C2germ (fun s => (expTube g gi hC p v s).1 j) s₀ := by
  have hlt1 : ∀ᶠ s in nhds s₀, |s| < 1 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_abs continuous_const).mem_nhds hs₀)
      (fun _ hs => hs)
  have hEq : (fun s => (expTube g gi hC p v s).1 j)
      =ᶠ[nhds s₀] (fun s => expMap g gi hC p (s • v) j) := by
    filter_upwards [hlt1] with s hs
    rw [(expMap_smul_eq_expTube g gi hC p v hv.le hs.le)]
  have hnorm : ‖s₀ • v‖ < expRho g gi hC p := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |s₀| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hs₀.le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < expRho g gi hC p := hv
  have hat : ContDiffAt ℝ 2 (expMap g gi hC p) (s₀ • v) := by
    refine (expMap_contDiffOn_two g gi hC p).contDiffAt (Metric.isOpen_ball.mem_nhds ?_)
    rw [Metric.mem_ball, dist_zero_right]; exact hnorm
  have hray_cdf : ContDiff ℝ (2 : WithTop ℕ∞) (fun s : ℝ => s • v) :=
    contDiff_id.smul contDiff_const
  have hexp : ContDiffAt ℝ 2 (fun s : ℝ => expMap g gi hC p (s • v)) s₀ := by
    simpa only [Function.comp_def] using hat.comp s₀ hray_cdf.contDiffAt
  have hcomp : ContDiffAt ℝ 2 (fun s : ℝ => expMap g gi hC p (s • v) j) s₀ := by
    have := (ContinuousLinearMap.proj j : Point n →L[ℝ] ℝ).contDiff.comp_contDiffAt s₀ hexp
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using this
  exact c2germ_of_contDiffAt (hcomp.congr_of_eventuallyEq hEq)

/-- **The frame component `e_i(·)^c` is `C²` near `s₀` (for `|s₀| < 1`), from the parallel-transport
    ODE.**  Parallelism `hpar` (`covariantDerivAlong g gi (expTube.1) (e i) = 0`) gives, in component
    form, the transport ODE

      `deriv (e_i^c) = − ∑_{j,k} Γ^c_{jk}(γ) · (γ^j)' · e_i^k`,

    whose right side is a sum of products of `C¹` functions — `Γ∘γ` (`C^∞ ∘` position curve),
    `(γ^j)' = deriv (position^j)` (`C¹`, i.e. position `C²` via `expTubePos_c2germ`), and `e_i^k`
    (`C¹` via `he`) — hence differentiable near `s₀`.  So `deriv (e_i^c)` is differentiable near `s₀`,
    i.e. `e_i^c` is `C²`. -/
theorem parallelFrameComp_c2germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) {s₀ : ℝ} (hs₀ : |s₀| < 1)
    (e : Fin n → ℝ → Point n)
    (he : ∀ i a, ∀ᶠ τ in nhds s₀,
        HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds s₀,
        covariantDerivAlong g gi (fun s => (expTube g gi hC p v s).1) (e i) τ = 0)
    (i c : Fin n) :
    C2germ (fun s => e i s c) s₀ := by
  -- the RHS of the transport ODE at component `c`
  set RHS : ℝ → ℝ := fun τ => -(∑ j, ∑ k, christoffel g gi c j k ((expTube g gi hC p v τ).1)
      * deriv (fun s => (expTube g gi hC p v s).1 j) τ * e i τ k) with hRHS
  -- position curve derivative (velocity), near `s₀`
  have hs₀2 : s₀ ∈ Set.Ioo (-2 : ℝ) 2 := by
    rw [abs_lt] at hs₀; exact ⟨by linarith [hs₀.1], by linarith [hs₀.2]⟩
  have hposd : ∀ τ ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s => (expTube g gi hC p v s).1) (expTube g gi hC p v τ).2 τ := by
    intro τ hτ
    have h2 := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ
      ((expTube_spec g gi hC p v hv.le).2.1 τ hτ)
    simpa [geodesicField] using h2
  -- part 1 of the germ: `e_i^c` differentiable near `s₀`
  have hpart1 : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (fun s => e i s c) τ := by
    filter_upwards [he i c] with τ hτ using hτ.differentiableAt
  -- the eventual transport identity `deriv (e_i^c) = RHS`
  have heq_deriv : ∀ᶠ τ in nhds s₀, deriv (fun s => e i s c) τ = RHS τ := by
    filter_upwards [hpar i] with τ hτ
    have h := congrFun hτ c
    rw [covariantDerivAlong_apply] at h
    -- h : deriv (e_i^c) τ + ∑∑ … = 0
    have hz : (0 : Point n) c = 0 := rfl
    rw [hz] at h
    have := eq_neg_of_add_eq_zero_left h
    rw [hRHS]; exact this
  -- differentiability of `RHS` near `s₀`
  have hBdiff : ∀ᶠ τ in nhds s₀, ∀ j,
      DifferentiableAt ℝ (deriv (fun s => (expTube g gi hC p v s).1 j)) τ :=
    Filter.eventually_all.2 (fun j => (expTubePos_c2germ g gi hC p v hv hs₀ j).2)
  have hEdiff : ∀ᶠ τ in nhds s₀, ∀ k, DifferentiableAt ℝ (fun s => e i s k) τ :=
    Filter.eventually_all.2 (fun k => (he i k).mono (fun _ hτ => hτ.differentiableAt))
  have hIoo : ∀ᶠ τ in nhds s₀, τ ∈ Set.Ioo (-2 : ℝ) 2 :=
    isOpen_Ioo.mem_nhds hs₀2
  have hRHSdiff : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ RHS τ := by
    filter_upwards [hIoo, hBdiff, hEdiff] with τ hτioo hBτ hEτ
    rw [hRHS]
    refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun j _ => ?_)
    refine DifferentiableAt.fun_sum (fun k _ => ?_)
    have hA : DifferentiableAt ℝ
        (fun s => christoffel g gi c j k ((expTube g gi hC p v s).1)) τ :=
      (hasDerivAt_comp_curve (fun z => christoffel g gi c j k z)
        (fun s => (expTube g gi hC p v s).1) ((expTube g gi hC p v τ).2) τ
        (hC c j k) (hposd τ hτioo)).differentiableAt
    exact (hA.mul (hBτ j)).mul (hEτ k)
  -- part 2 of the germ: `deriv (e_i^c)` differentiable near `s₀` (via the transport identity)
  have hpart2 : ∀ᶠ τ in nhds s₀, DifferentiableAt ℝ (deriv (fun s => e i s c)) τ := by
    filter_upwards [eventually_eventually_nhds.2 heq_deriv, hRHSdiff] with τ heqτ hRτ
    exact hRτ.congr_of_eventuallyEq heqτ
  exact ⟨hpart1, hpart2⟩

/-! ### Capstone — `hY2` discharged from the frame construction data -/

/-- **`hY2` — the frame Jacobi components are `C²` — discharged from the frame construction data.**
    For each `(j, i)`, near an interior `s₀ ∈ (0,1)`, the named first derivative
    `deriv (frameComponent g (expTube.1) e V j i)` has a derivative, i.e. the frame Jacobi component
    is `C²`.  This is exactly the `hY2` hypothesis carried by `vanVleck_ricci_frame_reduced2`.  The
    three factors are discharged: the metric factor `g∘γ` (`gComp_expTube_c2germ`), the variation
    component `V.1^a` (`frameVarComp_c2germ`, from the exp-flow `Φ`-data), and the frame component
    `e_i^b` (`parallelFrameComp_c2germ`, from `he` + `hpar`).  The inputs `Φ`/`hflow`/`hVeq`, `he`,
    `hpar` are exactly the data produced by the repo's frame construction (`expDiff_flow` and
    `parallelFrame_expTube_exists`). -/
theorem frameComponent_hY2_of_frameData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1)
    (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hflow : ∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s => Φ s z)
          (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z))
          (Set.Icc (0 : ℝ) 1) t)
    (hVeq : ∀ j s, V j s = Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))
    (he : ∀ i a, ∀ᶠ τ in nhds s₀,
        HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ)
    (hpar : ∀ i, ∀ᶠ τ in nhds s₀,
        covariantDerivAlong g gi (fun s => (expTube g gi hC p v s).1) (e i) τ = 0) :
    ∀ j i, ∀ᶠ τ in nhds s₀,
      HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
        (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ := by
  have hs₀abs : |s₀| < 1 := by
    rw [abs_lt]; exact ⟨by linarith [hs₀.1], hs₀.2⟩
  intro j i
  refine frameComponent_hY2germ g (fun u => (expTube g gi hC p v u).1) e V j i ?_ ?_ ?_
  · exact fun a b => gComp_expTube_c2germ g gi hC hg p v hv hs₀abs a b
  · exact fun a => frameVarComp_c2germ g gi hC p v hs₀ Φ hflow V hVeq j a
  · exact fun b => parallelFrameComp_c2germ g gi hC p v hv hs₀abs e he hpar i b

end QIQTH.ExpMap
