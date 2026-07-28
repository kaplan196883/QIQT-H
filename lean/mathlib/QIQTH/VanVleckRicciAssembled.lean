/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# VanVleckRicciAssembled — the van-Vleck determinant `−Ric` equation with the FRAME + h4 + hrel assembled

The headline interior van-Vleck determinant equation
```
  d²/ds²[log det g̃(s • v)] |_{s = s₀}  =  −2·Ric − 2·Sh + 2·n / s₀²
```
on the REAL exp-map Jacobian `g̃ = Jᵀ (g∘exp) J`, with the FRAME DATA discharged and the two
generic-point ingredients it consumes — the frame Raychaudhuri value `h4` (`d²(log det Y) = −Ric − Sh`)
and the frame-decomposition germ `hrel` (`log det B =ᶠ log det Y − ½ log det (g∘exp)`) — both
supplied from already-landed bricks, wired together via `vanVleck_ray_secondDeriv_ricci_at`.

## The one genuinely new ingredient — `frameComponent_logdet_hrel`

`vanVleck_ray_secondDeriv_ricci_at` takes an abstract frame Jacobi matrix `Y` together with the
germ identity `hrel`.  `vanVleck_h4_assembled` produces `h4` for the SPECIFIC frame matrix
`Y s = Matrix.of (fun k j => frameComponent g γ e V j k s)`, whose entry
`Y_{kj} = frameComponent_{jk} = ∑_{a,b} g(γ s)_{ab} (V j s)₁_a e_k(s)_b = ⟨V_j, e_k⟩_g`.  This file
supplies the MATCHING `hrel` for that same `Y`, from three genuine geometric germs near `s₀`:

* `hγ`   — the ray/tube identification `(expTube p v s)₁ = exp_p(s • v)`;
* `hBV`  — the radial Jacobi link `(V j s)₁_a = (s • D exp_p|_{s•v})_{aj}` (the flow columns are the
  radial Jacobi fields, i.e. `s` times the exp differential — the standard `J(s) = s·(d exp)_{sv}` law);
* `hortho` — `g`-orthonormality of the frame `e` (`∑_{a,b} g_{ab} e_i^a e_k^b = δ_{ik}`).

With `B := s • D exp_p|_{s•v}`, `G := g∘exp`, `E := (e_i^a)`, the frame-component matrix satisfies
`Y = (Bᵀ G E)ᵀ`, so `det Y = det B · det G · det E`; orthonormality (`Eᵀ G E = 1`) gives
`(det E)²·det G = 1`, hence `log det E = −½ log det G`, and therefore
`log det B = log det Y − ½ log det G` — exactly the `hrel` germ.  (No matrix inverse is needed:
`det Y = det B·det G·det E` is proved by `det_transpose`/`det_mul`, and `gorthonormal_det_sq`
supplies the metric factor.)

## What remains carried after this brick

The assembly `vanVleck_ricci_assembled` is CONDITIONAL only on:
* `hY2`, `hu_ev` — the two genuine follow-on arrows of `vanVleck_h4_assembled` (C²-regularity of the
  frame Jacobi components and the no-conjugate invertibility of the frame Jacobi matrix), and
* the genuine geometric/analytic side-conditions of `vanVleck_ray_secondDeriv_ricci_at` for THIS
  frame (`hγ`/`hBV`/`hortho`/positivity feeding `hrel`, the determinant split `hsplit`, the various
  differentiability and second-derivative `HasDerivAt` germs).

Discharging `hY2`/`hu_ev` (follow-on bricks) makes the frame-Raychaudhuri side unconditional; the
remaining side-conditions are standard Riemannian regularity, NOT the conclusion, NONE vacuous.

⚠ This is NOT the heat-kernel `a₁ = R/6` coefficient.  Axiom-free (`propext`, `Classical.choice`,
`Quot.sound` only).
-/
import Mathlib
import QIQTH.VanVleckRayRicciAt
import QIQTH.VanVleckH4Assembled
import QIQTH.OrthonormalFrameDet
import QIQTH.FrameComponentsHexp
import QIQTH.JacobianDet
import QIQTH.ExpJacobianRescale

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.JacobianDet QIQTH.PullbackMetric Finset Matrix

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **The frame-decomposition `hrel` for the frame Jacobi matrix `Y = Matrix.of frameComponent`.**

    For the frame Jacobi matrix `Y_{kj} = frameComponent g γ e V j k = ⟨V_j, e_k⟩_g` built from a
    `g`-orthonormal frame `e` and the exp-flow Jacobi columns `V`, given near `s₀`:

    * `hγ`     — `(expTube p v s)₁ = exp_p(s • v)`;
    * `hBV`    — the radial Jacobi link `(V j s)₁_a = (s • D exp_p|_{s•v})_{aj}`;
    * `hortho` — `g`-orthonormality `∑_{a,b} g(exp)_{ab} e_i^a e_k^b = δ_{ik}`;
    * positivity of `det E`, `det (g∘exp)`, and `det (s • D exp_p|_{s•v})`,

    the log-determinant germ identity
    ```
      log det (s • D exp_p|_{s•v})  =ᶠ  log det Y  −  ½ · log det (g∘exp)
    ```
    holds near `s₀`.  This is exactly the `hrel` hypothesis of `vanVleck_ray_secondDeriv_ricci_at`
    for `Y = Matrix.of (fun k j => frameComponent g (expTube …)₁ e V j k)`.  Proof: `Y = (Bᵀ G E)ᵀ`
    gives `det Y = det B · det G · det E`; orthonormality gives `(det E)² · det G = 1`; combine. -/
theorem frameComponent_logdet_hrel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n) {s₀ : ℝ}
    (hγ : ∀ᶠ s in nhds s₀, (expTube g gi hC p v s).1 = expMap g gi hC p (s • v))
    (hBV : ∀ᶠ s in nhds s₀, ∀ a j,
        (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j)
    (hortho : ∀ᶠ s in nhds s₀, ∀ i k,
        (∑ a, ∑ b, g (expMap g gi hC p (s • v)) a b * e i s a * e k s b)
          = if i = k then (1 : ℝ) else 0)
    (hEdet : ∀ᶠ s in nhds s₀,
        (Matrix.of (fun a i => e i s a) : Matrix (Fin n) (Fin n) ℝ).det ≠ 0)
    (hGdet : ∀ᶠ s in nhds s₀,
        0 < (Matrix.of (fun a b => g (expMap g gi hC p (s • v)) a b)
              : Matrix (Fin n) (Fin n) ℝ).det)
    (hBdet : ∀ᶠ s in nhds s₀,
        0 < ((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det) :
    (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))
      =ᶠ[nhds s₀]
    (fun s => Real.log ((Matrix.of (fun k j =>
          frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
        : Matrix (Fin n) (Fin n) ℝ).det)
      - (1/2 : ℝ) * Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det)) := by
  filter_upwards [hγ, hBV, hortho, hEdet, hGdet, hBdet]
    with s hγs hBVs horthos hEdets hGdets hBdets
  -- the four matrices at `s`
  set Bmat : Matrix (Fin n) (Fin n) ℝ := s • expJacobianMat g gi hC p (s • v) with hBmat
  set Gmat : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun a b => g (expMap g gi hC p (s • v)) a b) with hGmat
  set Emat : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a i => e i s a) with hEmat
  set Ymat : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun k j => frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
    with hYmat
  -- (1) orthonormality in matrix form: `Eᵀ G E = 1`.
  have hE1 : Ematᵀ * Gmat * Emat = 1 := by
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hEmat, hGmat, Matrix.of_apply,
      Matrix.one_apply]
    rw [← horthos i k]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  -- (2) the frame-component matrix is `(Bᵀ G E)ᵀ`.
  have hYM : Ymat = (Bmatᵀ * Gmat * Emat)ᵀ := by
    ext k j
    rw [Matrix.transpose_apply, Matrix.mul_apply]
    simp only [hYmat, Matrix.of_apply, frameComponent, Matrix.mul_apply, Matrix.transpose_apply,
      hGmat, hEmat]
    -- LHS: ∑ a ∑ b g(γ s)_{ab} (V j s)₁_a e_k(s)_b ; RHS: ∑ b (∑ a Bmat_{aj} Gmat_{ab}) Emat_{bk}
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hγs, hBVs b j]
    ring
  -- (3) `det Y = det B · det G · det E`.
  have hdetY : Ymat.det = Bmat.det * Gmat.det * Emat.det := by
    rw [hYM, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  -- (4) the orthonormal metric factor: `log det E = −½ log det G`.
  have hEne : Emat.det ≠ 0 := hEdets
  have hGpos : 0 < Gmat.det := hGdets
  have hBpos : 0 < Bmat.det := hBdets
  have hlogsq : Real.log (Emat.det ^ 2) = - Real.log Gmat.det :=
    gorthonormal_logdet Gmat Emat hE1 hGpos
  rw [Real.log_pow] at hlogsq
  have hlogE : Real.log Emat.det = -(1/2 : ℝ) * Real.log Gmat.det := by
    push_cast at hlogsq; linarith
  -- (5) assemble the log identity.
  have hLHS : ((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det = Bmat.det := rfl
  rw [hLHS, hdetY, Real.log_mul (mul_ne_zero hBpos.ne' hGpos.ne') hEne,
    Real.log_mul hBpos.ne' hGpos.ne', hlogE]
  ring

/-- **The interior van-Vleck determinant `−Ric` equation with the FRAME + h4 + hrel assembled.**

    For a smooth symmetric metric `g` (symmetric inverse `gi`, a genuine matrix inverse), base point
    `p`, and `‖v‖ < expRho`, there is a radius `δ > 0` such that at every interior parameter
    `s₀ ∈ (0, δ)` there are a parallel orthonormal frame `e` and an exp-flow Jacobi variation `V` for
    which, GIVEN the two genuine follow-on arrows of `vanVleck_h4_assembled` (`hY2` = C²-regularity of
    the frame Jacobi components, `hu_ev` = no-conjugate invertibility) together with the genuine
    geometric germs feeding the frame-decomposition `hrel` (`hγ`/`hBV`/`hortho` + positivity) and the
    standard analytic side-conditions of `vanVleck_ray_secondDeriv_ricci_at` (determinant split,
    differentiability, second-derivative `HasDerivAt` germs), the second ray-derivative of
    `log det g̃` at `s₀` equals
    ```
      d²/ds²[log det g̃(s • v)] |_{s = s₀}  =  −2·Ric − 2·Sh + 2·n / s₀²
    ```
    with `Ric = ∑_{σν} Ric_{σν}(γ s₀) γ'^σ γ'^ν` and `Sh = tr((Y'Y⁻¹)²)`, `Y` the frame Jacobi matrix.
    The frame Raychaudhuri value `h4` comes from `vanVleck_h4_assembled`, the frame-decomposition germ
    `hrel` from `frameComponent_logdet_hrel`; both are wired into `vanVleck_ray_secondDeriv_ricci_at`.
    Discharging `hY2`/`hu_ev` (follow-on bricks) makes the frame-Raychaudhuri side unconditional; the
    remaining side-conditions are standard Riemannian regularity, NONE vacuous.  NOT `a₁ = R/6`. -/
theorem vanVleck_ricci_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgisymm : ∀ y μ ν, gi y μ ν = gi y ν μ)
    (hginv : ∀ y a μ, (∑ b, g y a b * gi y μ b) = if a = μ then (1 : ℝ) else 0)
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p)
    (hgpd : Matrix.PosDef (g p : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ s₀ ∈ Set.Ioo (0 : ℝ) δ,
      ∃ (e : Fin n → ℝ → Point n) (V : Fin n → ℝ → Point n × Point n),
        -- exposed frame-side data (orthonormality of `e` and its `C¹` regularity) for a downstream
        -- discharge of the frame-Jacobi invertibility `hu_ev` and log-det differentiability `hYev`:
        (∀ᶠ s in nhds s₀, ∀ i k,
            (∑ a, ∑ b, g (expMap g gi hC p (s • v)) a b * e i s a * e k s b)
              = if i = k then (1 : ℝ) else 0) ∧
        (∀ i a, ∀ᶠ τ in nhds s₀,
            HasDerivAt (fun s => e i s a) (deriv (fun s => e i s a) τ) τ) ∧
        -- exposed exp-flow data `Φ` (threaded from `vanVleck_h4_assembled`) for a downstream
        -- discharge of the radial-Jacobi link `hBV` (`V = Φ(0,e_j)`):
        (∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
            Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
            (∀ (z : Point n × Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
                HasDerivWithinAt (fun s => Φ s z)
                  (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t z))
                  (Set.Icc (0 : ℝ) 1) t) ∧
            (∀ j s, V j s = Φ s ((0 : Point n), (Pi.single j (1 : ℝ) : Point n)))) ∧
        -- the two carried follow-on arrows of `vanVleck_h4_assembled`:
        ((∀ j i, ∀ᶠ τ in nhds s₀,
            HasDerivAt (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i))
              (deriv (deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j i)) τ) τ) →
        (∀ᶠ s in nhds s₀,
            IsUnit (Matrix.of (fun k j =>
                frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ)) →
        -- the carried geometric germs feeding `hrel` (`hortho`/`hEdet` are now discharged inside):
        (∀ᶠ s in nhds s₀, (expTube g gi hC p v s).1 = expMap g gi hC p (s • v)) →
        (∀ᶠ s in nhds s₀, ∀ a j,
            (V j s).1 a = (s • expJacobianMat g gi hC p (s • v)) a j) →
        (∀ᶠ s in nhds s₀,
            0 < (Matrix.of (fun a b => g (expMap g gi hC p (s • v)) a b)
                  : Matrix (Fin n) (Fin n) ℝ).det) →
        (∀ᶠ s in nhds s₀,
            0 < ((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det) →
        -- the carried analytic side-conditions of `vanVleck_ray_secondDeriv_ricci_at`:
        ((fun s : ℝ => Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))
          =ᶠ[nhds s₀] (fun s => 2 * Real.log (expJacobianDet g gi hC p (s • v))
            + Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) →
        (∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log (expJacobianDet g gi hC p (u • v))) s) →
        (∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (u • v)) a b).det)) s) →
        (∀ᶠ s in nhds s₀, 0 < expJacobianDet g gi hC p (s • v)) →
        (∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) u).det)) s) →
        (∀ᶠ s in nhds s₀, DifferentiableAt ℝ (fun u => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k u)
              : Matrix (Fin n) (Fin n) ℝ).det)) s) →
        (HasDerivAt (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) (deriv (deriv (fun s : ℝ => Real.log (expJacobianDet g gi hC p (s • v)))) s₀) s₀) →
        (HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of fun a b => g (expMap g gi hC p (s • v)) a b).det))) s₀) s₀) →
        (HasDerivAt (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) (deriv (deriv (fun s : ℝ => Real.log (((fun t : ℝ => t • expJacobianMat g gi hC p (t • v)) s).det))) s₀) s₀) →
        (HasDerivAt (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ).det)))
          (deriv (deriv (fun s : ℝ => Real.log ((Matrix.of (fun k j =>
            frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
              : Matrix (Fin n) (Fin n) ℝ).det))) s₀) s₀) →
          deriv (deriv (fun s : ℝ =>
              Real.log ((Matrix.of fun i j => expPullbackMetric g gi hC p (s • v) i j).det))) s₀
            = - 2 * (∑ σ, ∑ ν, ricci g gi σ ν (expTube g gi hC p v s₀).1
                    * (expTube g gi hC p v s₀).2 σ * (expTube g gi hC p v s₀).2 ν)
              - 2 * (((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)
                  * ((Matrix.of (fun k j =>
                      deriv (frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k) s₀))
                    * (Matrix.of (fun k j =>
                      frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s₀))⁻¹)).trace
              + 2 * (n : ℝ) / s₀ ^ 2) := by
  obtain ⟨δ, hδ, hbody⟩ := vanVleck_h4_assembled g gi hC hg hgsymm hgisymm hginv p v hv hgpd
  refine ⟨δ, hδ, fun s₀ hs₀ => ?_⟩
  obtain ⟨e, V, hortho, hEdet, he, hΦdata, hh4⟩ := hbody s₀ hs₀
  refine ⟨e, V, hortho, he, hΦdata, fun hY2 hu_ev hγ hBV hGdet hBdet hsplit hLJev hLmev hpos hLBev hYev
    hLJ2 hLm2 hLB2 hLY2 => ?_⟩
  have h4 := hh4 hY2 hu_ev
  have hrel := frameComponent_logdet_hrel g gi hC p v e V hγ hBV hortho hEdet hGdet hBdet
  exact vanVleck_ray_secondDeriv_ricci_at g gi hC p v
    (fun s => (Matrix.of (fun k j =>
        frameComponent g (fun u => (expTube g gi hC p v u).1) e V j k s)
      : Matrix (Fin n) (Fin n) ℝ))
    hs₀.1 hsplit hLJev hLmev hpos hLBev hrel hYev hLJ2 hLm2 hLB2 hLY2 h4

end QIQTH.ExpMap

