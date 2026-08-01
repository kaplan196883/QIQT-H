/-
  ResidualChartTransport — J4-89: the CHART-TRANSPORT core for the E-identification (`Vmap`) gap.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Census / scope (the honest map — this file's raison d'être).

  The conditional `a₁ = R/6` capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual`
  (`TrueKernelA1Reduced.lean:153`) needs a GLOBAL width-2 residual bound
      `hEboundW : ∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ C · baseKernelW 2 0 τ p q`,
  where `E := heatOp g gi H τ p q = ∂_τ H − Δ_g H` is the parametrix residual in the ORIGINAL chart
  (`heatOp g gi K t x y = deriv (fun u => K u x y) t − laplaceBeltrami g gi (fun p => K t p y) x`).
  Here `H` is a FUNCTION-VARIABLE (only pinned on the diagonal by `hHdiag`); the residual uses the
  GLOBAL-chart `laplaceBeltrami g gi`.

  The reduction chain is CLOSED down to one geometric fact:
    * `RecenterReduction.hEboundW_of_uniform_perBasePoint` : `hEboundW` ⟸ the per-base-point family
      `∀ q τ, 0<τ → ∀ p, |E τ p q| ≤ C · gaussDdim (2τ) (p − q)`.
    * `RecenterHEboundW.hEboundW_of_perBasePoint_bound` : the same, via `Vmap` (`Vmap q p = exp_q⁻¹ p`)
      from `hunif : |E τ p q| ≤ B · gaussDdimWide τ (Vmap q p)` + `hcoord` (`Vmap → p−q` Gaussian).
    * J4-88 `UniformTauResidual.cutoffResidual_uniformFlow_unconditional_tau` delivers, τ-free, the WIDE
      Gaussian bound on the RECENTERED cutoff residual `|χ·∂_τH₀ − Δ_{g̃_q}(χ·H₀(τ))(v)| ≤ B·G_wide τ v`,
      with `g̃_q = uniformFlowPullbackMetric g gi hC hK q` and `v` the q-centered coordinate.

  THE MISSING PIECE (the `E`-identification / `Vmap` gap) is the NATURALITY of Laplace–Beltrami under
  the recentering diffeomorphism `φ_q = uniformFlowExp g gi hC hK q`:
      `Δ_{g̃_q}(f ∘ φ_q)(v) = (Δ_g f)(φ_q v)`   (∀ v on the exp-ball, `f ∈ C²`),
  which — together with the recentred definition `H(τ,p,q) = χ(Vmap q p)·H₀(τ, Vmap q p)` and the
  `∂_τ`-commutation — turns `heatOp g gi H τ p q` at `v = Vmap q p` into exactly J4-88's recentred
  cutoff residual.

  ⚠ STRUCTURAL VERDICT (GPT-5.6-sol, high; and the `RecenterReduction` Step-1 finding).  In the repo's
  NON-DIVERGENCE coordinate form `Δ_g f = ∑ g^{ij}(∂_i∂_j f − Γ^k_{ij}∂_k f)`, pointwise naturality is
  genuinely D²φ-dependent (the `∂_i∂_j(f∘φ)` term spins off `∑_a ∂_a f·∂_i∂_jφ^a`, which must cancel
  the pullback-Christoffel transformation term).  For `φ_q = uniformFlowExp` — defined by
  `Classical.choose` of a geodesic ODE, with ONLY `fderiv`-nondegeneracy on a uniform ball available and
  NO pointwise D²φ / Christoffel-transformation / inverse-Jacobian relations proven — the FULL pointwise
  naturality brick is INFRASTRUCTURE-SCALE, not a one-lemma gap.  It is therefore FIREWALLED here.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  The tractable GENUINE cores of the transport, isolating exactly the D²φ-free content:
    * `pd_comp` — the FIRST-DERIVATIVE chain rule for the coordinate partial under composition:
        `∂_i(f ∘ φ)(x) = ∑_a (∂_a f)(φ x) · ∂_i(φ·a)(x)`   (pointwise, `f`/`φ` merely `DifferentiableAt`).
    * `pullbackInv_trace_contraction` — the PULLBACK-INVERSE trace contraction (pure pointwise linear
        algebra, avoiding any `Dφ⁻¹`): for the congruence pullback `gt = Jᵀ(g∘φ)J` (`J` = Jacobian CLM,
        invertible) with genuine inverses `Gi` of `g` and `gti` of `g̃`,
        `∑_{i,j} J_i^a · gti_{ij} · J_j^b = Gi^{ab}`.  This removes the "inverse-Jacobian relation not
        proven" obstruction cleanly.

  FIREWALLED (exact): the contracted Christoffel transformation law for `uniformFlowExp`, the pointwise
  second-jet D²(uniformFlowExp), the assembled pointwise naturality, and the resulting global
  E-identification.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.ExpMap
import QIQTH.PullbackNondegFromFDeriv
import QIQTH.ChristoffelSmooth

open Finset
open QIQTH.Curvature QIQTH.ExpMap QIQTH.PullbackMetric
open scoped Matrix

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ### Part 1 — the first-derivative chain rule for `pd` under composition. -/

/-- **FIRST-DERIVATIVE CHAIN RULE for the coordinate partial under composition.**  For a scalar `f` and
    a map `φ : Point n → Point n`, both differentiable at the relevant points,
        `∂_i(f ∘ φ)(x) = ∑_a (∂_a f)(φ x) · ∂_i(φ·a)(x)`,
    where `φ·a = fun y => φ y a` is the `a`-th component.  Pointwise; the ONLY hypotheses are
    `DifferentiableAt` of `f` at `φ x` and of `φ` at `x` (no `ContDiff ⊤`).  This is the reusable
    first-order layer of the recenter chart-transport (`f ∘ uniformFlowExp_q`). -/
theorem pd_comp (f : Point n → ℝ) (φ : Point n → Point n) (i : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    pd (fun y => f (φ y)) i x = ∑ a, pd f a (φ x) * pd (fun y => φ y a) i x := by
  have hcompDiff : DifferentiableAt ℝ (fun y => f (φ y)) x := hf.comp x hφ
  -- component-wise partials of `φ`.
  have hcomp_a : ∀ a : Fin n,
      pd (fun y => φ y a) i x = (fderiv ℝ φ x (Pi.single i 1)) a := by
    intro a
    let P : Point n →L[ℝ] ℝ := ContinuousLinearMap.proj a
    have hpa : HasFDerivAt (fun p : Point n => P p) P (φ x) := P.hasFDerivAt
    have hHF : HasFDerivAt (fun y => φ y a) (P.comp (fderiv ℝ φ x)) x :=
      hpa.comp x hφ.hasFDerivAt
    rw [pd_eq_fderiv (fun y => φ y a) i x hHF.differentiableAt, hHF.fderiv]
    rfl
  -- expand `∂_i(f∘φ)` via the fderiv chain rule, then `fderiv_apply_eq_sum_pd`.
  have hstep1 : pd (fun y => f (φ y)) i x
      = fderiv ℝ f (φ x) (fderiv ℝ φ x (Pi.single i 1)) := by
    rw [pd_eq_fderiv (fun y => f (φ y)) i x hcompDiff]
    have hc : fderiv ℝ (fun y => f (φ y)) x = (fderiv ℝ f (φ x)).comp (fderiv ℝ φ x) :=
      fderiv_comp x hf hφ
    rw [hc]; rfl
  rw [hstep1, fderiv_apply_eq_sum_pd f (φ x) (fderiv ℝ φ x (Pi.single i 1)) hf]
  exact Finset.sum_congr rfl fun a _ => by rw [hcomp_a a]

/-! ### Part 2 — the pullback-inverse trace contraction (pure linear algebra, no `Dφ⁻¹`). -/

/-- **PULLBACK-INVERSE TRACE CONTRACTION.**  Let `J : Point n →L[ℝ] Point n` be an invertible Jacobian
    CLM (`jacMat J a i = (J e_i)_a`), let `Gi` be a genuine (two-sided) inverse of the ambient metric
    `G`, and let `g̃` be the CONGRUENCE PULLBACK `g̃_{ij} = ∑_{a,b} G_{ab}·(J e_i)_a·(J e_j)_b`
    (= `Jᵀ G J`, the shape of `uniformFlowPullbackMetric`) with a genuine inverse `gti`.  Then the
    Jacobian-contracted inverse pullback returns the ambient inverse:
        `∑_{i,j} (J e_i)_a · gti_{ij} · (J e_j)_b = Gi^{ab}`,
    i.e. `J g̃⁻¹ Jᵀ = G⁻¹`.  This is the D²φ-FREE half of Laplace–Beltrami naturality (the metric-inverse
    transformation `g̃^{ij}(v) = ∑(Dφ⁻¹)(Dφ⁻¹)g^{ab}` in contracted form), proved by pure pointwise
    matrix algebra — WITHOUT ever forming `Dφ⁻¹`.  All hypotheses genuine (the inverse relations and the
    congruence shape), none the conclusion. -/
theorem pullbackInv_trace_contraction
    (J : Point n →L[ℝ] Point n) (G Gi gt gti : Fin n → Fin n → ℝ)
    (hJ : IsUnit J)
    (hGGi : ∀ i c, (∑ b, G i b * Gi b c) = if i = c then (1 : ℝ) else 0)
    (hgtdef : ∀ i j, gt i j = ∑ a, ∑ b, G a b * jacMat J a i * jacMat J b j)
    (hgtinv : ∀ i j, (∑ k, gti i k * gt k j) = if i = j then (1 : ℝ) else 0)
    (a b : Fin n) :
    (∑ i, ∑ j, jacMat J a i * gti i j * jacMat J b j) = Gi a b := by
  classical
  -- Wrap the raw arrays as matrices (matrix `*` = `Matrix.mul`, not pointwise).
  set JM : Matrix (Fin n) (Fin n) ℝ := jacMat J with hJMdef
  set GM : Matrix (Fin n) (Fin n) ℝ := Matrix.of G with hGMdef
  set GiM : Matrix (Fin n) (Fin n) ℝ := Matrix.of Gi with hGiMdef
  set gtM : Matrix (Fin n) (Fin n) ℝ := Matrix.of gt with hgtMdef
  set gtiM : Matrix (Fin n) (Fin n) ℝ := Matrix.of gti with hgtiMdef
  -- `JM` is a unit, hence so are its determinant and the transpose determinant.
  have hJM : IsUnit JM := by
    rw [hJMdef]
    exact (isUnit_matToCLM_iff (jacMat J)).mp (by rw [matToCLM_jacMat]; exact hJ)
  have hJdet : IsUnit JM.det := (Matrix.isUnit_iff_isUnit_det JM).mp hJM
  have hJTdet : IsUnit JMᵀ.det := by rw [Matrix.det_transpose]; exact hJdet
  -- `GiM = GM⁻¹` from the two-sided inverse relation `GM * GiM = 1`.
  have hGM1 : GM * GiM = 1 := by
    ext i c; rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hGMdef, hGiMdef, Matrix.of_apply]; exact hGGi i c
  have hGiM : GM⁻¹ = GiM := Matrix.inv_eq_right_inv hGM1
  -- `gtiM = gtM⁻¹` from the left inverse relation `gtiM * gtM = 1`.
  have hgt1 : gtiM * gtM = 1 := by
    ext i j; rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hgtiMdef, hgtMdef, Matrix.of_apply]; exact hgtinv i j
  have hgtiM : gtM⁻¹ = gtiM := Matrix.inv_eq_left_inv hgt1
  -- the congruence shape `gtM = JMᵀ * GM * JM`.
  have hgteq : gtM = JMᵀ * GM * JM := by
    ext i j
    have hR : (JMᵀ * GM * JM) i j
        = ∑ b, ∑ a, jacMat J a i * G a b * jacMat J b j := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Matrix.transpose_apply]
      simp only [hJMdef, hGMdef, Matrix.of_apply]
    rw [hR]
    simp only [hgtMdef, Matrix.of_apply, hgtdef i j]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  -- the matrix identity `J g̃⁻¹ Jᵀ = G⁻¹`.
  have hinv : (JMᵀ * GM * JM)⁻¹ = JM⁻¹ * (GM⁻¹ * (JMᵀ)⁻¹) := by
    rw [Matrix.mul_inv_rev (JMᵀ * GM) JM, Matrix.mul_inv_rev JMᵀ GM]
  have hmat : JM * gtiM * JMᵀ = GiM := by
    rw [← hgtiM, hgteq, hinv]
    rw [← Matrix.mul_assoc JM JM⁻¹ (GM⁻¹ * (JMᵀ)⁻¹), Matrix.mul_nonsing_inv JM hJdet,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul JMᵀ hJTdet, Matrix.mul_one]
    exact hGiM
  -- extract the entry `(a,b)` and reassemble the target sum.
  calc ∑ i, ∑ j, jacMat J a i * gti i j * jacMat J b j
      = ∑ i, JM a i * ∑ j, gtiM i j * JMᵀ j b := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.transpose_apply]
        simp only [hJMdef, hgtiMdef, Matrix.of_apply]; ring
    _ = ∑ i, JM a i * (gtiM * JMᵀ) i b := by
        refine Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_apply]
    _ = (JM * (gtiM * JMᵀ)) a b := (Matrix.mul_apply).symm
    _ = (JM * gtiM * JMᵀ) a b := by rw [Matrix.mul_assoc]
    _ = GiM a b := by rw [hmat]
    _ = Gi a b := by rw [hGiMdef, Matrix.of_apply]

/-! ### Part 3 — the second-order chain rule for `pd` under composition (D²φ source term). -/

/-- **SECOND-ORDER CHAIN RULE for the coordinate partial under composition.**  For `C^∞` `f` and `φ`,
        `∂_i∂_j(f ∘ φ)(x) = ∑_{a,b} (∂_b∂_a f)(φ x)·∂_i(φ·b)(x)·∂_j(φ·a)(x)
                            + ∑_a (∂_a f)(φ x)·∂_i∂_j(φ·a)(x)`.
    The first (Hessian-transport) block is the `Jᵀ·Hess_g(f)·J` term; the SECOND block is the D²φ
    source term whose cancellation against the pullback-Christoffel transformation is exactly the
    D²φ-dependent content firewalled for `uniformFlowExp`.  Proof: `pd_comp` pointwise (`hInner`),
    `pd_sum`, `pd_mul` (Leibniz), then `pd_comp` on `∂_a f`.  All regularity from `C^∞` of `f`, `φ`. -/
theorem pd_pd_comp (f : Point n → ℝ) (φ : Point n → Point n) (i j : Fin n) (x : Point n)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (hφ : ContDiff ℝ (⊤ : WithTop ℕ∞) φ) :
    pd (fun y => pd (fun z => f (φ z)) j y) i x
      = (∑ a, (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
              * pd (fun y => φ y a) j x)
        + ∑ a, pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
  classical
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hpdfa : ∀ a, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun w => pd f a w) := fun a => contDiff_pd f hf a
  have hφa : ∀ a, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => φ y a) := by
    intro a
    let P : Point n →L[ℝ] ℝ := ContinuousLinearMap.proj a
    exact (P.contDiff).comp hφ
  -- differentiability along `i` of the two factors of each summand.
  have hA : ∀ a, PdiffAt (fun y => pd f a (φ y)) i x :=
    fun a => PdiffAt_of_contDiff (fun y => pd f a (φ y)) ((hpdfa a).comp hφ) i x
  have hB : ∀ a, PdiffAt (fun y => pd (fun z => φ z a) j y) i x :=
    fun a => PdiffAt_of_contDiff (fun y => pd (fun z => φ z a) j y)
      (contDiff_pd (fun y => φ y a) (hφa a) j) i x
  -- inner functional identity via `pd_comp` pointwise.
  have hInner : (fun y => pd (fun z => f (φ z)) j y)
      = (fun y => ∑ a, pd f a (φ y) * pd (fun z => φ z a) j y) :=
    funext fun y => pd_comp f φ j y (hfd (φ y)) (hφd y)
  -- `∂_i` of `∂_a f ∘ φ` via `pd_comp` on `∂_a f`.
  have hAcomp : ∀ a, pd (fun y => pd f a (φ y)) i x
      = ∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x :=
    fun a => pd_comp (fun w => pd f a w) φ i x ((hpdfa a).differentiable (by simp) (φ x)) (hφd x)
  -- Leibniz per summand.
  have hEach : ∀ a, pd (fun y => pd f a (φ y) * pd (fun z => φ z a) j y) i x
      = (∑ b, pd (fun w => pd f a w) b (φ x) * pd (fun y => φ y b) i x)
          * pd (fun y => φ y a) j x
        + pd f a (φ x) * pd (fun y => pd (fun z => φ z a) j y) i x := by
    intro a
    rw [pd_mul (fun y => pd f a (φ y)) (fun y => pd (fun z => φ z a) j y) i x (hA a) (hB a),
        hAcomp a]
  rw [hInner,
      pd_sum Finset.univ (fun a y => pd f a (φ y) * pd (fun z => φ z a) j y) i x
        (fun a _ => (hA a).mul (hB a)),
      Finset.sum_congr rfl (fun a _ => hEach a), Finset.sum_add_distrib]

end QIQTH.HeatResidualBound
