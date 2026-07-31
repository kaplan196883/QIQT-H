/-
  JacobiOperatorFDeriv — J4-37: the (c)+(d) residual — upgrading the SCALAR directional smooth
  dependence of the doubled geodesic/Jacobi flow (`doubledField_variation_exists_uncond`) to the
  operator-valued second-jet IDENTIFICATION, and assembling the `hid` predicate that
  `expMap_common_nondeg_radius_of_velocity_ode_data` consumes.

  ## Context

  `JacobiOperatorBaseDeriv` (J4-36) delivered the `(h3a)` analytic CORE — the DIRECTIONAL (scalar `s`)
  smooth dependence of the DOUBLED tangent field `G = doubledField g gi` on `E = State × State`:
      `HasDerivAt (fun s => Y s t) (V t) 0`,
  for a doubled family `Y` of integral curves of `G` whose base IC is perturbed linearly `Y s 0 −
  Y 0 0 = s·p`, with `V` the supplied linearized-ODE (doubled-Jacobi) solution.

  `VelocityJacobiBaseDep` (J4-34) provides the two ENDPOINTS of the `(h3)`/`hid` identification:
    * `secondVariation_endpoint_unique` — ODE-uniqueness pinning any solution of the inhomogeneous
      second-variation ODE `Z' = DF(Y)·Z + Src` (matching seed) to a common endpoint;
    * `hid_of_firstJet_hasFDerivAt` — the formal CLM bridge turning
      `HasFDerivAt (fun w => fderiv ℝ Fam w) B v` + `B a b = (Zf a b 1).1` into `hid`.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `doubledField_fderiv_snd_apply` — **the BLOCK formula for `DG`'s second component.**  For the
    doubled field `G (P,W) = (F P, DF(P)·W)` (`F = geodesicField g gi`), the second component of the
    Fréchet derivative applied to a direction `u` decomposes as
        `(DG(e)·u).2 = DF(e.1)·u.2 + D²F(e.1)(u.1)(e.2)`.
    DERIVED via `HasFDerivAt.clm_apply` + `HasFDerivAt.prodMk` from `F ∈ C^∞`.  This is the exact
    coupling that makes the doubled linearized ODE a SECOND-VARIATION ODE.

  * `doubledField_secondFactor_ode` — **the doubled variation field's second factor solves the
    inhomogeneous second-variation ODE.**  Projecting the doubled linearized ODE `V' = DG(Y0)·V`
    onto the second `State` factor, `V₂ = (V ·).2` solves
        `V₂' = DF((Y0)·.1)·V₂ + Src`,   `Src τ = D²F((Y0 τ).1)((V τ).1)((Y0 τ).2)`,
    the EXACT shape `secondVariation_endpoint_unique` consumes.  DERIVED from `hVode` + the block
    formula.

  * `doubledField_secondFactor_endpoint_eq` — **(d), the identification.**  If a phase-space field
    `Zf` solves the SAME second-variation ODE along the SAME base geodesic with the SAME seed, then
    `(V 1).2 = Zf 1` (in particular `((V 1).2).1 = (Zf 1).1`), via `secondVariation_endpoint_unique`.

  * `clm_fderiv_value_of_directional` — **(c2), directional ⟹ CLM value.**  From the Fréchet
    differentiability `HasFDerivAt (fun w => fderiv ℝ Fam w) B v` and a scalar directional identity
    `HasDerivAt (fun s => fderiv ℝ Fam (v + s • a) b) c 0`, DERIVE `B a b = c` by
    `HasDerivAt.unique` on the line `s ↦ v + s • a`.

  * `hid_of_doubled_data` — **the (c)+(d) POINTWISE bridge.**  For a fixed base point (through `Fam`
    and `Zf`) and base velocity `v`, ASSEMBLING all of the above yields the `hid` predicate
        `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`
    from: the jet-map differentiability `hdiff` (genuine regularity — `Fam` is `C⁴`), the doubled
    families `Y a b` / variation fields `Vf a b` with their ODE / IC / confinement data (the genuine
    base-geodesic ODE data feeding `doubledField_variation_exists_uncond`), the FIRST-jet link
    `hlink` (`((Y a b) s 1).2.1 = fderiv ℝ Fam (v+s•a) b`, the `(h1)` identification), and the
    second-variation ODE data for `Zf`.  `hid` is DERIVED here — NOT carried.

  ## HONEST CHECKPOINT (binding) — what is discharged and what remains

  This lands the ENTIRE (c2-block)+(d) analytic bridge as compiled theorems: the block-ODE
  decomposition, the second-variation ODE for the doubled variation field, the endpoint
  identification with `Zf`, the directional⟹CLM-value step, and the pointwise `hid` assembly.

  `(J)` is NOT fully discharged here.  `expMap_common_nondeg_radius_of_velocity_ode_data` needs `hid`
  for EVERY `q ∈ K`, `v ∈ B̄(0,r)`; producing it via `hid_of_doubled_data` requires SUPPLYING, over
  the compact `K` uniformly, (i) the doubled families `Y a b` / variation fields `Vf a b` as genuine
  integral curves through `((q, v+s·a), (0,b))` (with confinement in a compact convex `S`), (ii) the
  first-jet link `hlink` relating those families' Jacobi endpoints to `fderiv ℝ (Fam q)`, and (iii)
  the jet-map differentiability `hdiff`.  Those doubled families are not constructed anywhere in the
  codebase — that construction (geodesic a-priori confinement ⊗ Jacobi existence, plus the `(h1)`
  identification of the doubled Jacobi endpoint with `fderiv (Fam q)`) is the precise remaining
  SUPPLY residual.  So `(J)` is REDUCED from the `(h3a)` CLM-upgrade firewall to that uniform-supply
  residual, with the pointwise CLM-value identification now a compiled theorem.  This file does NOT
  smuggle `hid`/`hbnd`/the `(J)` conclusion, NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3),
  NOT `a₁ = R/6`.
-/
import QIQTH.JacobiOperatorBaseDeriv
import QIQTH.VelocityJacobiBaseDep
import QIQTH.VelocitySecondJetId
import QIQTH.FlowVelocityJacobiField
import QIQTH.UniformFlowBridge
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **Block formula for the second component of `DG`.**  With `G = doubledField g gi` and
    `F = geodesicField g gi`, the second `State`-component of the Fréchet derivative applied to a
    direction `u` is
        `(fderiv G e u).2 = DF(e.1)·u.2 + D²F(e.1)(u.1)(e.2)`.
    DERIVED: `G = (F ∘ fst, (DF ∘ fst)·snd)`; the second factor is `HasFDerivAt.clm_apply` of
    `p ↦ DF(p.1)` (derivative `(D²F(e.1) ∘ fst)`) with `p ↦ p.2` (derivative `snd`), whose value on
    `u` is `DF(e.1)(u.2) + (D²F(e.1)(u.1))(e.2)`. -/
theorem doubledField_fderiv_snd_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (e u : (Point n × Point n) × (Point n × Point n)) :
    ((fderiv ℝ (doubledField g gi) e) u).2
      = fderiv ℝ (geodesicField g gi) e.1 u.2
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1 u.1 e.2 := by
  have hFdiff : Differentiable ℝ (geodesicField g gi) :=
    (contDiff_geodesicField g gi hC).differentiable (by simp)
  have hdFdiff : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_fderiv_geodesicField g gi hC).differentiable (by simp)
  have hF : HasFDerivAt (geodesicField g gi) (fderiv ℝ (geodesicField g gi) e.1) e.1 :=
    (hFdiff e.1).hasFDerivAt
  have hdF : HasFDerivAt (fderiv ℝ (geodesicField g gi))
      (fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1) e.1 :=
    (hdFdiff e.1).hasFDerivAt
  -- first component `p ↦ F p.1`
  have h1 : HasFDerivAt (fun p : (Point n × Point n) × (Point n × Point n) =>
        geodesicField g gi p.1)
      ((fderiv ℝ (geodesicField g gi) e.1).comp (ContinuousLinearMap.fst ℝ _ _)) e :=
    hF.comp e (hasFDerivAt_fst)
  -- CLM-valued factor `c p = DF p.1`, derivative `(D²F e.1) ∘ fst`
  have hc : HasFDerivAt (fun p : (Point n × Point n) × (Point n × Point n) =>
        fderiv ℝ (geodesicField g gi) p.1)
      ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1).comp (ContinuousLinearMap.fst ℝ _ _)) e :=
    hdF.comp e (hasFDerivAt_fst)
  have hu : HasFDerivAt (fun p : (Point n × Point n) × (Point n × Point n) => p.2)
      (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)) e :=
    hasFDerivAt_snd
  have h2 := hc.clm_apply hu
  -- assemble `G` and read off the derivative
  have hprod : HasFDerivAt (doubledField g gi)
      (((fderiv ℝ (geodesicField g gi) e.1).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        (((fderiv ℝ (geodesicField g gi) e.1).comp
            (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)))
          + ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) e.1).comp
              (ContinuousLinearMap.fst ℝ _ _)).flip e.2)) e :=
    h1.prodMk h2
  rw [hprod.fderiv]
  simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

/-- **The doubled variation field's second factor solves the second-variation ODE.**  If `V` solves
    the doubled linearized ODE `V' = DG(Y0)·V` on `[0,1]`, then `V₂ = (V ·).2` solves
        `V₂' = DF((Y0 τ).1)·V₂ + Src τ`,   `Src τ = D²F((Y0 τ).1)((V τ).1)((Y0 τ).2)`,
    the exact inhomogeneous second-variation ODE `secondVariation_endpoint_unique` consumes.
    DERIVED: project `hVode` by the CLM `snd` and rewrite the value by `doubledField_fderiv_snd_apply`. -/
theorem doubledField_secondFactor_ode (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y0 V : ℝ → (Point n × Point n) × (Point n × Point n)}
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (doubledField g gi) (Y0 τ) (V τ)) τ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => (V τ).2)
        (fderiv ℝ (geodesicField g gi) (Y0 τ).1 (V τ).2
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y0 τ).1 (V τ).1 (Y0 τ).2) τ := by
  intro τ hτ
  have hproj :=
    (ContinuousLinearMap.snd ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ (hVode τ hτ)
  have hproj2 : HasDerivAt (fun τ => (V τ).2)
      ((fderiv ℝ (doubledField g gi) (Y0 τ) (V τ)).2) τ := hproj
  have hval : (fderiv ℝ (doubledField g gi) (Y0 τ) (V τ)).2
      = fderiv ℝ (geodesicField g gi) (Y0 τ).1 (V τ).2
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y0 τ).1 (V τ).1 (Y0 τ).2 :=
    doubledField_fderiv_snd_apply g gi hC (Y0 τ) (V τ)
  rw [hval] at hproj2
  exact hproj2

/-- **(d) — the endpoint identification.**  If `Zf` solves the SAME inhomogeneous second-variation
    ODE along the SAME base geodesic `(Y0 ·).1` with the SAME source
    `Src τ = D²F((Y0 τ).1)((V τ).1)((Y0 τ).2)` and the SAME seed `(V 0).2 = Zf 0`, then the doubled
    variation field's second factor and `Zf` agree at the endpoint: `(V 1).2 = Zf 1`.
    DERIVED from `doubledField_secondFactor_ode` + `secondVariation_endpoint_unique`. -/
theorem doubledField_secondFactor_endpoint_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y0 V : ℝ → (Point n × Point n) × (Point n × Point n)}
    {Zf : ℝ → Point n × Point n} {K : ℝ} (hK0 : 0 ≤ K)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (doubledField g gi) (Y0 τ) (V τ)) τ)
    (hZf : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Zf
        (fderiv ℝ (geodesicField g gi) (Y0 τ).1 (Zf τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y0 τ).1 (V τ).1 (Y0 τ).2) τ)
    (h0 : (V 0).2 = Zf 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y0 τ).1‖ ≤ K) :
    (V 1).2 = Zf 1 := by
  have hZ := doubledField_secondFactor_ode g gi hC hVode
  have huniq := secondVariation_endpoint_unique g gi (K := K) hK0
    (Y := fun τ => (Y0 τ).1) (Z := fun τ => (V τ).2) (Z' := Zf)
    (Src := fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y0 τ).1 (V τ).1 (Y0 τ).2)
    hZ hZf h0 hKb
  exact huniq 1 (Set.right_mem_Icc.mpr (by norm_num))

/-- **(c2) — directional derivative ⟹ CLM value.**  From the Fréchet differentiability of the jet
    map `f = fun w => fderiv ℝ Fam w` at `v` (`HasFDerivAt f B v`) and the scalar directional identity
    `HasDerivAt (fun s => f (v + s • a) b) c 0`, DERIVE `B a b = c`.  DERIVED: `HasFDerivAt` gives the
    directional derivative `HasDerivAt (fun s => f (v + s • a)) (B a) 0`; applying the evaluation CLM at
    `b` gives `HasDerivAt (fun s => f (v + s • a) b) (B a b) 0`; `HasDerivAt.unique` closes it. -/
theorem clm_fderiv_value_of_directional {Fam : Point n → Point n}
    {B : Point n →L[ℝ] Point n →L[ℝ] Point n} {v a b : Point n} {c : Point n}
    (hf : HasFDerivAt (fun w => fderiv ℝ Fam w) B v)
    (hdir : HasDerivAt (fun s : ℝ => (fderiv ℝ Fam (v + s • a)) b) c 0) :
    B a b = c := by
  -- the base line `s ↦ v + s • a` has derivative `a` at `0`
  have hline : HasDerivAt (fun s : ℝ => v + s • a) a 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
    exact h1.const_add v
  have hf' : HasFDerivAt (fun w => fderiv ℝ Fam w) B (v + (0 : ℝ) • a) := by
    simpa using hf
  -- chain the Fréchet derivative along the line
  have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ Fam (v + s • a)) (B a) 0 := by
    simpa using hf'.comp_hasDerivAt 0 hline
  -- evaluate at `b` via the evaluation CLM
  have heval :
      HasDerivAt (fun s : ℝ => (fderiv ℝ Fam (v + s • a)) b) (B a b) 0 := by
    simpa using (ContinuousLinearMap.apply ℝ (Point n) b).hasFDerivAt.comp_hasDerivAt 0 hcomp
  exact heval.unique hdir

/-- **The (c)+(d) POINTWISE `hid` bridge.**  Fix a base point (through `Fam : Point n → Point n` and
    the phase-space second-order field `Zf`) and base velocity `v`.  Given
      * `hdiff` — the jet map `w ↦ fderiv ℝ Fam w` is differentiable at `v` (genuine regularity: `Fam`
        is `C⁴`), so `B := fderiv ℝ (fun w => fderiv ℝ Fam w) v` exists;
      * doubled families `Y a b` (integral curves of `G = doubledField g gi` on a compact convex `S`,
        base IC perturbed by `s·((0,a),(0,0))`) and variation fields `Vf a b` solving the doubled
        linearized ODE with seed `((0,a),(0,0))` — the genuine base-geodesic ODE data;
      * `hlink` — the FIRST-jet identification `((Y a b) s 1).2.1 = fderiv ℝ Fam (v + s • a) b`;
      * `hZf` / `h0` / `hKb` — `Zf` solves the second-variation ODE with the matching source and seed;
    the `hid` predicate holds:
        `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1`.
    DERIVED by welding `doubledField_variation_exists_uncond` (directional smooth dependence),
    `clm_fderiv_value_of_directional` (directional ⟹ CLM value), and
    `doubledField_secondFactor_endpoint_eq` (endpoint = `Zf`).  `hid` is DERIVED — NOT carried. -/
theorem hid_of_doubled_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Fam : Point n → Point n}
    {Zf : Point n → Point n → ℝ → Point n × Point n}
    {v : Point n} {K : ℝ} (hK0 : 0 ≤ K)
    {σ : Point n → Point n → ℝ} (hσ : ∀ a b : Point n, 0 < σ a b)
    {S : Point n → Point n → Set ((Point n × Point n) × (Point n × Point n))}
    (hScompact : ∀ a b : Point n, IsCompact (S a b))
    (hSconvex : ∀ a b : Point n, Convex ℝ (S a b))
    (Y : Point n → Point n → ℝ → ℝ → (Point n × Point n) × (Point n × Point n))
    (Vf : Point n → Point n → ℝ → (Point n × Point n) × (Point n × Point n))
    (hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ Fam w) v)
    (hYode : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Y a b s) (doubledField g gi (Y a b s τ)) τ)
    (hVode : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf a b)
        (fderiv ℝ (doubledField g gi) (Y a b 0 τ) (Vf a b τ)) τ)
    (hV0 : ∀ a b : Point n, Vf a b 0
      = (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hIC : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b), Y a b s 0 - Y a b 0 0
      = s • (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hmem : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b),
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, Y a b s τ ∈ S a b)
    (hlink : ∀ a b : Point n, ∀ s ∈ Set.Icc (-(σ a b)) (σ a b),
      (Y a b s 1).2.1 = fderiv ℝ Fam (v + s • a) b)
    (hZf : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Zf a b τ)
        (fderiv ℝ (geodesicField g gi) (Y a b 0 τ).1 (Zf a b τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y a b 0 τ).1 (Vf a b τ).1 (Y a b 0 τ).2) τ)
    (h0 : ∀ a b : Point n, (Vf a b 0).2 = Zf a b 0)
    (hKb : ∀ a b : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y a b 0 τ).1‖ ≤ K) :
    ∀ a b : Point n,
      (fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1 := by
  intro a b
  set B : Point n →L[ℝ] Point n →L[ℝ] Point n := fderiv ℝ (fun w => fderiv ℝ Fam w) v with hBdef
  have hf : HasFDerivAt (fun w => fderiv ℝ Fam w) B v := hdiff.hasFDerivAt
  -- directional smooth dependence of the doubled flow endpoint (J4-36 engine)
  have hdouble := doubledField_variation_exists_uncond g gi hC (hScompact a b) (hSconvex a b)
    (t := 1) (Set.right_mem_Icc.mpr (by norm_num)) (hσ a b)
    (Y := Y a b) (V := Vf a b) (p := (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (S := S a b) (hYode a b) (hVode a b) (hV0 a b) (hIC a b) (hmem a b)
  -- project onto the second-factor position; rewrite via the first-jet link
  have hdir0 : HasDerivAt (fun s : ℝ => (Y a b s 1).2.1) ((Vf a b 1).2.1) 0 := by
    have hcomp :=
      (((ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
        (ContinuousLinearMap.snd ℝ (Point n × Point n)
          (Point n × Point n)))).hasFDerivAt.comp_hasDerivAt 0 hdouble
    simpa using hcomp
  -- `HasDerivAt` at `0` is LOCAL: the first-jet link only needs to hold on the `s`-window
  -- `Icc (-σ) σ ∈ 𝓝 0`, so the two functions agree eventually near `0`.
  have hdir : HasDerivAt (fun s : ℝ => (fderiv ℝ Fam (v + s • a)) b) ((Vf a b 1).2.1) 0 := by
    have hIccnhds : Set.Icc (-(σ a b)) (σ a b) ∈ 𝓝 (0 : ℝ) :=
      Icc_mem_nhds (by linarith [hσ a b]) (hσ a b)
    have heq : (fun s : ℝ => (fderiv ℝ Fam (v + s • a)) b)
        =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => (Y a b s 1).2.1) :=
      Filter.eventuallyEq_of_mem hIccnhds (fun s hs => (hlink a b s hs).symm)
    exact hdir0.congr_of_eventuallyEq heq
  -- (c2): the CLM value equals the doubled second-factor endpoint
  have hval : B a b = (Vf a b 1).2.1 := clm_fderiv_value_of_directional hf hdir
  -- (d): the doubled second-factor endpoint equals the `Zf` position endpoint
  have hZeq : (Vf a b 1).2 = Zf a b 1 :=
    doubledField_secondFactor_endpoint_eq g gi hC hK0 (hVode a b) (hZf a b)
      (h0 a b) (hKb a b)
  rw [hBdef] at hval
  rw [hval, hZeq]

end QIQTH.ExpMap
