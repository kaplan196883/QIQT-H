/-
  ExpMap — groundwork toward the geodesic exponential map's strict derivative.

  THE_EXP_MAP_PLAN.md, first bricks.  The RNC-existence gate is that `exp_p` is a local
  C¹ diffeomorphism at `0`, which needs `HasStrictFDerivAt exp_p id 0` (the inverse function
  theorem needs a STRICT derivative).  GPT-5.5-pro's route reaches this via a two-point Grönwall
  estimate at the equilibrium `e=(p,0)` of the geodesic field `F=geodesicField`, dodging the
  (Mathlib-absent) C¹-dependence-on-initial-condition theorem.  This file lays the flow-independent
  groundwork:

  * **S2 (`hasStrictFDerivAt_geodesicField`)** — the STRICT derivative of `F` at the equilibrium
    `e=(p,0)` is the explicit linear map `A(ξ,η)=(η,0)` (`linF`).  Proof: `F` is `C^∞`
    (`contDiff_geodesicField`), so `ContDiffAt.hasStrictFDerivAt'` upgrades ANY Fréchet derivative to
    a strict one; and the Fréchet derivative at `e` is `A` because the only nonlinear part
    `(x,u)↦Γ(x)(u,u)` is bilinear in `u` and `u=0` at `e`, so every term of its derivative carries a
    factor `u=0`.  Flow-independent, clean.

  * **S1 (`geodesic_rescale`)** — the geodesic rescaling `γ_{p,sv}(t)=γ_{p,v}(st)`, stated as a
    property of ANY integral curve of `F` (no flow function needed): if `γ` solves the geodesic ODE,
    then `t ↦ ((γ(st)).1, s•(γ(st)).2)` solves it too, via the chain rule + bilinearity
    (`γ''(st)·s² = −Γ(γ)(sγ',sγ') = −s²Γ(γ)(γ',γ')`).

  HONEST CAPTION (binding): this is groundwork toward `HasStrictFDerivAt exp_p id 0` → the RNC local
  diffeo.  It does NOT (yet) build `exp_p` as a total function, does NOT run the two-point Grönwall
  (S4), does NOT derive the full RNC gauge (`g(0)=δ`, `∂g(0)=0`, `∂_{(l}Γ_{jk)}(0)=0`), and does NOT
  move numerical-G (species count N, granularity scale Λ_s, the E/ξ term remain).
-/
import Mathlib
import QIQTH.Geodesic

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **The linearization `A = DF(e)` of the geodesic field at the equilibrium `e=(p,0)`.**
    `A (ξ,η) = (η, 0)`: the derivative of `(x,u)↦(u,−Γ(x)(u,u))` at `u=0` (both `Γ`-terms carry a
    factor `u`).  As a continuous linear map on the phase space: `snd.prod 0`. -/
noncomputable def linF : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
  (ContinuousLinearMap.snd ℝ (Point n) (Point n)).prod
    (0 : (Point n × Point n) →L[ℝ] Point n)

@[simp] theorem linF_apply (z : Point n × Point n) : linF z = (z.2, 0) := rfl

/-- A triple product of scalar fields, two of which vanish at the base point, has zero Fréchet
    derivative there: `d(a·b·c) = (da)bc + a(db)c + ab(dc)` and `b=c=0` kills every term. -/
private theorem hasFDerivAt_triple_zero
    {a b c : (Point n × Point n) → ℝ} {x : Point n × Point n}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (hc : DifferentiableAt ℝ c x)
    (hb0 : b x = 0) (hc0 : c x = 0) :
    HasFDerivAt (fun p => a p * b p * c p) (0 : (Point n × Point n) →L[ℝ] ℝ) x := by
  have h := (ha.hasFDerivAt.mul hb.hasFDerivAt).mul hc.hasFDerivAt
  simp only [Pi.mul_apply, hb0, hc0, mul_zero, zero_smul, add_zero] at h
  exact h

/-- **S2 — the strict derivative of the geodesic field at the equilibrium.**
    `HasStrictFDerivAt (geodesicField g gi) A (p,0)` with `A(ξ,η)=(η,0)` (`linF`).

    The geodesic field `F(x,u)=(u,−Γ(x)(u,u))` is `C^∞` (`contDiff_geodesicField`), so
    `ContDiffAt.hasStrictFDerivAt'` upgrades its Fréchet derivative to a STRICT one.  The Fréchet
    derivative at `e=(p,0)` is `A`: the first component `(x,u)↦u` is linear (derivative `η`), and the
    acceleration component `−Γ(x)(u,u)` is bilinear in `u` with `u=0` at `e`, so its derivative
    vanishes there (every term of `d[a·b·c]` carries a factor `u`).

    HONEST: this is the strict derivative of the ODE FIELD at the fixed point — the linear-comparison
    input for the two-point Grönwall.  It is NOT yet `exp_p`, NOT the local diffeo, NOT the RNC gauge. -/
theorem hasStrictFDerivAt_geodesicField
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    HasStrictFDerivAt (geodesicField g gi) linF ((p, 0) : Point n × Point n) := by
  -- Fréchet derivative of each acceleration term `christoffel(q.1)·q.2 j·q.2 k` at `e=(p,0)` is 0.
  have term_deriv : ∀ i j k, HasFDerivAt
      (fun q : Point n × Point n => christoffel g gi i j k q.1 * q.2 j * q.2 k)
      (0 : (Point n × Point n) →L[ℝ] ℝ) ((p, 0) : Point n × Point n) := by
    intro i j k
    refine hasFDerivAt_triple_zero
      (a := fun q => christoffel g gi i j k q.1)
      (b := fun q => q.2 j) (c := fun q => q.2 k) ?_ ?_ ?_ ?_ ?_
    · exact (((hC i j k).differentiable (by simp)).differentiableAt).comp _ differentiableAt_fst
    · fun_prop
    · fun_prop
    · rfl
    · rfl
  -- The acceleration component (a `Point n`-valued map) has zero Fréchet derivative at `e`.
  have h2 : HasFDerivAt
      (fun q : Point n × Point n =>
        (fun i => -∑ j, ∑ k, christoffel g gi i j k q.1 * q.2 j * q.2 k : Point n))
      (0 : (Point n × Point n) →L[ℝ] Point n) ((p, 0) : Point n × Point n) := by
    apply hasFDerivAt_pi''
    intro i
    rw [ContinuousLinearMap.comp_zero]
    have hs : HasFDerivAt
        (fun q : Point n × Point n => ∑ j, ∑ k, christoffel g gi i j k q.1 * q.2 j * q.2 k)
        (0 : (Point n × Point n) →L[ℝ] ℝ) ((p, 0) : Point n × Point n) := by
      have := HasFDerivAt.fun_sum (u := (univ : Finset (Fin n)))
        (fun j _ => HasFDerivAt.fun_sum (u := (univ : Finset (Fin n)))
          (fun k _ => term_deriv i j k))
      simpa using this
    simpa using hs.neg
  -- Assemble the Fréchet derivative `HasFDerivAt F linF e`, then upgrade to strict.
  have hF : HasFDerivAt (geodesicField g gi) linF ((p, 0) : Point n × Point n) :=
    (hasFDerivAt_snd).prodMk h2
  exact (contDiff_geodesicField g gi hC).contDiffAt.hasStrictFDerivAt' hF (by simp)

/-! ### S1 — geodesic rescaling `γ_{p,sv}(t) = γ_{p,v}(s·t)` -/

/-- **The rescaling linear map** `L_s (x,u) = (x, s•u)` on the phase space.  Rescaling a geodesic's
    parameter by `s` scales its velocity by `s`; `L_s` implements that on phase points. -/
noncomputable def rescaleCLM (s : ℝ) : (Point n × Point n) →L[ℝ] (Point n × Point n) :=
  (ContinuousLinearMap.fst ℝ (Point n) (Point n)).prod
    (s • ContinuousLinearMap.snd ℝ (Point n) (Point n))

@[simp] theorem rescaleCLM_apply (s : ℝ) (z : Point n × Point n) :
    rescaleCLM s z = (z.1, s • z.2) := rfl

/-- Quadratic homogeneity of the acceleration term in the velocity:
    `s·(s·(−∑ Γ u u)) = −∑ Γ (s u)(s u)` (bilinearity of `Γ(x)(·,·)` pulls two factors of `s` out). -/
private theorem smul_smul_accel (g gi : Point n → Fin n → Fin n → ℝ)
    (x u : Point n) (s : ℝ) (i : Fin n) :
    s * (s * -∑ j, ∑ k, christoffel g gi i j k x * u j * u k)
      = -∑ j, ∑ k, christoffel g gi i j k x * (s * u j) * (s * u k) := by
  rw [mul_neg, mul_neg, neg_inj, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The rescaling intertwines the field:** `L_s (s • F w) = F (L_s w)`.  This is exactly the ODE
    identity `γ''(st)·s² = −Γ(γ)(sγ',sγ')` witnessing that the rescaled curve solves the same
    geodesic system.  First component: `s•w.2` both sides; second: quadratic homogeneity. -/
theorem rescale_field_eq (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (w : Point n × Point n) :
    rescaleCLM s (s • geodesicField g gi w) = geodesicField g gi (rescaleCLM s w) := by
  refine Prod.ext ?_ ?_
  · simp [geodesicField]
  · funext i
    simp only [rescaleCLM_apply, geodesicField, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul]
    exact smul_smul_accel g gi w.1 w.2 s i

/-- **S1 — geodesic rescaling.**  If `γ` is any integral curve of the geodesic field on `(a,b)`,
    then the reparametrized-and-velocity-scaled curve `τ ↦ L_s(γ(sτ)) = ((γ(sτ)).1, s•(γ(sτ)).2)`
    is again an integral curve.  Since the geodesic with initial data `(p, s•v)` is unique, this
    exhibits `γ_{p,sv}(t) = γ_{p,v}(st)` (velocity rescaled).  Flow-independent: a property of ANY
    solution, proved by the chain rule + `rescale_field_eq`.

    HONEST: this is the ODE rescaling symmetry — the geometric ingredient letting `exp_p` be
    analyzed near `v=0` (small `v` ⇔ short time).  It is NOT `exp_p` itself, NOT the diffeo. -/
theorem geodesic_rescale (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} {γ : ℝ → Point n × Point n}
    (hγ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (geodesicField g gi (γ t)) t)
    (s t : ℝ) (ht : s * t ∈ Set.Ioo a b) :
    HasDerivAt (fun τ => rescaleCLM s (γ (s * τ)))
      (geodesicField g gi (rescaleCLM s (γ (s * t)))) t := by
  have hlin : HasDerivAt (fun τ : ℝ => s * τ) s t := hasDerivAt_const_mul s
  have hscomp : HasDerivAt (fun τ => γ (s * τ)) (s • geodesicField g gi (γ (s * t))) t := by
    have := (hγ (s * t) ht).scomp t hlin
    simpa [Function.comp] using this
  have hcomp := (rescaleCLM s).hasFDerivAt.comp_hasDerivAt t hscomp
  rw [rescale_field_eq g gi s (γ (s * t))] at hcomp
  simpa [Function.comp] using hcomp

/-! ### Flow scaffolding — the geodesic solution as a FUNCTION + `expMap`

  `geodesic_local_existence` is EXISTENTIAL.  `geodesicSol` picks a genuine integral curve through
  `z₀` (at base time `0`) via `Classical.choose`, exposing it as a total function `ℝ → Point n ×
  Point n` with the two spec lemmas below (value at `0`; the ODE on a small interval around `0`).
  This is the minimal scaffolding that lets downstream estimates refer to a well-defined geodesic
  solution near an equilibrium.

  HONEST: the chosen curve is only GUARANTEED to solve the geodesic ODE on some interval `(-ε,ε)`
  (`ε` depends on `z₀`).  `expMap g gi hC p v := (geodesicSol (p,v) 1).1` is therefore DEFINED but its
  geodesic meaning at `t=1` is established only for small `v` (where `1` is reachable — that is the
  content of S1 rescaling + the not-yet-run existence-on-`[0,1]` step).  This scaffolding does NOT
  build the two-point Grönwall (S4) or the local diffeo. -/

/-- A genuine geodesic integral curve through `z₀` (chosen at base time `0`). -/
noncomputable def geodesicSol (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z₀ : Point n × Point n) : ℝ → Point n × Point n :=
  Classical.choose (geodesic_local_existence g gi hC z₀ 0)

/-- `geodesicSol` starts at `z₀`. -/
theorem geodesicSol_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z₀ : Point n × Point n) : geodesicSol g gi hC z₀ 0 = z₀ :=
  (Classical.choose_spec (geodesic_local_existence g gi hC z₀ 0)).1

/-- `geodesicSol` solves the geodesic ODE on a small interval `(-ε, ε)` around `0`. -/
theorem geodesicSol_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z₀ : Point n × Point n) :
    ∃ ε > (0 : ℝ), ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (geodesicSol g gi hC z₀)
        (geodesicField g gi (geodesicSol g gi hC z₀ t)) t := by
  obtain ⟨ε, hε, hd⟩ := (Classical.choose_spec (geodesic_local_existence g gi hC z₀ 0)).2
  exact ⟨ε, hε, fun t ht => hd t (by simpa using ht)⟩

/-- **Existence of the geodesic on `[0,1]` for a rescaled (small) velocity.**  The chosen solution
    `geodesicSol (p,v)` is guaranteed to solve the ODE only on some `(-ε, ε)` with `ε` depending on
    `v`.  Rescaling the parameter by `s = ε/2` (velocity by `s`, via `geodesic_rescale`) produces a
    genuine integral curve `γ` with `γ 0 = (p, (ε/2)•v)` that solves the geodesic ODE on the OPEN
    interval `(-1, 2) ⊇ [0,1]`.  Hence for every direction `v` there is a positive scale `s` such
    that the geodesic with initial velocity `s•v` reaches parameter `1`.

    This discharges the *existence-on-`[0,1]`* half of the flagged common-tube management, flow-free,
    by composing the scaffolding spec (`geodesicSol_hasDerivAt`) with the S1 rescaling symmetry
    (`geodesic_rescale`).  HONEST: this is existence on `[0,1]` for velocities of the form `s•v`
    (short geodesics) — it is NOT the uniform-over-a-ball tube, NOT the two-point estimate, NOT the
    diffeo.  The Lipschitz-flow half (S3) and the strict-remainder nbhd (S2) still have to be
    reconciled on the SAME sub-ball for the unconditional two-point Grönwall. -/
theorem geodesicSol_rescale_unit_existence (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) :
    ∃ s > (0 : ℝ), ∃ γ : ℝ → Point n × Point n,
      γ 0 = (p, s • v) ∧
      ∀ t ∈ Set.Ioo (-1 : ℝ) 2, HasDerivAt γ (geodesicField g gi (γ t)) t := by
  obtain ⟨ε, hε, hd⟩ := geodesicSol_hasDerivAt g gi hC (p, v)
  refine ⟨ε / 2, by positivity,
    fun τ => rescaleCLM (ε / 2) (geodesicSol g gi hC (p, v) ((ε / 2) * τ)), ?_, ?_⟩
  · -- value at `0`: `L_{ε/2} (geodesicSol (p,v) 0) = L_{ε/2} (p,v) = (p, (ε/2)•v)`.
    simp [geodesicSol_zero g gi hC (p, v), rescaleCLM_apply]
  · intro t ht
    -- the rescaled curve is an integral curve wherever `(ε/2)·t ∈ (-ε, ε)`.
    have hmem : (ε / 2) * t ∈ Set.Ioo (-ε) ε := by
      constructor
      · nlinarith [ht.1, hε]
      · nlinarith [ht.2, hε]
    exact geodesic_rescale g gi (a := -ε) (b := ε) hd (ε / 2) t hmem

/-! ### S3 — Lipschitz dependence of the geodesic flow on the initial condition

  The geodesic field `F = geodesicField g gi` is `C^∞`, hence `C^1`, so it satisfies the
  Picard–Lindelöf hypotheses near the equilibrium `e = (p,0)` (`IsPicardLindelof.of_contDiffAt_one`).
  Mathlib's flow theorem
  `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith` then produces a
  local flow `α : phase → ℝ → phase` on a closed ball `closedBall e r`, with integral-curve property
  `α x 0 = x`, `α x' = F(α x)`, that is **Lipschitz in the initial point** `x` (uniformly in time on
  the flow interval `[-ε, ε]`).  This is exactly the "Lipschitz flow dependence `‖Y_v(t) − Y_w(t)‖ ≤
  L‖v − w‖`" ingredient of the two-point Grönwall estimate.

  HONEST: this is the flow's Lipschitz-in-IC on the Picard–Lindelöf interval `[-ε, ε]` around the
  equilibrium.  Reaching the *unit* interval `[0,1]` for all small `v, w` (needed to evaluate `exp_p`
  at `t = 1`) is the flagged "common-tube management" bookkeeping that combines this with the geodesic
  rescaling `geodesic_rescale`; it is NOT discharged here. -/
theorem geodesicField_flow_lipschitz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ (r : NNReal), 0 < r ∧
      ∃ α : (Point n × Point n) → ℝ → (Point n × Point n),
        (∀ x ∈ Metric.closedBall ((p, 0) : Point n × Point n) (r : ℝ),
          α x 0 = x ∧ ∀ t ∈ Set.Icc (-ε) ε,
            HasDerivWithinAt (α x) (geodesicField g gi (α x t)) (Set.Icc (-ε) ε) t) ∧
        ∃ L' : NNReal, ∀ t ∈ Set.Icc (-ε) ε,
          LipschitzOnWith L' (fun x => α x t)
            (Metric.closedBall ((p, 0) : Point n × Point n) (r : ℝ)) := by
  have hCA : ContDiffAt ℝ 1 (geodesicField g gi) ((p, 0) : Point n × Point n) :=
    ((contDiff_geodesicField g gi hC).of_le le_top).contDiffAt
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hCA
  obtain ⟨α, hflow, L', hlip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hset : Set.Icc (0 - ε) (0 + ε) = Set.Icc (-ε) ε := by rw [zero_sub, zero_add]
  refine ⟨ε, hε, r, hr, α, ?_, L', ?_⟩
  · intro x hx
    obtain ⟨hx0, hxd⟩ := hflow x hx
    rw [hset] at hxd
    exact ⟨hx0, hxd⟩
  · intro t ht
    rw [hset] at hlip
    exact hlip t ht

/-! ### S4 — the two-point residual ODE and the Grönwall estimate

  Fix the equilibrium linearization `A = linF` (`A(ξ,η) = (η,0)`, `A² = 0`).  For two integral curves
  `Y₁, Y₂` of `F = geodesicField` and a fixed direction `d`, the explicit linear comparison is
  `ℓ_d(τ) = (1 + τA)·i(d) = (τ•d, d)` (`i(d) = (0,d)`), and the residual is
  `r(τ) := Y₁ τ − Y₂ τ − ℓ_d(τ)`.  The key ODE algebra (`residual_hasDerivAt`) is
  `r' = A·r + R` with `R := F(Y₁) − F(Y₂) − A·(Y₁ − Y₂)`, obtained from `Y₁' = F(Y₁)`, `Y₂' = F(Y₂)`,
  `ℓ_d' = A·i(d) = (d,0)`, and `A·ℓ_d = (d,0)`.  Feeding this into the inhomogeneous Grönwall
  inequality `norm_le_gronwallBound_of_norm_deriv_right_le` (with `‖R‖ ≤ C` on `[0,1]`) yields the
  two-point estimate `‖r(1)‖ ≤ gronwallBound 0 ‖A‖ C 1` (`residual_gronwall`). -/

/-- **S4 (ODE algebra) — the residual solves `r' = A·r + R`.**  With `A = linF`,
    `r(τ) = Y₁ τ − Y₂ τ − (τ•d, d)`, and `R(t) = F(Y₁ t) − F(Y₂ t) − A(Y₁ t − Y₂ t)`, any two
    integral curves `Y₁, Y₂` of the geodesic field give `HasDerivAt r (A·r(t) + R(t)) t`.

    Derivation: `Y₁' = F(Y₁)`, `Y₂' = F(Y₂)`, and `d/dτ (τ•d, d) = (d, 0)`, so
    `r'(t) = F(Y₁ t) − F(Y₂ t) − (d, 0)`; the identity `F(Y₁) − F(Y₂) − (d,0) = A·r + R` follows from
    linearity of `A` and `A·(τ•d, d) = (d, 0)`.  Flow-independent: a pointwise property of any two
    solutions.  This is the exact ODE the two-point Grönwall estimate integrates. -/
theorem residual_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (d : Point n) {Y₁ Y₂ : ℝ → Point n × Point n} {t : ℝ}
    (h1 : HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t) :
    HasDerivAt (fun τ => Y₁ τ - Y₂ τ - ((τ • d, d) : Point n × Point n))
      (linF (Y₁ t - Y₂ t - ((t • d, d) : Point n × Point n))
        + (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - linF (Y₁ t - Y₂ t))) t := by
  have hℓ : HasDerivAt (fun τ : ℝ => ((τ • d, d) : Point n × Point n))
      ((d, 0) : Point n × Point n) t := by
    have h1' : HasDerivAt (fun τ : ℝ => τ • d) d t := by
      simpa using (hasDerivAt_id t).smul_const d
    exact h1'.prodMk (hasDerivAt_const t d)
  have hbase : HasDerivAt (fun τ => Y₁ τ - Y₂ τ - ((τ • d, d) : Point n × Point n))
      (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - ((d, 0) : Point n × Point n)) t :=
    (h1.sub h2).sub hℓ
  have hval : (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - ((d, 0) : Point n × Point n))
      = linF (Y₁ t - Y₂ t - ((t • d, d) : Point n × Point n))
        + (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - linF (Y₁ t - Y₂ t)) := by
    have hl : linF (Y₁ t - Y₂ t - ((t • d, d) : Point n × Point n))
        = linF (Y₁ t - Y₂ t) - ((d, 0) : Point n × Point n) := by
      rw [map_sub]
      congr 1
    rw [hl]; abel
  rw [hval] at hbase
  exact hbase

/-- **S4 (the crux) — the two-point Grönwall estimate.**  If `Y₁, Y₂` are integral curves of the
    geodesic field on `[0,1]` with `Y₁ 0 − Y₂ 0 = (0, d)` (so the residual `r` vanishes at `0`) and
    the strict remainder is uniformly bounded, `‖F(Y₁ t) − F(Y₂ t) − A(Y₁ t − Y₂ t)‖ ≤ C` on `[0,1]`,
    then the residual at time `1` obeys the inhomogeneous Grönwall bound
    `‖Y₁ 1 − Y₂ 1 − (1•d, d)‖ ≤ gronwallBound 0 ‖A‖ C 1`, with `A = linF`.

    This is the two-point `o(‖v−w‖)` seed for the strict derivative of `exp_p`: taking `Y₁ = Y_v`,
    `Y₂ = Y_w`, `d = v − w`, and `C = εL‖v−w‖` (strict remainder × Lipschitz flow dependence, S3),
    the bound is `‖r(1)‖ ≤ (εL/‖A‖)(e^{‖A‖} − 1)‖v−w‖ = O(ε)‖v−w‖`.

    HONEST: this is the Grönwall estimate CONDITIONAL on its tube hypotheses — the integral-curve
    property on `[0,1]` and the uniform remainder bound `C`.  Supplying those for all small `v, w`
    from `geodesicField_flow_lipschitz` + `hasStrictFDerivAt_geodesicField` + `geodesic_rescale` is
    the flagged common-tube management, NOT discharged here. -/
theorem residual_gronwall (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ : ℝ → Point n × Point n} (d : Point n) (C : ℝ)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (h0 : Y₁ 0 - Y₂ 0 = ((0, d) : Point n × Point n))
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - linF (Y₁ t - Y₂ t)‖ ≤ C) :
    ‖Y₁ 1 - Y₂ 1 - ((1 • d, d) : Point n × Point n)‖
      ≤ gronwallBound 0 ‖(linF (n := n))‖ C 1 := by
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Y₁ τ - Y₂ τ - ((τ • d, d) : Point n × Point n))
        (linF (Y₁ t - Y₂ t - ((t • d, d) : Point n × Point n))
          + (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - linF (Y₁ t - Y₂ t))) t :=
    fun t ht => residual_hasDerivAt g gi d (h1 t ht) (h2 t ht)
  have hcont : ContinuousOn
      (fun τ => Y₁ τ - Y₂ τ - ((τ • d, d) : Point n × Point n)) (Set.Icc 0 1) :=
    fun t ht => ((key t ht).continuousAt).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun τ => Y₁ τ - Y₂ τ - ((τ • d, d) : Point n × Point n))
    (f' := fun t => linF (Y₁ t - Y₂ t - ((t • d, d) : Point n × Point n))
      + (geodesicField g gi (Y₁ t) - geodesicField g gi (Y₂ t) - linF (Y₁ t - Y₂ t)))
    (δ := 0) (K := ‖(linF (n := n))‖) (ε := C) (a := 0) (b := 1)
    hcont
    (fun x hx => (key x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by
      show ‖Y₁ 0 - Y₂ 0 - ((0 • d, d) : Point n × Point n)‖ ≤ 0
      rw [h0]; simp)
    (by
      intro x hx
      show ‖linF (Y₁ x - Y₂ x - ((x • d, d) : Point n × Point n))
          + (geodesicField g gi (Y₁ x) - geodesicField g gi (Y₂ x) - linF (Y₁ x - Y₂ x))‖
        ≤ ‖(linF (n := n))‖ * ‖Y₁ x - Y₂ x - ((x • d, d) : Point n × Point n)‖ + C
      refine (norm_add_le _ _).trans ?_
      exact add_le_add (linF.le_opNorm (Y₁ x - Y₂ x - ((x • d, d) : Point n × Point n)))
        (hR x (Set.Ico_subset_Icc_self hx)))
  have := hmain 1 (by norm_num [Set.mem_Icc])
  simpa using this

/-! ### S4′ — the a-priori Grönwall confinement and the direct two-point Lipschitz bound

  The equilibrium `e = (p,0)` is a zero of the geodesic field (`geodesicField_equilibrium`).  Near
  `e`, on any set `S` where `F = geodesicField` is `K`-Lipschitz, two exact integral curves obey the
  standard two-point Grönwall bound `dist (Y₁ t) (Y₂ t) ≤ dist (Y₁ 0) (Y₂ 0) · e^{K t}`
  (`geodesic_twopoint_gronwall`, via Mathlib's `dist_le_of_trajectories_ODE_of_mem`).  Specialising
  `Y₂` to the constant equilibrium curve gives the a-priori confinement
  `dist (Y t) e ≤ dist (Y 0) e · e^{K t}` (`geodesic_apriori_bound`): a solution starting `δ`-close to
  `e` stays `δ e^{K}`-close on `[0,1]` while it remains in `S`.  These are the two Grönwall estimates
  the two-point residual bound consumes, now in their clean unconditional-given-`S` form. -/

/-- **The equilibrium.** `e = (p,0)` is a zero of the geodesic field: the velocity component of `e`
    is `0`, so both the velocity output and every quadratic acceleration term vanish. -/
theorem geodesicField_equilibrium (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) :
    geodesicField g gi ((p, 0) : Point n × Point n) = 0 := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    simp [geodesicField]

/-- **The direct two-point Grönwall bound on `[0,1]`.**  If `Y₁, Y₂` are integral curves of the
    geodesic field on `[0,1]` that both stay in a set `S` on which `F = geodesicField` is
    `K`-Lipschitz, then `dist (Y₁ t) (Y₂ t) ≤ dist (Y₁ 0) (Y₂ 0) · e^{K t}` on `[0,1]`.  This is
    Mathlib's `dist_le_of_trajectories_ODE_of_mem` for the autonomous geodesic field.

    HONEST: this is the Lipschitz-in-initial-condition bound on the *unit* interval, valid on the
    set `S` where the field is Lipschitz — the tube hypothesis `Y₁, Y₂ ∈ S` on `[0,1]` is supplied,
    not derived here.  It is the two-point flow-Lipschitz ingredient the residual estimate needs,
    reached directly by Grönwall rather than by re-timing the Picard–Lindelöf flow. -/
theorem geodesic_twopoint_gronwall (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ : ℝ → Point n × Point n} {S : Set (Point n × Point n)} {K : NNReal}
    (hLip : LipschitzOnWith K (geodesicField g gi) S)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (Y₁ t) (Y₂ t) ≤ dist (Y₁ 0) (Y₂ 0) * Real.exp (K * t) := by
  intro t ht
  have hmain := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => geodesicField g gi) (s := fun _ => S) (K := K)
    (f := Y₁) (g := Y₂) (a := 0) (b := 1) (δ := dist (Y₁ 0) (Y₂ 0))
    (fun t _ => hLip)
    (fun t ht => (h1 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h1 t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hS1 t (Set.Ico_subset_Icc_self ht))
    (fun t ht => (h2 t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h2 t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hS2 t (Set.Ico_subset_Icc_self ht))
    le_rfl t ht
  simpa using hmain

/-- **The a-priori Grönwall confinement.**  A geodesic integral curve `Y` on `[0,1]` that stays in a
    set `S` containing the equilibrium `e = (p,0)` and on which `F` is `K`-Lipschitz stays
    `dist (Y 0) e · e^{K t}`-close to `e`: `dist (Y t) e ≤ dist (Y 0) e · e^{K t}`.  Proved by feeding
    the constant equilibrium curve (an integral curve, since `F(e)=0`) into
    `geodesic_twopoint_gronwall`.

    This is the a-priori boundedness: a solution launched `δ`-close to `e` cannot leave the ball of
    radius `δ e^{K}` around `e` on `[0,1]` while it remains in `S` — the ingredient that (given
    containment) confines the tube uniformly as `v → 0`.

    HONEST: conditional on the curve remaining in the Lipschitz set `S` on `[0,1]`.  Making this
    containment unconditional for a whole ball of initial velocities is the remaining common-tube
    step (see `geodesic_unit_tube_existence` for the existence half). -/
theorem geodesic_apriori_bound (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n)
    {Y : ℝ → Point n × Point n} {S : Set (Point n × Point n)} {K : NNReal}
    (hLip : LipschitzOnWith K (geodesicField g gi) S)
    (he : ((p, 0) : Point n × Point n) ∈ S)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y (geodesicField g gi (Y t)) t)
    (hYS : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y t ∈ S) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (Y t) ((p, 0) : Point n × Point n)
        ≤ dist (Y 0) ((p, 0) : Point n × Point n) * Real.exp (K * t) := by
  have hconst : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun _ : ℝ => ((p, 0) : Point n × Point n))
        (geodesicField g gi ((fun _ : ℝ => ((p, 0) : Point n × Point n)) t)) t := by
    intro t _
    rw [show geodesicField g gi ((fun _ : ℝ => ((p, 0) : Point n × Point n)) t) = 0 from
      geodesicField_equilibrium g gi p]
    exact hasDerivAt_const t _
  exact geodesic_twopoint_gronwall g gi hLip hY hconst hYS (fun _ _ => he)

/-! ### S4′ — uniform existence of the geodesic tube on `[0,1]` for a whole ball of velocities

  This closes the flagged existence half of the common-tube management, **uniformly over a ball**,
  flow-free (no Picard–Lindelöf re-timing bookkeeping).  The key is that the `C¹` local-existence
  lemma `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` produces ONE
  radius `r` and ONE time `ε` valid for *every* initial phase point in `closedBall e r` — the
  existence interval `(-ε, ε)` does not shrink as the point varies.  Combined with the geodesic
  rescaling `geodesic_rescale` (`s = ε/2`), a velocity `v` with `‖v‖ ≤ (ε/2)·r` is realised as the
  rescaling of the (uniformly-existing) short geodesic through `(p, (ε/2)⁻¹•v)`, giving a genuine
  integral curve through `(p, v)` on the OPEN interval `(-2, 2) ⊇ [0,1]`.  The radius
  `ρ = (ε/2)·r > 0` is uniform over the ball. -/

/-- **Uniform geodesic existence on `[0,1]` over a ball of velocities.**  There is a radius `ρ > 0`
    such that for every velocity `v` with `‖v‖ ≤ ρ` there is a genuine integral curve `Y` of the
    geodesic field with `Y 0 = (p, v)` solving the geodesic ODE on `(-2, 2) ⊇ [0,1]`.

    Proof: the geodesic field is `C¹`, so
    `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` gives a UNIFORM
    radius `r` and UNIFORM existence time `ε` at the equilibrium `e = (p,0)`.  For `‖v‖ ≤ (ε/2)·r`
    the point `(p, (ε/2)⁻¹•v)` lies in `closedBall e r`, so has a geodesic on `(-ε, ε)`; rescaling
    the parameter by `s = ε/2` (`geodesic_rescale`) stretches its interval to `(-2, 2)` and its
    initial velocity to `(ε/2)•((ε/2)⁻¹•v) = v`.

    This discharges the existence half of the common-tube management **uniformly over a whole ball**,
    resolving the interval mismatch that the Picard–Lindelöf interval `[-ε, ε]` created.  HONEST:
    this is uniform existence of the `[0,1]` integral curve; it does NOT by itself confine the tube
    inside a fixed Lipschitz/strict-remainder neighbourhood (that is the a-priori confinement, whose
    unconditional-over-a-ball form is the remaining step), and it is NOT yet `exp_p`'s strict
    derivative or the local diffeo. -/
theorem geodesic_unit_tube_existence (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ ρ > (0 : ℝ), ∀ v : Point n, ‖v‖ ≤ ρ →
      ∃ Y : ℝ → Point n × Point n, Y 0 = (p, v) ∧
        ∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t := by
  have hCA : ContDiffAt ℝ 1 (geodesicField g gi) ((p, 0) : Point n × Point n) :=
    ((contDiff_geodesicField g gi hC).of_le le_top).contDiffAt
  obtain ⟨r, hr, ε, hε, hex⟩ :=
    hCA.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  set s : ℝ := ε / 2 with hs
  have hs0 : 0 < s := by positivity
  refine ⟨s * r, mul_pos hs0 hr, fun v hv => ?_⟩
  -- The rescaled initial point `(p, s⁻¹•v)` lies in the uniform existence ball.
  have hmemball : (p, s⁻¹ • v) ∈ Metric.closedBall ((p, 0) : Point n × Point n) r := by
    rw [Metric.mem_closedBall, dist_eq_norm,
      show (p, s⁻¹ • v) - ((p, 0) : Point n × Point n) = ((0, s⁻¹ • v) : Point n × Point n) by
        simp]
    have hnorm : ‖((0, s⁻¹ • v) : Point n × Point n)‖ = s⁻¹ * ‖v‖ := by
      rw [Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0,
        max_eq_right (by positivity)]
    rw [hnorm]
    calc s⁻¹ * ‖v‖ ≤ s⁻¹ * (s * r) :=
          mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hs0))
      _ = r := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs0), one_mul]
  obtain ⟨α, hα0, hαd⟩ := hex (p, s⁻¹ • v) hmemball
  refine ⟨fun τ => rescaleCLM s (α (s * τ)), ?_, ?_⟩
  · -- Y 0 = L_s (α 0) = L_s (p, s⁻¹•v) = (p, s • s⁻¹ • v) = (p, v).
    show rescaleCLM s (α (s * 0)) = (p, v)
    rw [mul_zero, hα0, rescaleCLM_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt hs0), one_smul]
  · intro t ht
    have hmem : s * t ∈ Set.Ioo (0 - ε) (0 + ε) := by
      rw [zero_sub, zero_add]
      refine ⟨?_, ?_⟩
      · calc -ε = s * (-2) := by rw [hs]; ring
          _ < s * t := mul_lt_mul_of_pos_left ht.1 hs0
      · calc s * t < s * 2 := mul_lt_mul_of_pos_left ht.2 hs0
          _ = ε := by rw [hs]; ring
    exact geodesic_rescale g gi (a := 0 - ε) (b := 0 + ε) hαd s t hmem

/-! ### S4′ — the a-priori confinement: the tube stays `O(‖v‖)`-close to `e`, uniformly over a ball

  This makes the a-priori bound UNCONDITIONAL over a whole ball of velocities — the containment half
  of the common-tube management.  Two ingredients from the Picard–Lindelöf flow
  `geodesicField_flow_lipschitz` (which is `L'`-Lipschitz in the initial condition):
  * the equilibrium trajectory `α e` is CONSTANT (`α e t = e`): both `α e` and the constant curve
    `e` solve the geodesic ODE with the same initial value `e`, stay in a closed ball on which `F` is
    Lipschitz (the flow's compact range, `ContDiffOn.exists_lipschitzOnWith`), so agree by ODE
    uniqueness (`ODE_solution_unique_of_mem_Icc`);
  * hence `‖α (p,w) t − e‖ = ‖α (p,w) t − α e t‖ ≤ L'‖w‖` by Lipschitz-in-IC.
  Rescaling (`geodesic_rescale`, `s = ε/2`, `w = s⁻¹•v`) then confines the unit-interval geodesic
  through `(p,v)`: `‖Y_v t − e‖ ≤ (‖L_s‖·L'·s⁻¹)·‖v‖` on `[0,1]`, with the constant uniform over the
  ball `‖v‖ ≤ (ε/2)·r`.  This is the a-priori boundedness needed to pin the tube inside any fixed
  neighbourhood of `e` as `v → 0`. -/

/-- **The a-priori confinement of the geodesic tube.**  There is a radius `ρ > 0` and a constant
    `C₀ ≥ 0` such that for every velocity `v` with `‖v‖ ≤ ρ` the geodesic tube `Y` through `(p, v)`
    exists on `(-2, 2) ⊇ [0,1]` and stays `C₀‖v‖`-close to the equilibrium `e = (p,0)` on `[0,1]`:
    `‖Y t − (p,0)‖ ≤ C₀‖v‖`.  In particular `Y t → e` uniformly in `t ∈ [0,1]` as `v → 0`.

    Proof: the Picard–Lindelöf flow `α` (Lipschitz-in-IC with constant `L'` on `closedBall e r`,
    from `geodesicField_flow_lipschitz`) has a constant equilibrium trajectory `α e = e` (ODE
    uniqueness against the constant curve, on a closed ball containing `α e`'s compact range where
    `F` is Lipschitz).  Hence `‖α (p,w) t − e‖ ≤ L'‖w‖`; rescaling by `s = ε/2` with `w = s⁻¹•v`
    gives the `[0,1]` tube through `(p,v)` and `‖Y t − e‖ ≤ ‖rescaleCLM s‖·L'·s⁻¹·‖v‖`.

    This discharges the containment half of the common-tube management **unconditionally over a
    ball**.  HONEST: combined with `geodesic_unit_tube_existence` (existence) it gives the full tube;
    what remains for `HasStrictFDerivAt exp_p id 0` is to feed this + the S2 strict remainder + the
    two-point Grönwall into the `isLittleO` characterisation, and to pin `expMap`'s value to the tube
    endpoint (the definitional bridge). It is NOT yet `exp_p`'s strict derivative or the diffeo. -/
theorem geodesic_apriori_confinement (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ v : Point n, ‖v‖ ≤ ρ →
      ∃ Y : ℝ → Point n × Point n, Y 0 = (p, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((p, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ := by
  obtain ⟨ε, hε, r, hr, α, hflow, L', hlip⟩ := geodesicField_flow_lipschitz g gi hC p
  set e : Point n × Point n := (p, 0) with he_def
  have hmem_e : e ∈ Metric.closedBall e (r : ℝ) := Metric.mem_closedBall_self (le_of_lt hr)
  have hα0e : α e 0 = e := (hflow e hmem_e).1
  have hαe_deriv : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (α e) (geodesicField g gi (α e t)) (Set.Icc (-ε) ε) t :=
    (hflow e hmem_e).2
  have hcont : ContinuousOn (α e) (Set.Icc (-ε) ε) := HasDerivWithinAt.continuousOn hαe_deriv
  -- The flow's equilibrium trajectory has compact range, hence lies in a closed ball.
  obtain ⟨R, hR⟩ :=
    (((isCompact_Icc).image_of_continuousOn hcont).isBounded).subset_closedBall e
  have h0mem : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, le_of_lt hε⟩
  have h0memoo : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hR0 : (0 : ℝ) ≤ R := by
    have : e ∈ Metric.closedBall e R := hR ⟨0, h0mem, hα0e⟩
    simpa using this
  -- `F` is Lipschitz on `closedBall e R` (convex, compact).
  obtain ⟨K₀, hK₀⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := Metric.closedBall e R)).exists_lipschitzOnWith
      (by simp) (convex_closedBall e R) (isCompact_closedBall e R)
  -- Uniqueness: `α e` coincides with the constant equilibrium curve on `[-ε, ε]`.
  have hEq : Set.EqOn (α e) (fun _ => e) (Set.Icc (-ε) ε) := by
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicField g gi)
      (s := fun _ => Metric.closedBall e R) (K := K₀) (t₀ := 0)
      (fun t _ => hK₀) h0memoo hcont
      (fun t ht => (hαe_deriv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hR ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩)
      continuousOn_const
      (fun t _ => ?_) (fun _ _ => Metric.mem_closedBall_self hR0) hα0e
    show HasDerivAt (fun _ : ℝ => e) (geodesicField g gi e) t
    have hz : geodesicField g gi e = 0 := by rw [he_def]; exact geodesicField_equilibrium g gi p
    rw [hz]
    exact hasDerivAt_const t e
  -- Assemble the confined tube.
  set s : ℝ := ε / 2 with hs
  have hs0 : 0 < s := by positivity
  refine ⟨s * r, mul_pos hs0 hr, (1 + s) * L' * s⁻¹, by positivity, fun v hv => ?_⟩
  have hmemball : (p, s⁻¹ • v) ∈ Metric.closedBall e (r : ℝ) := by
    rw [he_def, Metric.mem_closedBall, dist_eq_norm,
      show (p, s⁻¹ • v) - ((p, 0) : Point n × Point n) = ((0, s⁻¹ • v) : Point n × Point n) by simp]
    have hnorm : ‖((0, s⁻¹ • v) : Point n × Point n)‖ = s⁻¹ * ‖v‖ := by
      rw [Prod.norm_def, norm_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0,
        max_eq_right (by positivity)]
    rw [hnorm]
    calc s⁻¹ * ‖v‖ ≤ s⁻¹ * (s * r) :=
          mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hs0))
      _ = r := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs0), one_mul]
  have hw_deriv : ∀ t ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (α (p, s⁻¹ • v)) (geodesicField g gi (α (p, s⁻¹ • v) t)) (Set.Icc (-ε) ε) t :=
    (hflow (p, s⁻¹ • v) hmemball).2
  have hw0 : α (p, s⁻¹ • v) 0 = (p, s⁻¹ • v) := (hflow (p, s⁻¹ • v) hmemball).1
  refine ⟨fun τ => rescaleCLM s (α (p, s⁻¹ • v) (s * τ)), ?_, ?_, ?_⟩
  · show rescaleCLM s (α (p, s⁻¹ • v) (s * 0)) = (p, v)
    rw [mul_zero, hw0, rescaleCLM_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt hs0), one_smul]
  · intro t ht
    have hmem : s * t ∈ Set.Ioo (0 - ε) (0 + ε) := by
      rw [zero_sub, zero_add]
      refine ⟨?_, ?_⟩
      · calc -ε = s * (-2) := by rw [hs]; ring
          _ < s * t := mul_lt_mul_of_pos_left ht.1 hs0
      · calc s * t < s * 2 := mul_lt_mul_of_pos_left ht.2 hs0
          _ = ε := by rw [hs]; ring
    refine geodesic_rescale g gi (a := 0 - ε) (b := 0 + ε) ?_ s t hmem
    intro u hu
    rw [zero_sub, zero_add] at hu
    exact (hw_deriv u (Set.Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  · intro t ht
    -- s*t ∈ [0, ε/2] ⊆ [-ε, ε]
    have hst : s * t ∈ Set.Icc (-ε) ε := by
      constructor
      · have : (0 : ℝ) ≤ s * t := mul_nonneg (le_of_lt hs0) ht.1
        linarith
      · calc s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hs0)
          _ = s := mul_one s
          _ ≤ ε := by rw [hs]; linarith
    show ‖rescaleCLM s (α (p, s⁻¹ • v) (s * t)) - e‖ ≤ (1 + s) * L' * s⁻¹ * ‖v‖
    -- Y t - e = L_s (α(p,w)(st) - α e (st)), using α e = e and linearity of L_s.
    set D : Point n × Point n := α (p, s⁻¹ • v) (s * t) - α e (s * t) with hD
    have hYt : rescaleCLM s (α (p, s⁻¹ • v) (s * t)) - e = rescaleCLM s D := by
      rw [hD, map_sub, hEq hst]
      congr 1
      rw [he_def]
      simp [rescaleCLM_apply]
    -- ‖α(p,w)(st) - α e (st)‖ ≤ L'·‖w‖  (flow Lipschitz-in-IC)
    have hdist : ‖D‖ ≤ L' * ‖s⁻¹ • v‖ := by
      have hl := (hlip (s * t) hst).dist_le_mul (p, s⁻¹ • v) hmemball e hmem_e
      rw [dist_eq_norm, dist_eq_norm] at hl
      rw [hD]
      refine hl.trans (le_of_eq ?_)
      rw [he_def,
        show (p, s⁻¹ • v) - ((p, 0) : Point n × Point n) = ((0, s⁻¹ • v) : Point n × Point n) by simp,
        Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    -- ‖L_s D‖ = max ‖D.1‖ (s‖D.2‖) ≤ (1+s)‖D‖  (direct, avoids the product-codomain opNorm diamond)
    have hcomp1 : ‖D.1‖ ≤ ‖D‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hcomp2 : ‖D.2‖ ≤ ‖D‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hrs : ‖rescaleCLM s D‖ ≤ (1 + s) * ‖D‖ := by
      rw [rescaleCLM_apply, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      refine max_le ?_ ?_
      · exact hcomp1.trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith))
      · calc s * ‖D.2‖ ≤ s * ‖D‖ := mul_le_mul_of_nonneg_left hcomp2 (le_of_lt hs0)
          _ ≤ (1 + s) * ‖D‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    rw [hYt]
    calc ‖rescaleCLM s D‖
        ≤ (1 + s) * ‖D‖ := hrs
      _ ≤ (1 + s) * (L' * ‖s⁻¹ • v‖) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = (1 + s) * L' * s⁻¹ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0]; ring

/-! ### The genuine geodesic exponential map, its strict derivative (S5), and local diffeo (S6)

  The scaffolding `geodesicSol` pins the geodesic only on some `(-δ_v, δ_v)`, so its value at `t = 1`
  need not be the geodesic endpoint.  Here the analyzed exponential map is DEFINED from the confined
  `[0,1]` tube of `geodesic_apriori_confinement`, whose endpoint IS the genuine geodesic position at
  parameter `1` for small `v`.  `exists_confined_tube_family` skolemizes the per-velocity tube into a
  single tube-valued function `expTube`; `expMap p v := (expTube p v 1).1`.

  With existence + confinement (both unconditional over a ball) in hand, **S5**
  (`hasStrictFDerivAt_expMap`) assembles `HasStrictFDerivAt expMap id 0` from: the S2 strict remainder
  of the field at the equilibrium (`hasStrictFDerivAt_geodesicField`), the two-point flow-Lipschitz
  bound (`geodesic_twopoint_gronwall`), and the inhomogeneous residual Grönwall (`residual_gronwall`),
  through the two-point `isLittleO` characterisation.  **S6** (`expMap_localInverse`) feeds this strict
  derivative (with `id` invertible) into Mathlib's inverse function theorem
  `HasStrictFDerivAt.toOpenPartialHomeomorph`, exhibiting `expMap` as a local homeomorphism at `0`
  with a continuous local inverse whose strict derivative is `id` — the normal-coordinate chart.

  HONEST CAPTION (binding): reaching `expMap` a local C¹ diffeo means normal coordinates EXIST as a
  chart.  It does NOT derive the RNC gauge in those coordinates (`g(0)=δ`, `∂g(0)=0`,
  `∂_{(l}Γ_{jk)}(0)=0` still need the metric-in-normal-coordinates change of variables), does NOT build
  a curved heat kernel, and does NOT move numerical-G (species count `N`, granularity scale `Λ_s`, the
  `E/ξ` term remain). -/

/-- Linearity of the inhomogeneous Grönwall bound in its `ε` argument (at `δ = 0`, `x = 1`):
    `gronwallBound 0 K ε 1 = ε · gronwallBound 0 K 1 1`.  A direct case split on `K = 0`. -/
theorem gronwallBound_zero_linear (K ε : ℝ) :
    gronwallBound 0 K ε 1 = ε * gronwallBound 0 K 1 1 := by
  simp only [gronwallBound]
  split_ifs with hK <;> ring

/-- **Skolemized confined tube family.**  Repackages the per-velocity existential of
    `geodesic_apriori_confinement` as a single tube-valued function `Y : Point n → ℝ → Point n ×
    Point n`, specified uniformly for `‖v‖ ≤ ρ` (a junk tube outside the ball). -/
theorem exists_confined_tube_family (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ Y : Point n → ℝ → Point n × Point n,
      ∀ v : Point n, ‖v‖ ≤ ρ →
        Y v 0 = (p, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt (Y v) (geodesicField g gi (Y v t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y v t - ((p, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖) := by
  obtain ⟨ρ, hρ, C₀, hC₀, hfam⟩ := geodesic_apriori_confinement g gi hC p
  have hchoose : ∀ v : Point n, ∃ Y : ℝ → Point n × Point n,
      ‖v‖ ≤ ρ →
        Y 0 = (p, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((p, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖) := by
    intro v
    by_cases hv : ‖v‖ ≤ ρ
    · obtain ⟨Y, hY⟩ := hfam v hv
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose Y hY using hchoose
  exact ⟨ρ, hρ, C₀, hC₀, Y, fun v hv => hY v hv⟩

/-- The confinement radius chosen for the exponential map at `p`. -/
noncomputable def expRho (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : ℝ :=
  (exists_confined_tube_family g gi hC p).choose

/-- The confinement constant chosen for the exponential map at `p`. -/
noncomputable def expConst (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : ℝ :=
  (exists_confined_tube_family g gi hC p).choose_spec.2.choose

/-- The chosen confined geodesic tube through `(p, v)` (a genuine `[0,1]` integral curve of the
    geodesic field for `‖v‖ ≤ expRho`). -/
noncomputable def expTube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : Point n → ℝ → Point n × Point n :=
  (exists_confined_tube_family g gi hC p).choose_spec.2.choose_spec.2.choose

/-- **The geodesic exponential map** `exp_p(v)` = position at parameter `1` of the confined geodesic
    tube through `(p, v)`.  For `‖v‖ ≤ expRho` this is the genuine geodesic endpoint. -/
noncomputable def expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) : Point n :=
  (expTube g gi hC p v 1).1

theorem expRho_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : 0 < expRho g gi hC p :=
  (exists_confined_tube_family g gi hC p).choose_spec.1

theorem expConst_nonneg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) : 0 ≤ expConst g gi hC p :=
  (exists_confined_tube_family g gi hC p).choose_spec.2.choose_spec.1

/-- **Specification of the confined tube.**  For `‖v‖ ≤ expRho`, `expTube p v` starts at `(p, v)`,
    solves the geodesic ODE on `(-2, 2) ⊇ [0,1]`, and stays `expConst · ‖v‖`-close to `(p,0)` on
    `[0,1]`.  Repackages `exists_confined_tube_family`'s chosen witness. -/
theorem expTube_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    expTube g gi hC p v 0 = (p, v) ∧
    (∀ t ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (expTube g gi hC p v) (geodesicField g gi (expTube g gi hC p v t)) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖ ≤ expConst g gi hC p * ‖v‖) :=
  (exists_confined_tube_family g gi hC p).choose_spec.2.choose_spec.2.choose_spec v hv

-- The three `Classical.choose`-based selectors are opaque from here on: their definitional bodies
-- unfold to the (enormous) Picard–Lindelöf/confinement witness, which would blow up `whnf` during
-- unification.  All downstream reasoning goes through the spec lemmas above, never the bodies.
attribute [irreducible] expRho expConst expTube

set_option maxHeartbeats 1000000 in
/-- **S5 — the strict derivative of the exponential map at the origin.**
    `HasStrictFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0`: the two-point
    little-o `‖exp_p v − exp_p w − (v − w)‖ = o(‖v − w‖)` as `(v, w) → (0, 0)`.

    Assembly: for `c > 0`, choose `η` so the residual Grönwall constant is `≤ c`; the a-priori
    confinement (`expTube_spec`) puts the tubes `Y_v(t), Y_w(t)` in the S2 `η`-neighbourhood of the
    equilibrium `e = (p,0)` for `(v,w)` near `0`, whence the S2 strict remainder
    (`hasStrictFDerivAt_geodesicField`) bounds `‖F(Y_v) − F(Y_w) − A(Y_v − Y_w)‖ ≤ η‖Y_v − Y_w‖`, the
    two-point flow-Lipschitz bound (`geodesic_twopoint_gronwall`) gives `‖Y_v − Y_w‖ ≤ e^{K}‖v − w‖`,
    and `residual_gronwall` propagates this to `‖r(1)‖ ≤ c‖v − w‖`; projecting onto the position
    component (`π₁ r(1) = exp_p v − exp_p w − (v − w)`) closes the little-o.

    HONEST: this is `exp_p`'s strict derivative at `0` (the input to the inverse function theorem). It
    is NOT the RNC gauge, NOT a curved heat kernel, NOT numerical-G. -/
theorem hasStrictFDerivAt_expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    HasStrictFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) (0 : Point n) := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- Lipschitz constant of the field on the unit closed ball around the equilibrium.
  obtain ⟨Ktube, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn
        (s := Metric.closedBall ((p, 0) : Point n × Point n) 1)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hC₀ := expConst_nonneg g gi hC p
  have hρpos := expRho_pos g gi hC p
  -- the Grönwall proportionality constant `β = gronwallBound 0 ‖A‖ 1 1 ≥ 0`.
  set β : ℝ := gronwallBound 0 ‖(linF (n := n))‖ 1 1 with hβdef
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    rcases eq_or_ne (‖(linF (n := n))‖) 0 with hK | hK
    · rw [hK, gronwallBound_K0]; norm_num
    · rw [gronwallBound_of_K_ne_0 hK]
      have hKpos : 0 < ‖(linF (n := n))‖ := (norm_nonneg _).lt_of_ne (Ne.symm hK)
      have hexp : (1 : ℝ) ≤ Real.exp (‖(linF (n := n))‖ * 1) := by
        rw [mul_one]; exact Real.one_le_exp hKpos.le
      have hprod : 0 ≤ 1 / ‖(linF (n := n))‖ * (Real.exp (‖(linF (n := n))‖ * 1) - 1) :=
        mul_nonneg (by positivity) (by linarith)
      simpa using hprod
  -- `M = e^{K}·β ≥ 0` and the tolerance `η = c/(M+1) > 0` with `η·M ≤ c`.
  set M : ℝ := Real.exp (Ktube : ℝ) * β with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (Real.exp_pos _).le hβ0
  have hM1 : 0 < M + 1 := by linarith
  set η : ℝ := c / (M + 1) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact div_pos hc hM1
  have hηM : η * M ≤ c := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ hM1]; nlinarith [hc, hM0]
  -- S2 strict remainder of the field, unpacked as a two-point estimate on an `η`-neighbourhood of the
  -- equilibrium.  Reducing the little-o's pair projections HERE (via `simp`) keeps the downstream
  -- application on the bare tube points `Yv t`, `Yw t` free of pair projections (whose `isDefEq`
  -- against `geodesicField`/`christoffel` would otherwise blow up `whnf`).
  have hstrict := (hasStrictFDerivAt_geodesicField g gi hC p).isLittleO
  rw [Asymptotics.isLittleO_iff] at hstrict
  have hev := hstrict hηpos
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨rη, hrη, hball⟩ := hev
  have hstrictbound : ∀ y z : Point n × Point n,
      dist y ((p, 0) : Point n × Point n) < rη → dist z ((p, 0) : Point n × Point n) < rη →
        ‖geodesicField g gi y - geodesicField g gi z - linF (y - z)‖ ≤ η * ‖y - z‖ := by
    intro y z hy hz
    have hpair : dist ((y, z) : (Point n × Point n) × (Point n × Point n))
        (((p, 0), (p, 0)) : (Point n × Point n) × (Point n × Point n)) < rη := by
      rw [Prod.dist_eq]; exact max_lt hy hz
    have hb := hball hpair
    simpa using hb
  -- the neighbourhood radius `δ`.
  have hC1 : 0 < expConst g gi hC p + 1 := by linarith
  have hden : 0 < 2 * (expConst g gi hC p + 1) := by positivity
  set δ : ℝ := min (expRho g gi hC p)
      (min (rη / (2 * (expConst g gi hC p + 1))) (1 / (expConst g gi hC p + 1))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min hρpos (lt_min (by positivity) (by positivity))
  have hδρ : δ ≤ expRho g gi hC p := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ rη / (2 * (expConst g gi hC p + 1)) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ 1 / (expConst g gi hC p + 1) := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hkey2 : δ * (2 * (expConst g gi hC p + 1)) ≤ rη := (le_div_iff₀ hden).mp hδ2
  have hkey3 : δ * (expConst g gi hC p + 1) ≤ 1 := (le_div_iff₀ hC1).mp hδ3
  have hCδ : expConst g gi hC p * δ < rη := by
    nlinarith [hkey2, hδpos, mul_nonneg hC₀ hδpos.le]
  have hCδ1 : expConst g gi hC p * δ ≤ 1 := by nlinarith [hkey3, hδpos]
  -- the eventual neighbourhood of `(0,0)`.
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδpos, ?_⟩
  intro q hq
  rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero, sub_zero] at hq
  obtain ⟨hv, hw⟩ := max_lt_iff.mp hq
  have hvρ : ‖q.1‖ ≤ expRho g gi hC p := (lt_of_lt_of_le hv hδρ).le
  have hwρ : ‖q.2‖ ≤ expRho g gi hC p := (lt_of_lt_of_le hw hδρ).le
  obtain ⟨hY0v, hYderivv, hYconfv⟩ := expTube_spec g gi hC p q.1 hvρ
  obtain ⟨hY0w, hYderivw, hYconfw⟩ := expTube_spec g gi hC p q.2 hwρ
  -- Fix the two tubes as opaque local functions (their `Classical.choose` bodies never unfold).
  set Yv : ℝ → Point n × Point n := expTube g gi hC p q.1 with hYvdef
  set Yw : ℝ → Point n × Point n := expTube g gi hC p q.2 with hYwdef
  clear_value Yv Yw
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- membership of the tubes in the unit ball on `[0,1]`.
  have hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Yv t ∈ Metric.closedBall ((p, 0) : Point n × Point n) 1 := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖Yv t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖q.1‖ := hYconfv t ht
      _ ≤ expConst g gi hC p * δ := mul_le_mul_of_nonneg_left hv.le hC₀
      _ ≤ 1 := hCδ1
  have hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Yw t ∈ Metric.closedBall ((p, 0) : Point n × Point n) 1 := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖Yw t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖q.2‖ := hYconfw t ht
      _ ≤ expConst g gi hC p * δ := mul_le_mul_of_nonneg_left hw.le hC₀
      _ ≤ 1 := hCδ1
  -- two-point Lipschitz bound on the tube separation.
  have hdist0 : dist (Yv 0) (Yw 0) = ‖q.1 - q.2‖ := by
    rw [hY0v, hY0w, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) 1) (K := Ktube) hLip
      (fun t ht => hYderivv t (hIcc_Ioo t ht)) (fun t ht => hYderivw t (hIcc_Ioo t ht)) hS1 hS2
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Yv t - Yw t‖ ≤ ‖q.1 - q.2‖ * Real.exp (Ktube : ℝ) := by
    intro t ht
    have h := htwopoint t ht
    rw [hdist0, dist_eq_norm] at h
    have hexple : Real.exp ((Ktube : ℝ) * t) ≤ Real.exp ((Ktube : ℝ)) := by
      apply Real.exp_le_exp.mpr
      calc (Ktube : ℝ) * t ≤ (Ktube : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        _ = (Ktube : ℝ) := mul_one _
    calc ‖Yv t - Yw t‖
        ≤ ‖q.1 - q.2‖ * Real.exp ((Ktube : ℝ) * t) := h
      _ ≤ ‖q.1 - q.2‖ * Real.exp ((Ktube : ℝ)) :=
          mul_le_mul_of_nonneg_left hexple (norm_nonneg _)
  -- the strict remainder bound, uniform over `[0,1]`.
  have hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Yv t) - geodesicField g gi (Yw t) - linF (Yv t - Yw t)‖
        ≤ η * (‖q.1 - q.2‖ * Real.exp (Ktube : ℝ)) := by
    intro t ht
    have hdv : ‖Yv t - ((p, 0) : Point n × Point n)‖ ≤ expConst g gi hC p * δ :=
      le_trans (hYconfv t ht) (mul_le_mul_of_nonneg_left hv.le hC₀)
    have hdw : ‖Yw t - ((p, 0) : Point n × Point n)‖ ≤ expConst g gi hC p * δ :=
      le_trans (hYconfw t ht) (mul_le_mul_of_nonneg_left hw.le hC₀)
    have hyd : dist (Yv t) ((p, 0) : Point n × Point n) < rη := by
      rw [dist_eq_norm]; exact lt_of_le_of_lt hdv hCδ
    have hzd : dist (Yw t) ((p, 0) : Point n × Point n) < rη := by
      rw [dist_eq_norm]; exact lt_of_le_of_lt hdw hCδ
    exact (hstrictbound (Yv t) (Yw t) hyd hzd).trans
      (mul_le_mul_of_nonneg_left (hYvw t ht) hηpos.le)
  -- the residual Grönwall bound.
  have h0 : Yv 0 - Yw 0 = ((0, q.1 - q.2) : Point n × Point n) := by
    rw [hY0v, hY0w, Prod.mk_sub_mk, sub_self]
  have hgron := residual_gronwall g gi (q.1 - q.2) (η * (‖q.1 - q.2‖ * Real.exp (Ktube : ℝ)))
    (fun t ht => hYderivv t (hIcc_Ioo t ht)) (fun t ht => hYderivw t (hIcc_Ioo t ht)) h0 hR
  -- project onto the position component and finish.
  have hev : expMap g gi hC p q.1 = (Yv 1).1 := by simp only [expMap, hYvdef]
  have hew : expMap g gi hC p q.2 = (Yw 1).1 := by simp only [expMap, hYwdef]
  have heq : expMap g gi hC p q.1 - expMap g gi hC p q.2
      - (ContinuousLinearMap.id ℝ (Point n)) (q.1 - q.2)
      = (Yv 1 - Yw 1 - ((1 • (q.1 - q.2), q.1 - q.2) : Point n × Point n)).1 := by
    rw [hev, hew]; simp [Prod.fst_sub]
  rw [heq]
  calc ‖(Yv 1 - Yw 1 - ((1 • (q.1 - q.2), q.1 - q.2) : Point n × Point n)).1‖
      ≤ ‖Yv 1 - Yw 1 - ((1 • (q.1 - q.2), q.1 - q.2) : Point n × Point n)‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ gronwallBound 0 ‖(linF (n := n))‖ (η * (‖q.1 - q.2‖ * Real.exp (Ktube : ℝ))) 1 := hgron
    _ ≤ c * ‖q.1 - q.2‖ := by
        rw [gronwallBound_zero_linear, ← hβdef]
        have key : η * (‖q.1 - q.2‖ * Real.exp (Ktube : ℝ)) * β = η * M * ‖q.1 - q.2‖ := by
          rw [hMdef]; ring
        rw [key]
        exact mul_le_mul_of_nonneg_right hηM (norm_nonneg _)

/-- **S6 — the exponential map is a local homeomorphism at `0` (the RNC local-diffeo gate).**
    From `hasStrictFDerivAt_expMap` (`HasStrictFDerivAt expMap id 0`, and `id` is invertible) the
    inverse function theorem `HasStrictFDerivAt.toOpenPartialHomeomorph` produces an
    `OpenPartialHomeomorph φ` with `⇑φ = expMap`, `0 ∈ φ.source`, and a continuous local inverse
    `φ.symm` whose strict derivative at `expMap 0` is again `id`.  `φ.symm` is the normal-coordinate
    chart: normal coordinates EXIST as a chart around `p`.

    HONEST: this is the local diffeo / normal-coordinate-chart existence.  It does NOT derive the RNC
    gauge (`g(0)=δ`, `∂g(0)=0`, `∂_{(l}Γ_{jk)}(0)=0` — those need the metric-in-normal-coordinates
    change of variables), NOT a curved heat kernel, NOT numerical-G. -/
theorem expMap_localInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ φ : OpenPartialHomeomorph (Point n) (Point n),
      (⇑φ = expMap g gi hC p) ∧ (0 : Point n) ∈ φ.source ∧
      HasStrictFDerivAt (φ.symm) (ContinuousLinearMap.id ℝ (Point n))
        (expMap g gi hC p 0) := by
  have hderiv := hasStrictFDerivAt_expMap g gi hC p
  rw [← ContinuousLinearEquiv.coe_refl (R₁ := ℝ) (M₁ := Point n)] at hderiv
  refine ⟨hderiv.toOpenPartialHomeomorph (expMap g gi hC p),
    hderiv.toOpenPartialHomeomorph_coe, hderiv.mem_toOpenPartialHomeomorph_source, ?_⟩
  have hli := hderiv.to_localInverse
  rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
    hderiv.localInverse_def] at hli
  exact hli

/-! ### The exponential map's radial 2-jet is `−Γ(p)`

  This is the second-order radial behaviour of `exp_p` along a fixed direction `v`: the curve
  `t ↦ exp_p(t•v)` has first `t`-derivative `v` at `0` and second `t`-derivative `−Γ(p)(v,v)` at `0`.
  Concretely, `exp_p(t•v)` traces (a reparametrisation of) the geodesic through `p` with velocity `v`,
  so its 2-jet reads off the geodesic field at the equilibrium: velocity then acceleration.

  Route (flow-free): fix a scale `s>0` with `‖s•v‖ ≤ expRho` and let `Y := expTube p (s•v)` be the
  confined `[0,1]` integral curve through `(p, s•v)` (`expTube_spec`).  Geodesic homogeneity
  (`geodesic_rescale`) plus local uniqueness (`geodesic_local_unique`) identify
  `exp_p(t•v) = (Y (t/s)).1` on a neighbourhood of `t=0`; then the first component `(Y τ).1` has
  `t`-derivative `(Y τ).2` (velocity) and the second component `(Y τ).2` has `t`-derivative the
  acceleration `−∑Γ(Y.1)(Y.2,Y.2)`, evaluated at `τ=0` where `Y 0 = (p, s•v)`.  The two factors of
  `1/s` from the chain rule cancel the two factors of `s` in `s•v`, leaving exactly `−Γ(p)(v,v)`.

  HONEST CAPTION (binding): this is the exp map's RADIAL 2-jet only — the second-order radial
  behaviour of `exp_p(tv)` encodes `−Γ(p)(v,v)`.  It is the radial DIAGONAL, NOT the RNC gauge (which
  needs the off-radial Jacobian field / higher jets — the Mathlib-absent smooth-dependence-on-IC
  theorem).  It does NOT discharge `hgauge`, does NOT build normal-coordinate metric jets, and does
  NOT move numerical-G (species count `N`, granularity scale `Λ_s`, the `E/ξ` term remain). -/
set_option maxHeartbeats 1600000 in
theorem expMap_radial_accel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) :
    HasDerivAt (fun t : ℝ => expMap g gi hC p (t • v)) v 0
      ∧ HasDerivAt (deriv (fun t : ℝ => expMap g gi hC p (t • v)))
          (-(fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k) : Point n) 0 := by
  -- A scale `s>0` making `s•v` a legal (confined) tube direction.
  set s : ℝ := min 1 (expRho g gi hC p / (‖v‖ + 1)) with hs_def
  have hs0 : 0 < s :=
    lt_min one_pos (div_pos (expRho_pos g gi hC p) (by positivity))
  have hsne : s ≠ 0 := hs0.ne'
  have hsv : ‖s • v‖ ≤ expRho g gi hC p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    have hs2 : s ≤ expRho g gi hC p / (‖v‖ + 1) := min_le_right _ _
    calc s * ‖v‖ ≤ (expRho g gi hC p / (‖v‖ + 1)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
      _ ≤ expRho g gi hC p := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg v, (expRho_pos g gi hC p).le]
  -- The confined tube `Y` through `(p, s•v)`.
  obtain ⟨hY0, hYd, -⟩ := expTube_spec g gi hC p (s • v) hsv
  set Y : ℝ → Point n × Point n := expTube g gi hC p (s • v) with hYdef
  -- Projections of the ODE onto position/velocity components.
  have hpos : ∀ τ ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt (fun u => (Y u).1) ((Y τ).2) τ := by
    intro τ hτ
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ
      (hYd τ hτ)
    simpa [geodesicField] using this
  have hvel : ∀ τ ∈ Set.Ioo (-2 : ℝ) 2,
      HasDerivAt (fun u => (Y u).2) ((geodesicField g gi (Y τ)).2) τ := by
    intro τ hτ
    have := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ
      (hYd τ hτ)
    simpa using this
  -- The radial position curve and its first derivative (chain rule with `τ = t/s`).
  have hpos_comp : ∀ t : ℝ, t / s ∈ Set.Ioo (-2 : ℝ) 2 →
      HasDerivAt (fun u => (Y (u / s)).1) ((1 / s) • (Y (t / s)).2) t := by
    intro t hmem
    have hlin : HasDerivAt (fun u : ℝ => u / s) (1 / s) t := by
      simpa using (hasDerivAt_id t).div_const s
    simpa [Function.comp] using (hpos (t / s) hmem).scomp t hlin
  -- The acceleration at the base point, and its rescaled value `= −Γ(p)(v,v)`.
  have haccel0 : (geodesicField g gi (Y 0)).2
      = (fun i => -∑ j, ∑ k, christoffel g gi i j k p * (s * v j) * (s * v k)) := by
    rw [hY0]; rfl
  have hval : ((1 / s) • ((1 / s) • (geodesicField g gi (Y (0 / s))).2) : Point n)
      = (-(fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k) : Point n) := by
    rw [zero_div, haccel0]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    rw [show (∑ j, ∑ k, christoffel g gi i j k p * (s * v j) * (s * v k))
          = (s * s) * ∑ j, ∑ k, christoffel g gi i j k p * v j * v k from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring]
    field_simp
  -- Second radial derivative of the velocity component at `0`.
  have hH_deriv0 : HasDerivAt (fun u => (1 / s) • (Y (u / s)).2)
      (-(fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k) : Point n) 0 := by
    have hlin0 : HasDerivAt (fun u : ℝ => u / s) (1 / s) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const s
    have h0mem : (0 : ℝ) / s ∈ Set.Ioo (-2 : ℝ) 2 := by
      rw [zero_div]; exact ⟨by norm_num, by norm_num⟩
    have hg0 : HasDerivAt (fun u => (Y (u / s)).2)
        ((1 / s) • (geodesicField g gi (Y (0 / s))).2) 0 := by
      simpa only [Function.comp] using (hvel (0 / s) h0mem).scomp (0 : ℝ) hlin0
    have hg1 := hg0.const_smul (1 / s)
    rw [hval] at hg1
    exact hg1
  -- The identification `exp_p(t•v) = (Y (t/s)).1` on a neighbourhood of `0` (geodesic uniqueness).
  have hEqA : (fun t : ℝ => expMap g gi hC p (t • v)) =ᶠ[𝓝 (0 : ℝ)] (fun t => (Y (t / s)).1) := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨s, hs0, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero] at ht
    have ha1 : |t / s| < 1 := by rw [abs_div, abs_of_pos hs0, div_lt_one hs0]; exact ht
    have heqarg : t • v = (t / s) • (s • v) := by
      rw [smul_smul, div_mul_cancel₀ t hsne]
    have haw : ‖(t / s) • (s • v)‖ ≤ expRho g gi hC p := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |t / s| * ‖s • v‖ ≤ 1 * ‖s • v‖ := mul_le_mul_of_nonneg_right ha1.le (norm_nonneg _)
        _ = ‖s • v‖ := one_mul _
        _ ≤ expRho g gi hC p := hsv
    obtain ⟨hZ0, hZd, -⟩ := expTube_spec g gi hC p ((t / s) • (s • v)) haw
    have hRd : ∀ τ : ℝ, (t / s) * τ ∈ Set.Ioo (-2 : ℝ) 2 →
        HasDerivAt (fun τ' => rescaleCLM (t / s) (Y ((t / s) * τ')))
          (geodesicField g gi (rescaleCLM (t / s) (Y ((t / s) * τ)))) τ :=
      fun τ hτ => geodesic_rescale g gi hYd (t / s) τ hτ
    have hIoosub : Set.Ioo (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hIccsub : Set.Icc (-1 : ℝ) (3 / 2) ⊆ Set.Ioo (-2 : ℝ) 2 :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hRmem_arg : ∀ τ ∈ Set.Icc (-1 : ℝ) (3 / 2), (t / s) * τ ∈ Set.Ioo (-2 : ℝ) 2 := by
      intro τ hτ
      have hτabs : |τ| ≤ 3 / 2 := by rw [abs_le]; exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hlt : |(t / s) * τ| < 2 := by
        rw [abs_mul]
        calc |t / s| * |τ| ≤ 1 * (3 / 2) :=
              mul_le_mul ha1.le hτabs (abs_nonneg _) (by norm_num)
          _ = 3 / 2 := by norm_num
          _ < 2 := by norm_num
      exact Set.mem_Ioo.mpr (abs_lt.mp hlt)
    -- bound the two curves' images on the compact interval `[-1, 3/2]`
    have hZcont : ContinuousOn (expTube g gi hC p ((t / s) • (s • v)))
        (Set.Icc (-1 : ℝ) (3 / 2)) :=
      fun τ hτ => ((hZd τ (hIccsub hτ)).continuousAt).continuousWithinAt
    obtain ⟨Mz, hMz⟩ :=
      (((isCompact_Icc).image_of_continuousOn hZcont).isBounded).subset_closedBall
        ((p, 0) : Point n × Point n)
    have hRcont : ContinuousOn (fun τ' => rescaleCLM (t / s) (Y ((t / s) * τ')))
        (Set.Icc (-1 : ℝ) (3 / 2)) :=
      fun τ hτ => ((hRd τ (hRmem_arg τ hτ)).continuousAt).continuousWithinAt
    obtain ⟨Mr, hMr⟩ :=
      (((isCompact_Icc).image_of_continuousOn hRcont).isBounded).subset_closedBall
        ((p, 0) : Point n × Point n)
    obtain ⟨Klip, hLip⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
        (s := Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr))).exists_lipschitzOnWith
        (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
    have hZmem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
        expTube g gi hC p ((t / s) • (s • v)) τ
          ∈ Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr) := fun τ hτ =>
      Metric.closedBall_subset_closedBall (le_max_left _ _)
        (hMz ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
    have hRmem : ∀ τ ∈ Set.Ioo (-1 : ℝ) (3 / 2),
        (fun τ' => rescaleCLM (t / s) (Y ((t / s) * τ'))) τ
          ∈ Metric.closedBall ((p, 0) : Point n × Point n) (max Mz Mr) := fun τ hτ =>
      Metric.closedBall_subset_closedBall (le_max_right _ _)
        (hMr ⟨τ, Set.Ioo_subset_Icc_self hτ, rfl⟩)
    have hEqon := geodesic_local_unique g gi (a := -1) (b := 3 / 2) (t₀ := 0)
      ⟨by norm_num, by norm_num⟩ hLip
      (fun τ hτ => ⟨hZd τ (hIoosub hτ), hZmem τ hτ⟩)
      (fun τ hτ => ⟨hRd τ (hRmem_arg τ (Set.Ioo_subset_Icc_self hτ)), hRmem τ hτ⟩)
      (by rw [hZ0]; simp [mul_zero, hY0, rescaleCLM_apply])
    have hZR := hEqon (show (1 : ℝ) ∈ Set.Ioo (-1 : ℝ) (3 / 2) from ⟨by norm_num, by norm_num⟩)
    show expMap g gi hC p (t • v) = (Y (t / s)).1
    rw [heqarg]
    simp only [expMap]
    rw [hZR]
    simp [rescaleCLM_apply, mul_one]
  -- Part 1: the first radial derivative is `v`.
  have hpart1 : HasDerivAt (fun t : ℝ => expMap g gi hC p (t • v)) v 0 := by
    have h0mem : (0 : ℝ) / s ∈ Set.Ioo (-2 : ℝ) 2 := by
      rw [zero_div]; exact ⟨by norm_num, by norm_num⟩
    have hd := hpos_comp 0 h0mem
    rw [show ((1 / s) • (Y (0 / s)).2 : Point n) = v by
      rw [zero_div, hY0]
      show (1 / s) • (s • v) = v
      rw [smul_smul, one_div, inv_mul_cancel₀ hsne, one_smul]] at hd
    exact hd.congr_of_eventuallyEq hEqA
  -- Part 2: the second radial derivative is `−Γ(p)(v,v)`.
  refine ⟨hpart1, ?_⟩
  have hderivh_eq : deriv (fun u => (Y (u / s)).1)
      =ᶠ[𝓝 (0 : ℝ)] (fun u => (1 / s) • (Y (u / s)).2) := by
    have hloc : ∀ᶠ t in 𝓝 (0 : ℝ),
        HasDerivAt (fun u => (Y (u / s)).1) ((1 / s) • (Y (t / s)).2) t := by
      apply Metric.eventually_nhds_iff.mpr
      refine ⟨2 * s, by positivity, fun t ht => ?_⟩
      apply hpos_comp t
      rw [Real.dist_eq, sub_zero] at ht
      have hlt : |t / s| < 2 := by rw [abs_div, abs_of_pos hs0, div_lt_iff₀ hs0]; exact ht
      exact Set.mem_Ioo.mpr (abs_lt.mp hlt)
    exact hloc.mono (fun t ht => ht.deriv)
  have hderiv_eq : deriv (fun t : ℝ => expMap g gi hC p (t • v))
      =ᶠ[𝓝 (0 : ℝ)] (fun u => (1 / s) • (Y (u / s)).2) :=
    (hEqA.deriv).trans hderivh_eq
  exact hH_deriv0.congr_of_eventuallyEq hderiv_eq

/-! ### EXP-JET1 — the value 2-jet `exp_p(v) = p + v − ½Γ_p(v,v) + o(‖v‖²)`

  The Fréchet value 2-jet of `exp_p` at `0`, in diagonal form.  Concretely the geodesic tube `Y = expTube p v`
  is compared to the explicit model curve `M(t) = (p + t·v − ½t²·Γ_p(v,v), v − t·Γ_p(v,v))`, whose position
  component at `t=1` is `p + v − ½Γ_p(v,v)`.  The residual `q = Y − M` solves `q' = A·q + Err` (`A = linF`) with
  `Err(t) = (0, Γ_p(v,v) − Γ_{(Y t).1}((Y t).2,(Y t).2))`, and the a-priori confinement + local Christoffel bounds
  give `‖Err(t)‖ ≤ Acoef‖v‖³ + Bcoef‖v‖‖q t‖` on `[0,1]`.  The inhomogeneous Grönwall bound then yields
  `‖q 1‖ ≤ C‖v‖³`, and projecting the position component gives `exp_p(v) − p − v + ½Γ_p(v,v) = O(‖v‖³) = o(‖v‖²)`.

  HONEST CAPTION (binding): this is the Fréchet value 2-jet of `exp_p` at `0`.  It is a step toward discharging the
  RNC gauge; it does NOT yet discharge `hgauge`, NOT build the pullback metric, NOT move numerical-G (`N`, `Λ_s`,
  `E/ξ` remain). -/

/-- **Sup-norm bound for the Christoffel quadratic form.**  If `|Γ^i_{jk}(p)| ≤ Mc` for all `i,j,k`, then the
    quadratic form `Γ_p(a,b)_i = ∑_{j,k} Γ^i_{jk}(p) a_j b_k` obeys `‖Γ_p(a,b)‖ ≤ Mc·n²·‖a‖·‖b‖`. -/
theorem christoffel_bilin_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (p a b : Point n) {Mc : ℝ} (hMc0 : 0 ≤ Mc)
    (hMc : ∀ i j k, |christoffel g gi i j k p| ≤ Mc) :
    ‖(fun i => ∑ j, ∑ k, christoffel g gi i j k p * a j * b k : Point n)‖
      ≤ Mc * (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Real.norm_eq_abs]
  have hterm : ∀ j k : Fin n, |christoffel g gi i j k p * a j * b k| ≤ Mc * (‖a‖ * ‖b‖) := by
    intro j k
    rw [abs_mul, abs_mul]
    have h1 : |christoffel g gi i j k p| ≤ Mc := hMc i j k
    have h2 : |a j| ≤ ‖a‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a j
    have h3 : |b k| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k
    calc |christoffel g gi i j k p| * |a j| * |b k|
        ≤ Mc * ‖a‖ * ‖b‖ :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hMc0) h3 (abs_nonneg _) (by positivity)
      _ = Mc * (‖a‖ * ‖b‖) := by ring
  calc |∑ j, ∑ k, christoffel g gi i j k p * a j * b k|
      ≤ ∑ j, |∑ k, christoffel g gi i j k p * a j * b k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, Mc * (‖a‖ * ‖b‖) :=
        Finset.sum_le_sum fun j _ =>
          (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
    _ = Mc * (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Sup-norm bound for a difference of Christoffel quadratic forms at two base points.**  With `|Γ^i_{jk}(p)| ≤
    Mc` and `|Γ^i_{jk}(p) − Γ^i_{jk}(y)| ≤ Lc·‖y − p‖`, the difference `Γ_p(a,a) − Γ_y(b,b)` obeys
    `‖Γ_p(a,a) − Γ_y(b,b)‖ ≤ Mc·n²·(‖a−b‖·(‖a‖+‖b‖)) + Lc·n²·(‖y−p‖·‖b‖²)`.  The two terms come from the algebraic
    split `Γ^i_{jk}(p) a_j a_k − Γ^i_{jk}(y) b_j b_k = Γ^i_{jk}(p)(a_j a_k − b_j b_k) + (Γ^i_{jk}(p) − Γ^i_{jk}(y)) b_j b_k`. -/
theorem christoffel_quad_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (p y a b : Point n) {Mc Lc : ℝ} (hMc0 : 0 ≤ Mc) (hLc0 : 0 ≤ Lc)
    (hMc : ∀ i j k, |christoffel g gi i j k p| ≤ Mc)
    (hLc : ∀ i j k, |christoffel g gi i j k p - christoffel g gi i j k y| ≤ Lc * ‖y - p‖) :
    ‖(fun i => (∑ j, ∑ k, christoffel g gi i j k p * a j * a k)
              - (∑ j, ∑ k, christoffel g gi i j k y * b j * b k) : Point n)‖
      ≤ Mc * (n : ℝ) ^ 2 * (‖a - b‖ * (‖a‖ + ‖b‖)) + Lc * (n : ℝ) ^ 2 * (‖y - p‖ * ‖b‖ ^ 2) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Real.norm_eq_abs]
  have hterm : ∀ j k : Fin n,
      |christoffel g gi i j k p * a j * a k - christoffel g gi i j k y * b j * b k|
        ≤ Mc * (‖a - b‖ * (‖a‖ + ‖b‖)) + Lc * ‖y - p‖ * ‖b‖ ^ 2 := by
    intro j k
    have e1 : christoffel g gi i j k p * a j * a k - christoffel g gi i j k y * b j * b k
        = christoffel g gi i j k p * (a j * a k - b j * b k)
          + (christoffel g gi i j k p - christoffel g gi i j k y) * (b j * b k) := by ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hd : |a j * a k - b j * b k| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
      have e2 : a j * a k - b j * b k = a j * (a k - b k) + (a j - b j) * b k := by ring
      rw [e2]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have haj : |a j| ≤ ‖a‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a j
      have hbk : |b k| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k
      have hakbk : |a k - b k| ≤ ‖a - b‖ := by
        rw [← Real.norm_eq_abs, show a k - b k = (a - b) k from (Pi.sub_apply a b k).symm]
        exact norm_le_pi_norm (a - b) k
      have hajbj : |a j - b j| ≤ ‖a - b‖ := by
        rw [← Real.norm_eq_abs, show a j - b j = (a - b) j from (Pi.sub_apply a b j).symm]
        exact norm_le_pi_norm (a - b) j
      calc |a j| * |a k - b k| + |a j - b j| * |b k|
          ≤ ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ :=
            add_le_add (mul_le_mul haj hakbk (abs_nonneg _) (norm_nonneg _))
              (mul_le_mul hajbj hbk (abs_nonneg _) (norm_nonneg _))
        _ = ‖a - b‖ * (‖a‖ + ‖b‖) := by ring
    have hbb : |b j * b k| ≤ ‖b‖ ^ 2 := by
      rw [abs_mul]
      have hbj : |b j| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b j
      have hbk : |b k| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k
      calc |b j| * |b k| ≤ ‖b‖ * ‖b‖ := mul_le_mul hbj hbk (abs_nonneg _) (norm_nonneg _)
        _ = ‖b‖ ^ 2 := by ring
    have h1 : |christoffel g gi i j k p| ≤ Mc := hMc i j k
    have h2 : |christoffel g gi i j k p - christoffel g gi i j k y| ≤ Lc * ‖y - p‖ := hLc i j k
    exact add_le_add (mul_le_mul h1 hd (abs_nonneg _) hMc0)
      (mul_le_mul h2 hbb (abs_nonneg _) (by positivity))
  have hstep : ∀ j : Fin n,
      |(∑ k, christoffel g gi i j k p * a j * a k) - (∑ k, christoffel g gi i j k y * b j * b k)|
        ≤ ∑ _k : Fin n, (Mc * (‖a - b‖ * (‖a‖ + ‖b‖)) + Lc * ‖y - p‖ * ‖b‖ ^ 2) := by
    intro j
    rw [← Finset.sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
  rw [← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hstep j).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The zero-initial-data unit-time Grönwall proportionality bound is `≤ e^K`:
    `gronwallBound 0 K 1 1 ≤ Real.exp K` for `K ≥ 0`. -/
theorem gronwallBound_zero_one_le_exp (K : ℝ) (hK : 0 ≤ K) :
    gronwallBound 0 K 1 1 ≤ Real.exp K := by
  rcases eq_or_lt_of_le hK with hK0 | hK0
  · rw [← hK0, gronwallBound_K0]; simp
  · have hEK : 0 < Real.exp K := Real.exp_pos K
    have h1 : (1 - K) ≤ 1 / Real.exp K := by
      have := Real.add_one_le_exp (-K)
      rw [Real.exp_neg] at this
      rw [one_div]; linarith
    rw [le_div_iff₀ hEK] at h1
    have hfin : (Real.exp K - 1) / K ≤ Real.exp K := by
      rw [div_le_iff₀ hK0]; nlinarith [h1]
    have hval : gronwallBound 0 K 1 1 = (Real.exp K - 1) / K := by
      rw [gronwallBound_of_K_ne_0 hK0.ne']
      show 0 * Real.exp (K * 1) + 1 / K * (Real.exp (K * 1) - 1) = (Real.exp K - 1) / K
      rw [mul_one, zero_mul, zero_add, one_div_mul_eq_div]
    rw [hval]; exact hfin

/-- The zero-initial-data Grönwall proportionality bound on `[0,1]` is `≤ ε·e^K`, uniformly in the
    time `t ∈ [0,1]`: `gronwallBound 0 K ε t ≤ ε · Real.exp K` for `K ≥ 0`, `ε ≥ 0`, `t ∈ [0,1]`.
    Generalizes `gronwallBound_zero_one_le_exp` to arbitrary `ε` and interior times `t`. -/
theorem gronwallBound_zero_le_exp (K ε t : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) : gronwallBound 0 K ε t ≤ ε * Real.exp K := by
  have hstep : gronwallBound 0 K ε t = ε * gronwallBound 0 K 1 t := by
    simp only [gronwallBound]; split_ifs <;> ring
  rw [hstep]
  have hb : gronwallBound 0 K 1 t ≤ Real.exp K := by
    simp only [gronwallBound]
    split_ifs with hK0
    · subst hK0
      rw [Real.exp_zero]; linarith
    · have hKpos : 0 < K := hK.lt_of_ne (Ne.symm hK0)
      rw [zero_mul, zero_add]
      have hexpKt : Real.exp (K * t) ≤ Real.exp K :=
        Real.exp_le_exp.mpr (mul_le_of_le_one_right hKpos.le ht1)
      have hle : (Real.exp K - 1) / K ≤ Real.exp K := by
        have h := Real.add_one_le_exp (-K)
        rw [Real.exp_neg] at h
        have hEK := Real.exp_pos K
        rw [div_le_iff₀ hKpos]
        have h2 : (-K + 1) * Real.exp K ≤ 1 := by
          have := mul_le_mul_of_nonneg_right h hEK.le
          rwa [inv_mul_cancel₀ hEK.ne'] at this
        nlinarith [h2]
      calc 1 / K * (Real.exp (K * t) - 1)
          ≤ 1 / K * (Real.exp K - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (Real.exp K - 1) / K := by ring
        _ ≤ Real.exp K := hle
  exact mul_le_mul_of_nonneg_left hb hε

set_option maxHeartbeats 1600000 in
/-- **EXP-JET1 — the value 2-jet of the exponential map at `0`.**
    `exp_p(v) = p + v − ½Γ_p(v,v) + o(‖v‖²)`, i.e.
    `(fun v => exp_p v − p − v + ½·Γ_p(v,v)) =o[𝓝 0] (fun v => ‖v‖²)`, with
    `Γ_p(v,v)_i = ∑_{j,k} Γ^i_{jk}(p) v_j v_k`.

    The geodesic tube `Y = expTube p v` is compared to the explicit model curve
    `M(t) = (p + t·v − ½t²·Γ_p(v,v), v − t·Γ_p(v,v))`.  The residual `q = Y − M` has `q 0 = 0` and
    `q'(t) = geodesicField(Y t) − M'(t) = ((q t).2, Γ_p(v,v) − Γ_{(Y t).1}((Y t).2,(Y t).2))`.  The a-priori
    confinement (`expTube_spec`) plus the local Christoffel bounds (value bound `Mc`, Lipschitz `Lc` on
    `closedBall p R`) give `‖q'(t)‖ ≤ (1 + Bcoef‖v‖)‖q t‖ + Acoef‖v‖³` on `[0,1]`, so the inhomogeneous
    Grönwall bound yields `‖q 1‖ ≤ Cfinal·‖v‖³`; projecting the position component gives
    `‖exp_p v − p − v + ½Γ_p(v,v)‖ ≤ Cfinal‖v‖³ = o(‖v‖²)`.

    HONEST CAPTION (binding): this is the Fréchet value 2-jet of `exp_p` at `0`.  It is a step toward
    discharging the RNC gauge; it does NOT yet discharge `hgauge`, NOT build the pullback metric, NOT move
    numerical-G (`N`, `Λ_s`, `E/ξ` remain). -/
theorem expMap_value_two_jet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    (fun v => expMap g gi hC p v - p - v
        + (1 / 2 : ℝ) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n))
      =o[𝓝 (0 : Point n)] (fun v => ‖v‖ ^ 2) := by
  have hρpos := expRho_pos g gi hC p
  have hC₀ := expConst_nonneg g gi hC p
  set ρ : ℝ := expRho g gi hC p with hρ
  set C₀ : ℝ := expConst g gi hC p with hC₀def
  set R : ℝ := C₀ * ρ with hRdef
  have hR0 : 0 ≤ R := mul_nonneg hC₀ hρpos.le
  have hpmem : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self hR0
  -- The Christoffel tensor as a map, and its value / Lipschitz bounds on `closedBall p R`.
  set T : Point n → (Fin n → Fin n → Fin n → ℝ) :=
    fun y => (fun i j k => christoffel g gi i j k y) with hTdef
  have hTcd : ContDiff ℝ (⊤ : WithTop ℕ∞) T :=
    contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => contDiff_pi.mpr fun k => hC i j k
  obtain ⟨Mc, hMcsub⟩ :=
    (((isCompact_closedBall p R).image_of_continuousOn
      hTcd.continuous.continuousOn).isBounded).subset_closedBall (0 : Fin n → Fin n → Fin n → ℝ)
  have hTyp : ‖T p‖ ≤ Mc := by
    have := hMcsub (Set.mem_image_of_mem T hpmem)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have Mc0 : 0 ≤ Mc := le_trans (norm_nonneg _) hTyp
  have hMc : ∀ y ∈ Metric.closedBall p R, ∀ i j k, |christoffel g gi i j k y| ≤ Mc := by
    intro y hy i j k
    have hTy : ‖T y‖ ≤ Mc := by
      have := hMcsub (Set.mem_image_of_mem T hy)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have e : christoffel g gi i j k y = T y i j k := by simp only [hTdef]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (T y i j) k).trans
      ((norm_le_pi_norm (T y i) j).trans (norm_le_pi_norm (T y) i))).trans hTy
  obtain ⟨Lc, hLip⟩ :=
    (hTcd.contDiffOn (s := Metric.closedBall p R)).exists_lipschitzOnWith (by simp)
      (convex_closedBall p R) (isCompact_closedBall p R)
  have Lc0 : 0 ≤ (Lc : ℝ) := Lc.coe_nonneg
  have hLc : ∀ y ∈ Metric.closedBall p R, ∀ i j k,
      |christoffel g gi i j k p - christoffel g gi i j k y| ≤ (Lc : ℝ) * ‖y - p‖ := by
    intro y hy i j k
    have hd := hLip.dist_le_mul p hpmem y hy
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev p y] at hd
    have e : christoffel g gi i j k p - christoffel g gi i j k y = (T p - T y) i j k := by
      simp only [hTdef, Pi.sub_apply]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm ((T p - T y) i j) k).trans
      ((norm_le_pi_norm ((T p - T y) i) j).trans (norm_le_pi_norm (T p - T y) i))).trans hd
  -- The constants of the Grönwall estimate.
  set Acoef : ℝ := Mc ^ 2 * (n : ℝ) ^ 4 * (1 + C₀) + (Lc : ℝ) * (n : ℝ) ^ 2 * C₀ ^ 3 with hAcoefdef
  set Bcoef : ℝ := Mc * (n : ℝ) ^ 2 * (1 + C₀) with hBcoefdef
  have hBcoef0 : 0 ≤ Bcoef := by
    rw [hBcoefdef]; exact mul_nonneg (mul_nonneg Mc0 (by positivity)) (by linarith [hC₀])
  have hAcoef0 : 0 ≤ Acoef := by
    rw [hAcoefdef]
    have t1 : 0 ≤ Mc ^ 2 * (n : ℝ) ^ 4 * (1 + C₀) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (by linarith [hC₀])
    have t2 : 0 ≤ (Lc : ℝ) * (n : ℝ) ^ 2 * C₀ ^ 3 :=
      mul_nonneg (mul_nonneg Lc0 (by positivity)) (pow_nonneg hC₀ 3)
    linarith
  set Kmax : ℝ := 1 + Bcoef * ρ with hKmaxdef
  set Cfinal : ℝ := Acoef * Real.exp Kmax with hCfinaldef
  have hCfinal0 : 0 ≤ Cfinal := by rw [hCfinaldef]; exact mul_nonneg hAcoef0 (Real.exp_pos _).le
  -- The core `O(‖v‖³)` bound for `‖v‖ ≤ ρ`.
  have hbound : ∀ v : Point n, ‖v‖ ≤ ρ →
      ‖expMap g gi hC p v - p - v
          + (1 / 2 : ℝ) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)‖
        ≤ Cfinal * ‖v‖ ^ 3 := by
    intro v hvρ
    obtain ⟨hY0, hYd, hYconf⟩ := expTube_spec g gi hC p v hvρ
    set Y : ℝ → Point n × Point n := expTube g gi hC p v with hYdef
    set Γv : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k with hΓvdef
    have hΓv_bound : ‖Γv‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      rw [hΓvdef]
      have h := christoffel_bilin_bound g gi p v v Mc0 (fun i j k => hMc p hpmem i j k)
      calc ‖(fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)‖
          ≤ Mc * (n : ℝ) ^ 2 * (‖v‖ * ‖v‖) := h
        _ = Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by ring
    set M : ℝ → Point n × Point n :=
      fun τ => (p + τ • v - (τ ^ 2 / 2) • Γv, v - τ • Γv) with hMdef
    have hM : ∀ t : ℝ, HasDerivAt M ((v - t • Γv, -Γv) : Point n × Point n) t := by
      intro t
      rw [hMdef]
      have hc1 : HasDerivAt (fun τ : ℝ => p + τ • v - (τ ^ 2 / 2) • Γv) (v - t • Γv) t := by
        have hp : HasDerivAt (fun _ : ℝ => p) (0 : Point n) t := hasDerivAt_const t p
        have hv1 : HasDerivAt (fun τ : ℝ => τ • v) v t := by
          simpa using (hasDerivAt_id t).smul_const v
        have hsq : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
          convert (hasDerivAt_pow 2 t).div_const 2 using 1
          norm_num
        have hquad : HasDerivAt (fun τ : ℝ => (τ ^ 2 / 2) • Γv) (t • Γv) t := hsq.smul_const Γv
        have := (hp.add hv1).sub hquad
        simpa using this
      have hc2 : HasDerivAt (fun τ : ℝ => v - τ • Γv) (-Γv) t := by
        have hvc : HasDerivAt (fun _ : ℝ => v) (0 : Point n) t := hasDerivAt_const t v
        have hτΓ : HasDerivAt (fun τ : ℝ => τ • Γv) Γv t := by
          simpa using (hasDerivAt_id t).smul_const Γv
        have := hvc.sub hτΓ
        simpa using this
      exact hc1.prodMk hc2
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun τ => Y τ - M τ)
          (geodesicField g gi (Y t) - ((v - t • Γv, -Γv) : Point n × Point n)) t :=
      fun t ht => (hYd t (hIcc_Ioo t ht)).sub (hM t)
    have hf : ContinuousOn (fun τ => Y τ - M τ) (Set.Icc (0 : ℝ) 1) :=
      fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt
    have hf' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ => Y τ - M τ)
        (geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)) (Set.Ici x) x :=
      fun x hx => (hfderiv x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt
    have ha : ‖(fun τ => Y τ - M τ) 0‖ ≤ 0 := by
      show ‖Y 0 - M 0‖ ≤ 0
      have hM0 : M 0 = (p, v) := by
        show (p + (0 : ℝ) • v - ((0 : ℝ) ^ 2 / 2) • Γv, v - (0 : ℝ) • Γv) = (p, v)
        simp
      rw [hY0, hM0, sub_self, norm_zero]
    have bound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        ‖geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)‖
          ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      have hx0 : (0 : ℝ) ≤ x := hx.1
      have hx1 : x < 1 := hx.2
      have hconf := hYconf x hxIcc
      have hMx2 : (M x).2 = v - x • Γv := by simp only [hMdef]
      have hw : ‖(Y x).2‖ ≤ C₀ * ‖v‖ := by
        have e : (Y x).2 = (Y x - ((p, 0) : Point n × Point n)).2 := by simp [Prod.snd_sub]
        rw [e]
        exact le_trans (by rw [Prod.norm_def]; exact le_max_right _ _) hconf
      have hy1 : ‖(Y x).1 - p‖ ≤ C₀ * ‖v‖ := by
        have e : (Y x).1 - p = (Y x - ((p, 0) : Point n × Point n)).1 := by simp [Prod.fst_sub]
        rw [e]
        exact le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) hconf
      have hyxmem : (Y x).1 ∈ Metric.closedBall p R := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖(Y x).1 - p‖ ≤ C₀ * ‖v‖ := hy1
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀
          _ = R := by rw [hRdef]
      -- the residual ODE has `q'(x) = ((q x).2, Γ_p(v,v) − Γ_{(Y x).1}((Y x).2,(Y x).2))`.
      have hid : geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)
          = ((Y x).2 - (v - x • Γv),
              (fun i => (∑ j, ∑ k, christoffel g gi i j k p * v j * v k)
                      - (∑ j, ∑ k, christoffel g gi i j k (Y x).1 * (Y x).2 j * (Y x).2 k)))
            := by
        refine Prod.ext ?_ ?_
        · simp [geodesicField]
        · funext i
          simp only [geodesicField, Prod.snd_sub, hΓvdef, Pi.sub_apply, Pi.neg_apply]
          ring
      -- the velocity gap `v − (Y x).2` is `O(‖v‖²) + ‖q x‖`.
      have hveq : v - (Y x).2 = x • Γv - (Y x - M x).2 := by
        rw [Prod.snd_sub, hMx2]; abel
      have hvw : ‖v - (Y x).2‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖ := by
        rw [hveq]
        have hxΓ : ‖x • Γv‖ ≤ ‖Γv‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
          calc x * ‖Γv‖ ≤ 1 * ‖Γv‖ := mul_le_mul_of_nonneg_right hx1.le (norm_nonneg _)
            _ = ‖Γv‖ := one_mul _
        have hsnd : ‖(Y x - M x).2‖ ≤ ‖Y x - M x‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
        calc ‖x • Γv - (Y x - M x).2‖
            ≤ ‖x • Γv‖ + ‖(Y x - M x).2‖ := norm_sub_le _ _
          _ ≤ ‖Γv‖ + ‖Y x - M x‖ := add_le_add hxΓ hsnd
          _ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖ := by linarith [hΓv_bound]
      -- the Christoffel-difference bound feeding the inhomogeneous term.
      have hbnd := christoffel_quad_diff_bound g gi p (Y x).1 v (Y x).2 Mc0 Lc0
        (fun i j k => hMc p hpmem i j k) (fun i j k => hLc (Y x).1 hyxmem i j k)
      have hP2 : ‖v‖ + ‖(Y x).2‖ ≤ (1 + C₀) * ‖v‖ := by
        have he : (1 + C₀) * ‖v‖ = ‖v‖ + C₀ * ‖v‖ := by ring
        rw [he]; linarith [hw]
      have hP4 : ‖(Y x).2‖ ^ 2 ≤ (C₀ * ‖v‖) ^ 2 := by
        have := hw; gcongr
      have step : Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
            + (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
          ≤ Acoef * ‖v‖ ^ 3 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
        have e1 : Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
            ≤ Mc * (n : ℝ) ^ 2
              * ((Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖) * ((1 + C₀) * ‖v‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hvw hP2 (by positivity) (by positivity))
            (by positivity)
        have e2 : (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
            ≤ (Lc : ℝ) * (n : ℝ) ^ 2 * ((C₀ * ‖v‖) * (C₀ * ‖v‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hy1 hP4 (by positivity) (by positivity))
            (by positivity)
        calc Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
              + (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
            ≤ Mc * (n : ℝ) ^ 2
                * ((Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖) * ((1 + C₀) * ‖v‖))
              + (Lc : ℝ) * (n : ℝ) ^ 2 * ((C₀ * ‖v‖) * (C₀ * ‖v‖) ^ 2) := add_le_add e1 e2
          _ = Acoef * ‖v‖ ^ 3 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
              rw [hAcoefdef, hBcoefdef]; ring
      have hBle : ‖(fun i => (∑ j, ∑ k, christoffel g gi i j k p * v j * v k)
            - (∑ j, ∑ k, christoffel g gi i j k (Y x).1 * (Y x).2 j * (Y x).2 k) : Point n)‖
          ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
        have hb := hbnd.trans step
        have hexp : (1 + Bcoef * ‖v‖) * ‖Y x - M x‖
            = ‖Y x - M x‖ + Bcoef * ‖v‖ * ‖Y x - M x‖ := by ring
        rw [hexp]; linarith [hb, norm_nonneg (Y x - M x)]
      have hAle : ‖(Y x).2 - (v - x • Γv)‖
          ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
        have hAle0 : ‖(Y x).2 - (v - x • Γv)‖ ≤ ‖Y x - M x‖ := by
          have e : (Y x).2 - (v - x • Γv) = (Y x - M x).2 := by rw [Prod.snd_sub, hMx2]
          rw [e, Prod.norm_def]; exact le_max_right _ _
        have h2' : ‖Y x - M x‖ ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ :=
          le_mul_of_one_le_left (norm_nonneg _)
            (by have := mul_nonneg hBcoef0 (norm_nonneg v); linarith)
        have h3' : 0 ≤ Acoef * ‖v‖ ^ 3 := mul_nonneg hAcoef0 (by positivity)
        linarith
      rw [hid, Prod.norm_def]
      exact max_le hAle hBle
    -- inhomogeneous Grönwall.
    have hg1 := (norm_le_gronwallBound_of_norm_deriv_right_le hf hf' ha bound) 1
      (by norm_num [Set.mem_Icc])
    rw [sub_zero] at hg1
    -- project the position component of `q 1`.
    have htarget : expMap g gi hC p v - p - v + (1 / 2 : ℝ) • Γv = (Y 1 - M 1).1 := by
      rw [Prod.fst_sub]
      have hM1 : (M 1).1 = p + v - (1 / 2 : ℝ) • Γv := by
        show p + (1 : ℝ) • v - ((1 : ℝ) ^ 2 / 2) • Γv = p + v - (1 / 2 : ℝ) • Γv
        rw [one_smul, one_pow]
      have hexpeq : expMap g gi hC p v = (Y 1).1 := by simp only [expMap, hYdef]
      rw [hM1, hexpeq]; abel
    have h2 : gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 3) 1 ≤ Cfinal * ‖v‖ ^ 3 := by
      rw [gronwallBound_zero_linear]
      have hKpos : 0 ≤ 1 + Bcoef * ‖v‖ := by
        have := mul_nonneg hBcoef0 (norm_nonneg v); linarith
      have hAv0 : 0 ≤ Acoef * ‖v‖ ^ 3 := mul_nonneg hAcoef0 (by positivity)
      have hKle : 1 + Bcoef * ‖v‖ ≤ Kmax := by
        rw [hKmaxdef]
        have : Bcoef * ‖v‖ ≤ Bcoef * ρ := mul_le_mul_of_nonneg_left hvρ hBcoef0
        linarith
      calc Acoef * ‖v‖ ^ 3 * gronwallBound 0 (1 + Bcoef * ‖v‖) 1 1
          ≤ Acoef * ‖v‖ ^ 3 * Real.exp (1 + Bcoef * ‖v‖) :=
            mul_le_mul_of_nonneg_left (gronwallBound_zero_one_le_exp _ hKpos) hAv0
        _ ≤ Acoef * ‖v‖ ^ 3 * Real.exp Kmax :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKle) hAv0
        _ = Cfinal * ‖v‖ ^ 3 := by rw [hCfinaldef]; ring
    rw [htarget]
    calc ‖(Y 1 - M 1).1‖
        ≤ ‖Y 1 - M 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 3) 1 := hg1
      _ ≤ Cfinal * ‖v‖ ^ 3 := h2
  -- Package `O(‖v‖³)` into `o(‖v‖²)`.
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev1 : ∀ᶠ v in 𝓝 (0 : Point n), ‖v‖ ≤ ρ :=
    Metric.eventually_nhds_iff.mpr ⟨ρ, hρpos, fun v hv => by
      rw [dist_zero_right] at hv; exact hv.le⟩
  have hev2 : ∀ᶠ v in 𝓝 (0 : Point n), ‖v‖ ≤ c / (Cfinal + 1) :=
    Metric.eventually_nhds_iff.mpr ⟨c / (Cfinal + 1), div_pos hc (by linarith [hCfinal0]),
      fun v hv => by rw [dist_zero_right] at hv; exact hv.le⟩
  filter_upwards [hev1, hev2] with v hv1 hv2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hCv : Cfinal * ‖v‖ ≤ c := by
    calc Cfinal * ‖v‖ ≤ Cfinal * (c / (Cfinal + 1)) := mul_le_mul_of_nonneg_left hv2 hCfinal0
      _ = Cfinal / (Cfinal + 1) * c := by ring
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right
          (by rw [div_le_one (by linarith [hCfinal0])]; linarith [hCfinal0]) hc.le
      _ = c := one_mul c
  calc ‖expMap g gi hC p v - p - v
          + (1 / 2 : ℝ) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)‖
      ≤ Cfinal * ‖v‖ ^ 3 := hbound v hv1
    _ = Cfinal * ‖v‖ * ‖v‖ ^ 2 := by ring
    _ ≤ c * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hCv (sq_nonneg _)

set_option maxHeartbeats 1600000 in
/-- **EXP-JET3c (STEP 1 ingredient) — the uniform-in-`t` tube value 2-jet.**  For `‖v‖ ≤ ρ` the whole
    confined geodesic tube `Y_v(t) = expTube p v t` (not just its position endpoint at `t = 1`) is
    `O(‖v‖³)`-close, UNIFORMLY in `t ∈ [0,1]`, to the explicit model curve
    `M(t) = (p + t·v − ½t²·Γ_p(v,v), v − t·Γ_p(v,v))`:
    `‖Y_v(t) − M(t)‖ ≤ C·‖v‖³` on `[0,1]`, with `Γ_p(v,v)_i = ∑_{jk} Γ^i_{jk}(p) v_j v_k`.

    This is the value 2-jet of the tube `Y_v(t) − e = S₁(t,v) + S₂(t,v) + O(‖v‖³)`,
    `S₁ = (t·v, v)`, `S₂ = (−½t²Γ_p(v,v), −t·Γ_p(v,v))` — the input the operator-valued Jacobian
    2-jet's uniform `DF(Y_v t)` expansion consumes (compose `geodesicField_fderiv_apply` at
    `(x,u) = Y_v(t)` with this).  Same equilibrium-anchored residual-ODE + inhomogeneous Grönwall as
    `expMap_value_two_jet`, but with the Grönwall applied at every `t ∈ [0,1]` and BOTH components
    exposed (no position projection).

    HONEST: the uniform-in-`t`, full-phase-vector value 2-jet of the geodesic tube.  It does NOT by
    itself give the operator `DF` expansion, NOT the Jacobian 2-jet, NOT the pullback metric, NOT
    numerical-G (`N`, `Λ_s`, `E/ξ` remain). -/
theorem expTube_value_two_jet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ v : Point n, ‖v‖ ≤ ρ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t
          - (p + t • v
              - (t ^ 2 / 2) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n),
             v - t • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n))‖
        ≤ C * ‖v‖ ^ 3 := by
  have hρpos := expRho_pos g gi hC p
  have hC₀ := expConst_nonneg g gi hC p
  set ρ : ℝ := expRho g gi hC p with hρ
  set C₀ : ℝ := expConst g gi hC p with hC₀def
  set R : ℝ := C₀ * ρ with hRdef
  have hR0 : 0 ≤ R := mul_nonneg hC₀ hρpos.le
  have hpmem : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self hR0
  set T : Point n → (Fin n → Fin n → Fin n → ℝ) :=
    fun y => (fun i j k => christoffel g gi i j k y) with hTdef
  have hTcd : ContDiff ℝ (⊤ : WithTop ℕ∞) T :=
    contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => contDiff_pi.mpr fun k => hC i j k
  obtain ⟨Mc, hMcsub⟩ :=
    (((isCompact_closedBall p R).image_of_continuousOn
      hTcd.continuous.continuousOn).isBounded).subset_closedBall (0 : Fin n → Fin n → Fin n → ℝ)
  have hTyp : ‖T p‖ ≤ Mc := by
    have := hMcsub (Set.mem_image_of_mem T hpmem)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have Mc0 : 0 ≤ Mc := le_trans (norm_nonneg _) hTyp
  have hMc : ∀ y ∈ Metric.closedBall p R, ∀ i j k, |christoffel g gi i j k y| ≤ Mc := by
    intro y hy i j k
    have hTy : ‖T y‖ ≤ Mc := by
      have := hMcsub (Set.mem_image_of_mem T hy)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have e : christoffel g gi i j k y = T y i j k := by simp only [hTdef]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (T y i j) k).trans
      ((norm_le_pi_norm (T y i) j).trans (norm_le_pi_norm (T y) i))).trans hTy
  obtain ⟨Lc, hLip⟩ :=
    (hTcd.contDiffOn (s := Metric.closedBall p R)).exists_lipschitzOnWith (by simp)
      (convex_closedBall p R) (isCompact_closedBall p R)
  have Lc0 : 0 ≤ (Lc : ℝ) := Lc.coe_nonneg
  have hLc : ∀ y ∈ Metric.closedBall p R, ∀ i j k,
      |christoffel g gi i j k p - christoffel g gi i j k y| ≤ (Lc : ℝ) * ‖y - p‖ := by
    intro y hy i j k
    have hd := hLip.dist_le_mul p hpmem y hy
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev p y] at hd
    have e : christoffel g gi i j k p - christoffel g gi i j k y = (T p - T y) i j k := by
      simp only [hTdef, Pi.sub_apply]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm ((T p - T y) i j) k).trans
      ((norm_le_pi_norm ((T p - T y) i) j).trans (norm_le_pi_norm (T p - T y) i))).trans hd
  set Acoef : ℝ := Mc ^ 2 * (n : ℝ) ^ 4 * (1 + C₀) + (Lc : ℝ) * (n : ℝ) ^ 2 * C₀ ^ 3 with hAcoefdef
  set Bcoef : ℝ := Mc * (n : ℝ) ^ 2 * (1 + C₀) with hBcoefdef
  have hBcoef0 : 0 ≤ Bcoef := by
    rw [hBcoefdef]; exact mul_nonneg (mul_nonneg Mc0 (by positivity)) (by linarith [hC₀])
  have hAcoef0 : 0 ≤ Acoef := by
    rw [hAcoefdef]
    have t1 : 0 ≤ Mc ^ 2 * (n : ℝ) ^ 4 * (1 + C₀) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) (by linarith [hC₀])
    have t2 : 0 ≤ (Lc : ℝ) * (n : ℝ) ^ 2 * C₀ ^ 3 :=
      mul_nonneg (mul_nonneg Lc0 (by positivity)) (pow_nonneg hC₀ 3)
    linarith
  set Kmax : ℝ := 1 + Bcoef * ρ with hKmaxdef
  set Cfinal : ℝ := Acoef * Real.exp Kmax with hCfinaldef
  have hCfinal0 : 0 ≤ Cfinal := by rw [hCfinaldef]; exact mul_nonneg hAcoef0 (Real.exp_pos _).le
  refine ⟨ρ, hρpos, Cfinal, hCfinal0, fun v hvρ t ht => ?_⟩
  obtain ⟨hY0, hYd, hYconf⟩ := expTube_spec g gi hC p v hvρ
  set Y : ℝ → Point n × Point n := expTube g gi hC p v with hYdef
  set Γv : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k with hΓvdef
  have hΓv_bound : ‖Γv‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    rw [hΓvdef]
    have h := christoffel_bilin_bound g gi p v v Mc0 (fun i j k => hMc p hpmem i j k)
    calc ‖(fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)‖
        ≤ Mc * (n : ℝ) ^ 2 * (‖v‖ * ‖v‖) := h
      _ = Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by ring
  set M : ℝ → Point n × Point n :=
    fun τ => (p + τ • v - (τ ^ 2 / 2) • Γv, v - τ • Γv) with hMdef
  have hM : ∀ t : ℝ, HasDerivAt M ((v - t • Γv, -Γv) : Point n × Point n) t := by
    intro t
    rw [hMdef]
    have hc1 : HasDerivAt (fun τ : ℝ => p + τ • v - (τ ^ 2 / 2) • Γv) (v - t • Γv) t := by
      have hp : HasDerivAt (fun _ : ℝ => p) (0 : Point n) t := hasDerivAt_const t p
      have hv1 : HasDerivAt (fun τ : ℝ => τ • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      have hsq : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
        convert (hasDerivAt_pow 2 t).div_const 2 using 1
        norm_num
      have hquad : HasDerivAt (fun τ : ℝ => (τ ^ 2 / 2) • Γv) (t • Γv) t := hsq.smul_const Γv
      have := (hp.add hv1).sub hquad
      simpa using this
    have hc2 : HasDerivAt (fun τ : ℝ => v - τ • Γv) (-Γv) t := by
      have hvc : HasDerivAt (fun _ : ℝ => v) (0 : Point n) t := hasDerivAt_const t v
      have hτΓ : HasDerivAt (fun τ : ℝ => τ • Γv) Γv t := by
        simpa using (hasDerivAt_id t).smul_const Γv
      have := hvc.sub hτΓ
      simpa using this
    exact hc1.prodMk hc2
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun τ => Y τ - M τ)
        (geodesicField g gi (Y t) - ((v - t • Γv, -Γv) : Point n × Point n)) t :=
    fun t ht => (hYd t (hIcc_Ioo t ht)).sub (hM t)
  have hf : ContinuousOn (fun τ => Y τ - M τ) (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt
  have hf' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ => Y τ - M τ)
      (geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)) (Set.Ici x) x :=
    fun x hx => (hfderiv x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt
  have ha : ‖(fun τ => Y τ - M τ) 0‖ ≤ 0 := by
    show ‖Y 0 - M 0‖ ≤ 0
    have hM0 : M 0 = (p, v) := by
      show (p + (0 : ℝ) • v - ((0 : ℝ) ^ 2 / 2) • Γv, v - (0 : ℝ) • Γv) = (p, v)
      simp
    rw [hY0, hM0, sub_self, norm_zero]
  have bound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)‖
        ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hx1 : x < 1 := hx.2
    have hconf := hYconf x hxIcc
    have hMx2 : (M x).2 = v - x • Γv := by simp only [hMdef]
    have hw : ‖(Y x).2‖ ≤ C₀ * ‖v‖ := by
      have e : (Y x).2 = (Y x - ((p, 0) : Point n × Point n)).2 := by simp [Prod.snd_sub]
      rw [e]
      exact le_trans (by rw [Prod.norm_def]; exact le_max_right _ _) hconf
    have hy1 : ‖(Y x).1 - p‖ ≤ C₀ * ‖v‖ := by
      have e : (Y x).1 - p = (Y x - ((p, 0) : Point n × Point n)).1 := by simp [Prod.fst_sub]
      rw [e]
      exact le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) hconf
    have hyxmem : (Y x).1 ∈ Metric.closedBall p R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖(Y x).1 - p‖ ≤ C₀ * ‖v‖ := hy1
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀
        _ = R := by rw [hRdef]
    have hid : geodesicField g gi (Y x) - ((v - x • Γv, -Γv) : Point n × Point n)
        = ((Y x).2 - (v - x • Γv),
            (fun i => (∑ j, ∑ k, christoffel g gi i j k p * v j * v k)
                    - (∑ j, ∑ k, christoffel g gi i j k (Y x).1 * (Y x).2 j * (Y x).2 k)))
          := by
      refine Prod.ext ?_ ?_
      · simp [geodesicField]
      · funext i
        simp only [geodesicField, Prod.snd_sub, hΓvdef, Pi.sub_apply, Pi.neg_apply]
        ring
    have hveq : v - (Y x).2 = x • Γv - (Y x - M x).2 := by
      rw [Prod.snd_sub, hMx2]; abel
    have hvw : ‖v - (Y x).2‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖ := by
      rw [hveq]
      have hxΓ : ‖x • Γv‖ ≤ ‖Γv‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
        calc x * ‖Γv‖ ≤ 1 * ‖Γv‖ := mul_le_mul_of_nonneg_right hx1.le (norm_nonneg _)
          _ = ‖Γv‖ := one_mul _
      have hsnd : ‖(Y x - M x).2‖ ≤ ‖Y x - M x‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      calc ‖x • Γv - (Y x - M x).2‖
          ≤ ‖x • Γv‖ + ‖(Y x - M x).2‖ := norm_sub_le _ _
        _ ≤ ‖Γv‖ + ‖Y x - M x‖ := add_le_add hxΓ hsnd
        _ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖ := by linarith [hΓv_bound]
    have hbnd := christoffel_quad_diff_bound g gi p (Y x).1 v (Y x).2 Mc0 Lc0
      (fun i j k => hMc p hpmem i j k) (fun i j k => hLc (Y x).1 hyxmem i j k)
    have hP2 : ‖v‖ + ‖(Y x).2‖ ≤ (1 + C₀) * ‖v‖ := by
      have he : (1 + C₀) * ‖v‖ = ‖v‖ + C₀ * ‖v‖ := by ring
      rw [he]; linarith [hw]
    have hP4 : ‖(Y x).2‖ ^ 2 ≤ (C₀ * ‖v‖) ^ 2 := by
      have := hw; gcongr
    have step : Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
          + (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
        ≤ Acoef * ‖v‖ ^ 3 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
      have e1 : Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
          ≤ Mc * (n : ℝ) ^ 2
            * ((Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖) * ((1 + C₀) * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hvw hP2 (by positivity) (by positivity))
          (by positivity)
      have e2 : (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
          ≤ (Lc : ℝ) * (n : ℝ) ^ 2 * ((C₀ * ‖v‖) * (C₀ * ‖v‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hy1 hP4 (by positivity) (by positivity))
          (by positivity)
      calc Mc * (n : ℝ) ^ 2 * (‖v - (Y x).2‖ * (‖v‖ + ‖(Y x).2‖))
            + (Lc : ℝ) * (n : ℝ) ^ 2 * (‖(Y x).1 - p‖ * ‖(Y x).2‖ ^ 2)
          ≤ Mc * (n : ℝ) ^ 2
              * ((Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 + ‖Y x - M x‖) * ((1 + C₀) * ‖v‖))
            + (Lc : ℝ) * (n : ℝ) ^ 2 * ((C₀ * ‖v‖) * (C₀ * ‖v‖) ^ 2) := add_le_add e1 e2
        _ = Acoef * ‖v‖ ^ 3 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
            rw [hAcoefdef, hBcoefdef]; ring
    have hBle : ‖(fun i => (∑ j, ∑ k, christoffel g gi i j k p * v j * v k)
          - (∑ j, ∑ k, christoffel g gi i j k (Y x).1 * (Y x).2 j * (Y x).2 k) : Point n)‖
        ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
      have hb := hbnd.trans step
      have hexp : (1 + Bcoef * ‖v‖) * ‖Y x - M x‖
          = ‖Y x - M x‖ + Bcoef * ‖v‖ * ‖Y x - M x‖ := by ring
      rw [hexp]; linarith [hb, norm_nonneg (Y x - M x)]
    have hAle : ‖(Y x).2 - (v - x • Γv)‖
        ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 3 := by
      have hAle0 : ‖(Y x).2 - (v - x • Γv)‖ ≤ ‖Y x - M x‖ := by
        have e : (Y x).2 - (v - x • Γv) = (Y x - M x).2 := by rw [Prod.snd_sub, hMx2]
        rw [e, Prod.norm_def]; exact le_max_right _ _
      have h2' : ‖Y x - M x‖ ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ :=
        le_mul_of_one_le_left (norm_nonneg _)
          (by have := mul_nonneg hBcoef0 (norm_nonneg v); linarith)
      have h3' : 0 ≤ Acoef * ‖v‖ ^ 3 := mul_nonneg hAcoef0 (by positivity)
      linarith
    rw [hid, Prod.norm_def]
    exact max_le hAle hBle
  have h2 : gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 3) t ≤ Cfinal * ‖v‖ ^ 3 := by
    have hKpos : 0 ≤ 1 + Bcoef * ‖v‖ := by
      have := mul_nonneg hBcoef0 (norm_nonneg v); linarith
    have hAv0 : 0 ≤ Acoef * ‖v‖ ^ 3 := mul_nonneg hAcoef0 (by positivity)
    have hKle : 1 + Bcoef * ‖v‖ ≤ Kmax := by
      rw [hKmaxdef]
      have : Bcoef * ‖v‖ ≤ Bcoef * ρ := mul_le_mul_of_nonneg_left hvρ hBcoef0
      linarith
    calc gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 3) t
        ≤ Acoef * ‖v‖ ^ 3 * Real.exp (1 + Bcoef * ‖v‖) :=
          gronwallBound_zero_le_exp _ _ _ hKpos hAv0 ht.1 ht.2
      _ ≤ Acoef * ‖v‖ ^ 3 * Real.exp Kmax :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKle) hAv0
      _ = Cfinal * ‖v‖ ^ 3 := by rw [hCfinaldef]; ring
  have hg1 := (norm_le_gronwallBound_of_norm_deriv_right_le hf hf' ha bound) t ht
  rw [sub_zero] at hg1
  have hfinal : ‖Y t - M t‖ ≤ Cfinal * ‖v‖ ^ 3 := le_trans hg1 h2
  have hMt : M t = (p + t • v - (t ^ 2 / 2) • Γv, v - t • Γv) := by rw [hMdef]
  rw [← hMt]
  exact hfinal

/-! ### EXP-JET2 — the value 3-jet `exp_p(v) = p + v − ½Γ_p(v,v) + ⅙a₃(v) + o(‖v‖³)`

  One order up from EXP-JET1, by the SAME equilibrium-anchored residual-ODE + inhomogeneous-Grönwall
  technique.  The cubic coefficient is the true third radial derivative `γ'''(0)` of `t ↦ exp_p(tv)`:
  `a₃(v)_i = −∑_{j,k,l} ∂_l Γ^i_{jk}(p) v_j v_k v_l + ∑_{j,k} Γ^i_{jk}(p)(Γ_p(v,v)_j v_k + v_j Γ_p(v,v)_k)`
  (with `∂_l Γ = pd (christoffel …) l`).  This is the honest symmetry-free form; when the metric is
  symmetric (so `Γ^i_{jk} = Γ^i_{kj}`, `christoffel_symm`) the second sum equals `2∑_{j,k}
  Γ^i_{jk}(p) Γ_p(v,v)_j v_k`.

  The genuinely new analytic ingredient over EXP-JET1 is the SECOND-order Taylor remainder for the
  Christoffel symbols (`christoffel_taylor_bound`): a base-point `∂Γ`-Lipschitz bound makes the leading
  cubic terms cancel EXACTLY against `a₃`, leaving an `O(‖v‖⁴)` inhomogeneous term, hence `o(‖v‖³)`.

  HONEST CAPTION (binding): this is the Fréchet value 3-jet of `exp_p` at `0`.  It does NOT discharge
  `hgauge`, NOT build the pullback metric, NOT move numerical-G (`N`, `Λ_s`, `E/ξ` remain). -/

/-- **`fderiv` in coordinate form:** for `f : Point n → ℝ` differentiable at `x`, the Fréchet
    derivative applied to a vector `w` is the coordinate expansion `Df(x)[w] = ∑_l ∂_l f(x)·w_l`
    (each `∂_l f = pd f l`, via `pd_eq_fderiv` + linearity of `fderiv` over the standard basis). -/
theorem fderiv_apply_eq_sum_pd (f : Point n → ℝ) (x w : Point n)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x w = ∑ l, pd f l x * w l := by
  have hw : (∑ l, w l • (Pi.single l (1 : ℝ) : Point n)) = w := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq]
  calc fderiv ℝ f x w
      = fderiv ℝ f x (∑ l, w l • (Pi.single l (1 : ℝ) : Point n)) := by rw [hw]
    _ = ∑ l, w l • fderiv ℝ f x (Pi.single l 1) := by rw [map_sum]; simp_rw [map_smul]
    _ = ∑ l, pd f l x * w l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [pd_eq_fderiv f l x hf, smul_eq_mul, mul_comm]

/-- **`pd (christoffel …) l` is `C^∞`.**  `pd f l = fun y => Df(y)[eₗ]` (`pd_eq_fderiv`), and `y ↦
    Df(y)` is `C^∞` for `C^∞` `f` (`ContDiff.fderiv_right`); evaluating at the fixed basis vector `eₗ`
    is a continuous-linear application, preserving `C^∞`.  This provides the sup-norm value and
    Lipschitz bounds for the first Christoffel derivatives on a compact ball. -/
theorem christoffel_pd_contDiff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (i j k l : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => pd (fun z => christoffel g gi i j k z) l y) := by
  have he : (fun y => pd (fun z => christoffel g gi i j k z) l y)
      = (fun y => fderiv ℝ (fun z => christoffel g gi i j k z) y (Pi.single l 1)) :=
    funext fun y => pd_eq_fderiv _ l y ((hC i j k).differentiable (by simp) y)
  rw [he]
  exact (ContinuousLinearMap.apply ℝ ℝ ((Pi.single l 1 : Point n))).contDiff.comp
    ((hC i j k).fderiv_right (m := ⊤) le_top)

/-- **Second-order Taylor remainder for a Christoffel symbol.**  Writing `w = X − p`, if the first
    partials `∂_l Γ^i_{jk}` are `M2`-Lipschitz along the segment `[p, X]` (each `|∂_l Γ(p+θw) − ∂_l
    Γ(p)| ≤ M2‖θw‖` for `θ ∈ [0,1]`), then the first-order Taylor error obeys
    `|Γ^i_{jk}(X) − Γ^i_{jk}(p) − ∑_l ∂_l Γ^i_{jk}(p) w_l| ≤ M2·n·‖w‖²`.  Proof: mean-value on the
    scalar curve `φ(θ) = Γ(p+θw)` (chain rule + `fderiv_apply_eq_sum_pd`), comparing `φ(1)−φ(0)` to
    `φ'(0)` via `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`. -/
theorem christoffel_taylor_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (p X : Point n) (i j k : Fin n) {M2 : ℝ} (hM2 : 0 ≤ M2)
    (hdiff : ∀ y, DifferentiableAt ℝ (fun z => christoffel g gi i j k z) y)
    (hLip : ∀ l : Fin n, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      |pd (fun z => christoffel g gi i j k z) l (p + θ • (X - p))
        - pd (fun z => christoffel g gi i j k z) l p| ≤ M2 * ‖θ • (X - p)‖) :
    |christoffel g gi i j k X - christoffel g gi i j k p
        - ∑ l, pd (fun z => christoffel g gi i j k z) l p * (X - p) l|
      ≤ M2 * (n : ℝ) * ‖X - p‖ ^ 2 := by
  set Γf : Point n → ℝ := fun z => christoffel g gi i j k z with hΓf
  set w : Point n := X - p with hw
  set L0 : ℝ := ∑ l, pd Γf l p * w l with hL0
  -- the scalar curve `φ(θ) = Γf(p + θ w)` and its derivative.
  have hφ : ∀ θ : ℝ, HasDerivAt (fun θ' => Γf (p + θ' • w))
      (∑ l, pd Γf l (p + θ • w) * w l) θ := by
    intro θ
    have hid : HasDerivAt (fun θ' : ℝ => θ' • w) w θ := by
      simpa using (hasDerivAt_id θ).smul_const w
    have hcurve : HasDerivAt (fun θ' : ℝ => p + θ' • w) w θ := hid.const_add p
    have hcomp := (hdiff (p + θ • w)).hasFDerivAt.comp_hasDerivAt θ hcurve
    rw [fderiv_apply_eq_sum_pd Γf (p + θ • w) w (hdiff (p + θ • w))] at hcomp
    exact hcomp
  -- `ψ(θ) = φ(θ) − φ(0) − θ·φ'(0)`, with `ψ(0) = 0` and derivative `φ'(θ) − φ'(0)`.
  set ψ : ℝ → ℝ := fun θ => Γf (p + θ • w) - Γf p - θ * L0 with hψ
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hψderiv : ∀ θ : ℝ, HasDerivAt ψ ((∑ l, pd Γf l (p + θ • w) * w l) - L0) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ' => Γf (p + θ' • w) - Γf p)
        (∑ l, pd Γf l (p + θ • w) * w l) θ := (hφ θ).sub_const _
    have h2 : HasDerivAt (fun θ' : ℝ => θ' * L0) L0 θ := by
      simpa using (hasDerivAt_id θ).mul_const L0
    exact h1.sub h2
  -- the derivative bound on `[0,1]`.
  have hbd : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖(∑ l, pd Γf l (p + θ • w) * w l) - L0‖ ≤ M2 * (n : ℝ) * ‖w‖ ^ 2 := by
    intro θ hθ
    rw [hL0, ← Finset.sum_sub_distrib]
    have hθw : ‖θ • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ = ‖w‖ := one_mul _
    have hterm : ∀ l : Fin n,
        |pd Γf l (p + θ • w) * w l - pd Γf l p * w l| ≤ M2 * ‖w‖ * ‖w‖ := by
      intro l
      rw [← sub_mul, abs_mul]
      have ha : |pd Γf l (p + θ • w) - pd Γf l p| ≤ M2 * ‖w‖ :=
        (hLip l θ hθ).trans (mul_le_mul_of_nonneg_left hθw hM2)
      have hb : |w l| ≤ ‖w‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w l
      exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs]
    calc |∑ l, (pd Γf l (p + θ • w) * w l - pd Γf l p * w l)|
        ≤ ∑ l, |pd Γf l (p + θ • w) * w l - pd Γf l p * w l| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin n, M2 * ‖w‖ * ‖w‖ := Finset.sum_le_sum fun l _ => hterm l
      _ = M2 * (n : ℝ) * ‖w‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- mean-value: `‖ψ 1 − ψ 0‖ ≤ (M2 n ‖w‖²)·‖1 − 0‖`.
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := ψ) (f' := fun θ => (∑ l, pd Γf l (p + θ • w) * w l) - L0)
    (s := Set.Icc (0 : ℝ) 1) (C := M2 * (n : ℝ) * ‖w‖ ^ 2) (x := 0) (y := 1)
    (fun θ hθ => (hψderiv θ).hasDerivWithinAt) hbd (convex_Icc 0 1)
    (by simp) (by simp)
  rw [hψ0, sub_zero] at hmvt
  have hψ1 : ψ 1 = Γf X - Γf p - L0 := by
    show Γf (p + (1 : ℝ) • w) - Γf p - (1 : ℝ) * L0 = Γf X - Γf p - L0
    rw [show p + (1 : ℝ) • w = X by rw [hw, one_smul]; abel, one_mul]
  rw [hψ1] at hmvt
  calc |christoffel g gi i j k X - christoffel g gi i j k p - L0|
      = ‖Γf X - Γf p - L0‖ := (Real.norm_eq_abs _).symm
    _ ≤ M2 * (n : ℝ) * ‖w‖ ^ 2 * ‖(1 : ℝ) - 0‖ := hmvt
    _ = M2 * (n : ℝ) * ‖X - p‖ ^ 2 := by rw [hw]; norm_num

/-- **Sup-norm bound for a `pd`-Christoffel trilinear form.**  If `|∂_l Γ^i_{jk}(p)| ≤ Nc`, then
    `‖(fun i => ∑_{j,k,l} ∂_l Γ^i_{jk}(p)·a_j·b_k·c_l)‖ ≤ Nc·n³·‖a‖·‖b‖·‖c‖`.  The trilinear analogue
    of `christoffel_bilin_bound`, used to control the first-order Taylor terms of `Γ`. -/
theorem christoffel_pd_trilin_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (p a b c : Point n) {Nc : ℝ} (hNc0 : 0 ≤ Nc)
    (hNc : ∀ i j k l, |pd (fun z => christoffel g gi i j k z) l p| ≤ Nc) :
    ‖(fun i => ∑ j, ∑ k, ∑ l,
        pd (fun z => christoffel g gi i j k z) l p * a j * b k * c l : Point n)‖
      ≤ Nc * (n : ℝ) ^ 3 * (‖a‖ * ‖b‖ * ‖c‖) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Real.norm_eq_abs]
  have hterm : ∀ j k l : Fin n,
      |pd (fun z => christoffel g gi i j k z) l p * a j * b k * c l|
        ≤ Nc * (‖a‖ * ‖b‖ * ‖c‖) := by
    intro j k l
    rw [abs_mul, abs_mul, abs_mul]
    have h1 : |pd (fun z => christoffel g gi i j k z) l p| ≤ Nc := hNc i j k l
    have h2 : |a j| ≤ ‖a‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a j
    have h3 : |b k| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k
    have h4 : |c l| ≤ ‖c‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c l
    calc |pd (fun z => christoffel g gi i j k z) l p| * |a j| * |b k| * |c l|
        ≤ Nc * ‖a‖ * ‖b‖ * ‖c‖ :=
          mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hNc0) h3 (abs_nonneg _)
            (by positivity)) h4 (abs_nonneg _) (by positivity)
      _ = Nc * (‖a‖ * ‖b‖ * ‖c‖) := by ring
  calc |∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * a j * b k * c l|
      ≤ ∑ j, |∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * a j * b k * c l| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, Nc * (‖a‖ * ‖b‖ * ‖c‖) :=
        Finset.sum_le_sum fun j _ =>
          (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
            (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hterm j k l))
    _ = Nc * (n : ℝ) ^ 3 * (‖a‖ * ‖b‖ * ‖c‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Generic sup-norm bound for a bilinear form.**  For any coefficient array `F : Fin n → Fin n →
    Fin n → ℝ` with `|F i j k| ≤ Mc`, the form `∑_{j,k} F i j k · a_j · b_k` obeys `‖·‖ ≤ Mc·n²·‖a‖·‖b‖`.
    Generalises `christoffel_bilin_bound` to an arbitrary base-point Christoffel array or Taylor
    remainder. -/
theorem bilin_sup_bound (F : Fin n → Fin n → Fin n → ℝ) (a b : Point n) {Mc : ℝ} (hMc0 : 0 ≤ Mc)
    (hMc : ∀ i j k, |F i j k| ≤ Mc) :
    ‖(fun i => ∑ j, ∑ k, F i j k * a j * b k : Point n)‖ ≤ Mc * (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp only [Real.norm_eq_abs]
  have hterm : ∀ j k : Fin n, |F i j k * a j * b k| ≤ Mc * (‖a‖ * ‖b‖) := by
    intro j k
    rw [abs_mul, abs_mul]
    have h1 : |F i j k| ≤ Mc := hMc i j k
    have h2 : |a j| ≤ ‖a‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a j
    have h3 : |b k| ≤ ‖b‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k
    calc |F i j k| * |a j| * |b k|
        ≤ Mc * ‖a‖ * ‖b‖ :=
          mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hMc0) h3 (abs_nonneg _) (by positivity)
      _ = Mc * (‖a‖ * ‖b‖) := by ring
  calc |∑ j, ∑ k, F i j k * a j * b k|
      ≤ ∑ j, |∑ k, F i j k * a j * b k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, Mc * (‖a‖ * ‖b‖) :=
        Finset.sum_le_sum fun j _ =>
          (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
    _ = Mc * (n : ℝ) ^ 2 * (‖a‖ * ‖b‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The EXP-JET2 model curve's derivative.**  The explicit cubic model
    `M(τ) = (p + τ·v − ½τ²·Γv + ⅙τ³·a₃, v − τ·Γv + ½τ²·a₃)` has velocity
    `M'(τ) = (v − τ·Γv + ½τ²·a₃, −Γv + τ·a₃)`.  Pure calculus (position component differentiates to
    the velocity component); the seed for the residual ODE `r₃' = A·r₃ + Err`. -/
theorem expJet2_model_hasDerivAt (p v Γv a3 : Point n) (t : ℝ) :
    HasDerivAt (fun τ : ℝ =>
        ((p + τ • v - (τ ^ 2 / 2) • Γv + (τ ^ 3 / 6) • a3,
          v - τ • Γv + (τ ^ 2 / 2) • a3) : Point n × Point n))
      ((v - t • Γv + (t ^ 2 / 2) • a3, -Γv + t • a3) : Point n × Point n) t := by
  have hc1 : HasDerivAt (fun τ : ℝ => p + τ • v - (τ ^ 2 / 2) • Γv + (τ ^ 3 / 6) • a3)
      (v - t • Γv + (t ^ 2 / 2) • a3) t := by
    have hp : HasDerivAt (fun _ : ℝ => p) (0 : Point n) t := hasDerivAt_const t p
    have hv1 : HasDerivAt (fun τ : ℝ => τ • v) v t := by simpa using (hasDerivAt_id t).smul_const v
    have hsq : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; norm_num
    have hquad : HasDerivAt (fun τ : ℝ => (τ ^ 2 / 2) • Γv) (t • Γv) t := hsq.smul_const Γv
    have hcub0 : HasDerivAt (fun τ : ℝ => τ ^ 3 / 6) (t ^ 2 / 2) t := by
      convert (hasDerivAt_pow 3 t).div_const 6 using 1; norm_num; ring
    have hcub : HasDerivAt (fun τ : ℝ => (τ ^ 3 / 6) • a3) ((t ^ 2 / 2) • a3) t :=
      hcub0.smul_const a3
    have := ((hp.add hv1).sub hquad).add hcub
    simpa using this
  have hc2 : HasDerivAt (fun τ : ℝ => v - τ • Γv + (τ ^ 2 / 2) • a3) (-Γv + t • a3) t := by
    have hvc : HasDerivAt (fun _ : ℝ => v) (0 : Point n) t := hasDerivAt_const t v
    have hτΓ : HasDerivAt (fun τ : ℝ => τ • Γv) Γv t := by
      simpa using (hasDerivAt_id t).smul_const Γv
    have hsq : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
      convert (hasDerivAt_pow 2 t).div_const 2 using 1; norm_num
    have hquad : HasDerivAt (fun τ : ℝ => (τ ^ 2 / 2) • a3) (t • a3) t := hsq.smul_const a3
    have := (hvc.sub hτΓ).add hquad
    simpa using this
  exact hc1.prodMk hc2

/-- **The EXP-JET2 residual ODE identity.**  For any curve `Y`, the difference between the geodesic
    field at `Y t` and the model velocity `M'(t) = (v − t·Γv + ½t²·a₃, −Γv + t·a₃)` is
    `((Y t).2 − M₂(t), Γv − t·a₃ − Γ_{(Y t).1}((Y t).2,(Y t).2))`.  This is `r₃'(t) = A·r₃ + Err` in
    explicit form: the first (velocity-transport `A`) component is the residual velocity `(r₃).2`, and
    the second component is the inhomogeneous `Err(t)`.  Pure algebra of `geodesicField`. -/
theorem expJet2_residual_deriv_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (Y : ℝ → Point n × Point n) (Γv a3 v : Point n) (t : ℝ) :
    geodesicField g gi (Y t)
        - ((v - t • Γv + (t ^ 2 / 2) • a3, -Γv + t • a3) : Point n × Point n)
      = ((Y t).2 - (v - t • Γv + (t ^ 2 / 2) • a3),
          Γv - t • a3
            - (fun i => ∑ j, ∑ k, christoffel g gi i j k (Y t).1 * (Y t).2 j * (Y t).2 k)) := by
  refine Prod.ext ?_ ?_
  · simp [geodesicField]
  · funext i
    simp only [geodesicField, Prod.snd_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul]
    ring

/-- **Bilinear expansion of `Γ(v − x·w, v − x·w)`.**  For any coefficient array `F`, the quadratic
    form at the shifted argument `v − x·w` expands to `Γ(v,v) − x·Γ(v,w) − x·Γ(w,v) + x²·Γ(w,w)`.
    A pure `Finset` distribution identity (per-component `ring` after splitting the double sum). -/
theorem bilin_sub_smul_expand (F : Fin n → Fin n → Fin n → ℝ) (v w : Point n) (x : ℝ) :
    (fun i => ∑ j, ∑ k, F i j k * (v - x • w) j * (v - x • w) k : Point n)
      = (fun i => ∑ j, ∑ k, F i j k * v j * v k)
        - x • (fun i => ∑ j, ∑ k, F i j k * v j * w k)
        - x • (fun i => ∑ j, ∑ k, F i j k * w j * v k)
        + x ^ 2 • (fun i => ∑ j, ∑ k, F i j k * w j * w k) := by
  funext i
  show (∑ j, ∑ k, F i j k * (v - x • w) j * (v - x • w) k)
     = (∑ j, ∑ k, F i j k * v j * v k)
        - x * (∑ j, ∑ k, F i j k * v j * w k)
        - x * (∑ j, ∑ k, F i j k * w j * v k)
        + x ^ 2 * (∑ j, ∑ k, F i j k * w j * w k)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Trilinear telescoping with a shared coefficient array `P`.**  The difference
    `x·P(v,v,v) − P(u,u,d)` splits as `P(v,v,x·v − d) + P(v − u, v, d) + P(u, v − u, d)`.  A pure
    `Finset` identity (per-component `ring` after merging the triple sums). -/
theorem tri_shared_telescope (P : Fin n → Fin n → Fin n → Fin n → ℝ) (v u d : Point n) (x : ℝ) :
    (fun i => x * (∑ j, ∑ k, ∑ l, P i j k l * v j * v k * v l)
            - (∑ j, ∑ k, ∑ l, P i j k l * u j * u k * d l) : Point n)
      = (fun i => ∑ j, ∑ k, ∑ l, P i j k l * v j * v k * ((x • v - d) l))
        + (fun i => ∑ j, ∑ k, ∑ l, P i j k l * (v - u) j * v k * d l)
        + (fun i => ∑ j, ∑ k, ∑ l, P i j k l * u j * (v - u) k * d l) := by
  funext i
  show x * (∑ j, ∑ k, ∑ l, P i j k l * v j * v k * v l)
        - (∑ j, ∑ k, ∑ l, P i j k l * u j * u k * d l)
      = (∑ j, ∑ k, ∑ l, P i j k l * v j * v k * ((x • v - d) l))
        + (∑ j, ∑ k, ∑ l, P i j k l * (v - u) j * v k * d l)
        + (∑ j, ∑ k, ∑ l, P i j k l * u j * (v - u) k * d l)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Repackaging the second-order Taylor remainder of a quadratic form.**  With `Q`, `F` two
    coefficient arrays and `P` a first-derivative array, the vector
    `Q(u,u) − F(u,u) − ∑_l P(u,u,·)·d_l` equals the quadratic form of the per-entry remainder
    `Q i j k − F i j k − ∑_l P i j k l · d_l`.  This puts the Christoffel Taylor remainder in the
    `bilin_sup_bound`-ready shape.  Pure `Finset` distribution. -/
theorem bilin_taylor_repack (Q F : Fin n → Fin n → Fin n → ℝ)
    (P : Fin n → Fin n → Fin n → Fin n → ℝ) (u d : Point n) :
    (fun i => (∑ j, ∑ k, Q i j k * u j * u k)
            - (∑ j, ∑ k, F i j k * u j * u k)
            - (∑ j, ∑ k, ∑ l, P i j k l * u j * u k * d l) : Point n)
      = (fun i => ∑ j, ∑ k, (Q i j k - F i j k - ∑ l, P i j k l * d l) * u j * u k) := by
  funext i
  show (∑ j, ∑ k, Q i j k * u j * u k)
        - (∑ j, ∑ k, F i j k * u j * u k)
        - (∑ j, ∑ k, ∑ l, P i j k l * u j * u k * d l)
      = ∑ j, ∑ k, (Q i j k - F i j k - ∑ l, P i j k l * d l) * u j * u k
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hkey : (∑ l, P i j k l * d l) * u j * u k = ∑ l, P i j k l * u j * u k * d l := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [← hkey]; ring

set_option maxHeartbeats 6400000 in
/-- **EXP-JET2 — the value 3-jet of the exponential map at `0`.**
    `exp_p(v) = p + v − ½Γ_p(v,v) + ⅙a₃(v) + o(‖v‖³)`, with the symmetry-free cubic coefficient
    `a₃(v)_i = −∑_{jkl} ∂_l Γ^i_{jk}(p) v_j v_k v_l + ∑_{jk} Γ^i_{jk}(p)(Γ_p(v,v)_j v_k + v_j Γ_p(v,v)_k)`.

    Same equilibrium-anchored residual-ODE + inhomogeneous-Grönwall technique as EXP-JET1, one order
    up: the geodesic tube `Y = expTube p v` is compared to the cubic model curve
    `M(t) = (p + t·v − ½t²·Γ_p(v,v) + ⅙t³·a₃, v − t·Γ_p(v,v) + ½t²·a₃)`.  The residual `r₃ = Y − M`
    solves `r₃' = A·r₃ + Err` with `Err = Γ_p(v,v) − t·a₃ − Γ_{(Y t).1}((Y t).2,(Y t).2)`, and the
    telescope `Err = [−t²·Γ_p(Γv,Γv)] + [t·D(v,v,v) − D(u*,u*,X−p)] − Rem + [Γ_X(u*,u*) − Γ_X(U,U)]`
    (with `u* = v − t·Γv`, `X = (Y t).1`, `U = (Y t).2`, `D = ∂Γ_p`, `Rem` the second-order Christoffel
    Taylor remainder) makes the leading cubic terms cancel EXACTLY against `a₃`, leaving
    `‖Err(t)‖ ≤ Acoef·‖v‖⁴ + Bcoef·‖v‖·‖r₃ t‖`.  The inhomogeneous Grönwall then gives
    `‖r₃ 1‖ ≤ Cfinal·‖v‖⁴`, and projecting the position component closes the `o(‖v‖³)`.

    HONEST CAPTION (binding): this is the Fréchet value 3-jet of `exp_p` at `0`.  It does NOT discharge
    `hgauge`, NOT build the pullback metric, NOT move numerical-G (`N`, `Λ_s`, `E/ξ` remain). -/
theorem expMap_value_three_jet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    (fun v => expMap g gi hC p v - p - v
        + (1 / 2 : ℝ) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)
        - (1 / 6 : ℝ) • (fun i =>
            -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
            + (∑ j, ∑ k, christoffel g gi i j k p
                  * (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) * v k)
            + (∑ j, ∑ k, christoffel g gi i j k p
                  * v j * (∑ a, ∑ b, christoffel g gi k a b p * v a * v b)) : Point n))
      =o[𝓝 (0 : Point n)] (fun v => ‖v‖ ^ 3) := by
  have hρpos := expRho_pos g gi hC p
  have hC₀ := expConst_nonneg g gi hC p
  set ρ : ℝ := expRho g gi hC p with hρ
  set C₀ : ℝ := expConst g gi hC p with hC₀def
  set R : ℝ := C₀ * ρ with hRdef
  have hR0 : 0 ≤ R := mul_nonneg hC₀ hρpos.le
  have hpmem : p ∈ Metric.closedBall p R := Metric.mem_closedBall_self hR0
  -- Christoffel value bound `Mc` on `closedBall p R`.
  set T : Point n → (Fin n → Fin n → Fin n → ℝ) :=
    fun y => (fun i j k => christoffel g gi i j k y) with hTdef
  have hTcd : ContDiff ℝ (⊤ : WithTop ℕ∞) T :=
    contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => contDiff_pi.mpr fun k => hC i j k
  obtain ⟨Mc, hMcsub⟩ :=
    (((isCompact_closedBall p R).image_of_continuousOn
      hTcd.continuous.continuousOn).isBounded).subset_closedBall (0 : Fin n → Fin n → Fin n → ℝ)
  have hMc : ∀ y ∈ Metric.closedBall p R, ∀ i j k, |christoffel g gi i j k y| ≤ Mc := by
    intro y hy i j k
    have hTy : ‖T y‖ ≤ Mc := by
      have := hMcsub (Set.mem_image_of_mem T hy)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have e : christoffel g gi i j k y = T y i j k := by simp only [hTdef]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (T y i j) k).trans
      ((norm_le_pi_norm (T y i) j).trans (norm_le_pi_norm (T y) i))).trans hTy
  have Mc0 : 0 ≤ Mc := le_trans (norm_nonneg _) (by
    have := hMcsub (Set.mem_image_of_mem T hpmem)
    rwa [Metric.mem_closedBall, dist_zero_right] at this)
  -- First-derivative Christoffel value bound `Nc` at `p`.
  set PDp : (Fin n → Fin n → Fin n → Fin n → ℝ) :=
    fun i j k l => pd (fun z => christoffel g gi i j k z) l p with hPDpdef
  set Nc : ℝ := ‖PDp‖ with hNcdef
  have Nc0 : 0 ≤ Nc := norm_nonneg _
  have hNc : ∀ i j k l, |pd (fun z => christoffel g gi i j k z) l p| ≤ Nc := by
    intro i j k l
    have e : pd (fun z => christoffel g gi i j k z) l p = PDp i j k l := by simp only [hPDpdef]
    rw [e, hNcdef, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm (PDp i j k) l).trans
      ((norm_le_pi_norm (PDp i j) k).trans
        ((norm_le_pi_norm (PDp i) j).trans (norm_le_pi_norm PDp i))))
  -- First-derivative Christoffel Lipschitz bound `M2` on `closedBall p R`.
  set PD : Point n → (Fin n → Fin n → Fin n → Fin n → ℝ) :=
    fun y => (fun i j k l => pd (fun z => christoffel g gi i j k z) l y) with hPDdef
  have hPDcd : ContDiff ℝ (⊤ : WithTop ℕ∞) PD :=
    contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => contDiff_pi.mpr fun k =>
      contDiff_pi.mpr fun l => christoffel_pd_contDiff g gi hC i j k l
  obtain ⟨M2, hM2lip⟩ :=
    (hPDcd.contDiffOn (s := Metric.closedBall p R)).exists_lipschitzOnWith (by simp)
      (convex_closedBall p R) (isCompact_closedBall p R)
  have M20 : 0 ≤ (M2 : ℝ) := M2.coe_nonneg
  have hM2 : ∀ a ∈ Metric.closedBall p R, ∀ b ∈ Metric.closedBall p R, ∀ i j k l,
      |pd (fun z => christoffel g gi i j k z) l a - pd (fun z => christoffel g gi i j k z) l b|
        ≤ (M2 : ℝ) * ‖a - b‖ := by
    intro a ha b hb i j k l
    have hd := hM2lip.dist_le_mul a ha b hb
    rw [dist_eq_norm, dist_eq_norm] at hd
    have e : pd (fun z => christoffel g gi i j k z) l a - pd (fun z => christoffel g gi i j k z) l b
        = (PD a - PD b) i j k l := by simp only [hPDdef, Pi.sub_apply]
    rw [e, ← Real.norm_eq_abs]
    exact ((norm_le_pi_norm ((PD a - PD b) i j k) l).trans
      ((norm_le_pi_norm ((PD a - PD b) i j) k).trans
        ((norm_le_pi_norm ((PD a - PD b) i) j).trans
          (norm_le_pi_norm (PD a - PD b) i)))).trans hd
  -- Derived constants.
  set Cu : ℝ := 1 + Mc * (n : ℝ) ^ 2 * ρ with hCudef
  set Pc : ℝ := Mc * (n : ℝ) ^ 2 * C₀ ^ 2 with hPcdef
  set A3c : ℝ := Nc * (n : ℝ) ^ 3 + 2 * Mc ^ 2 * (n : ℝ) ^ 4 with hA3cdef
  set Bcoef : ℝ := Mc * (n : ℝ) ^ 2 * (Cu + C₀) with hBcoefdef
  set Acoef : ℝ := Nc * (n : ℝ) ^ 3 * Pc + Nc * Mc * C₀ * (n : ℝ) ^ 5
      + Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5 + Mc ^ 3 * (n : ℝ) ^ 6
      + M2 * (n : ℝ) ^ 3 * C₀ ^ 2 * Cu ^ 2
      + (1 / 2 : ℝ) * Mc * (n : ℝ) ^ 2 * (Cu + C₀) * A3c with hAcoefdef
  have hn : ∀ k : ℕ, (0 : ℝ) ≤ (n : ℝ) ^ k := fun k => by positivity
  have hCu0 : 0 ≤ Cu := by
    rw [hCudef]; exact add_nonneg (by norm_num) (mul_nonneg (mul_nonneg Mc0 (hn 2)) hρpos.le)
  have hPc0 : 0 ≤ Pc := by
    rw [hPcdef]; exact mul_nonneg (mul_nonneg Mc0 (hn 2)) (sq_nonneg _)
  have hA3c0 : 0 ≤ A3c := by
    rw [hA3cdef]
    exact add_nonneg (mul_nonneg Nc0 (hn 3))
      (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg Mc0 2)) (hn 4))
  have hBcoef0 : 0 ≤ Bcoef := by
    rw [hBcoefdef]; exact mul_nonneg (mul_nonneg Mc0 (hn 2)) (add_nonneg hCu0 hC₀)
  have hAcoef0 : 0 ≤ Acoef := by
    rw [hAcoefdef]
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_) ?_
    · exact mul_nonneg (mul_nonneg Nc0 (hn 3)) hPc0
    · exact mul_nonneg (mul_nonneg (mul_nonneg Nc0 Mc0) hC₀) (hn 5)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Nc0 hCu0) Mc0) hC₀) (hn 5)
    · exact mul_nonneg (pow_nonneg Mc0 3) (hn 6)
    · exact mul_nonneg (mul_nonneg (mul_nonneg M20 (hn 3)) (sq_nonneg _)) (sq_nonneg _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Mc0) (hn 2))
        (add_nonneg hCu0 hC₀)) hA3c0
  set Kmax : ℝ := 1 + Bcoef * ρ with hKmaxdef
  set Cfinal : ℝ := Acoef * Real.exp Kmax with hCfinaldef
  have hCfinal0 : 0 ≤ Cfinal := by rw [hCfinaldef]; exact mul_nonneg hAcoef0 (Real.exp_pos _).le
  -- The core `O(‖v‖⁴)` bound for `‖v‖ ≤ ρ`.
  have hbound : ∀ v : Point n, ‖v‖ ≤ ρ →
      ‖expMap g gi hC p v - p - v
          + (1 / 2 : ℝ) • (fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k : Point n)
          - (1 / 6 : ℝ) • (fun i =>
              -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
              + (∑ j, ∑ k, christoffel g gi i j k p
                    * (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) * v k)
              + (∑ j, ∑ k, christoffel g gi i j k p
                    * v j * (∑ a, ∑ b, christoffel g gi k a b p * v a * v b)) : Point n)‖
        ≤ Cfinal * ‖v‖ ^ 4 := by
    intro v hvρ
    obtain ⟨hY0, hYd, hYconf⟩ := expTube_spec g gi hC p v hvρ
    set Y : ℝ → Point n × Point n := expTube g gi hC p v with hYdef
    set Γv : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * v k with hΓvdef
    set a3 : Point n := fun i =>
        -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) * v k)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * v j * (∑ a, ∑ b, christoffel g gi k a b p * v a * v b)) with ha3def
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hGvj : ∀ j : Fin n, (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) = Γv j := by
      intro j; rw [hΓvdef]
    -- Christoffel quadratic-form value bound (base `p`).
    have hΓv_bound : ‖Γv‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
      have h := christoffel_bilin_bound g gi p v v Mc0 (fun i j k => hMc p hpmem i j k)
      calc ‖Γv‖ ≤ Mc * (n : ℝ) ^ 2 * (‖v‖ * ‖v‖) := h
        _ = Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by ring
    -- The cubic model curve and its derivative.
    set M : ℝ → Point n × Point n :=
      fun τ => (p + τ • v - (τ ^ 2 / 2) • Γv + (τ ^ 3 / 6) • a3,
                v - τ • Γv + (τ ^ 2 / 2) • a3) with hMdef
    have hM : ∀ t : ℝ,
        HasDerivAt M ((v - t • Γv + (t ^ 2 / 2) • a3, -Γv + t • a3) : Point n × Point n) t := by
      intro t; rw [hMdef]; exact expJet2_model_hasDerivAt p v Γv a3 t
    -- a-priori confinement + tube first-order (velocity / position) bounds.
    have hvel_tube : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖(Y s).2 - v‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by
      have hfd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun τ => (Y τ).2) ((geodesicField g gi (Y t)).2) t := fun t ht =>
        (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t
          (hYd t (hIcc_Ioo t ht))
      have hf'bd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖(geodesicField g gi (Y t)).2‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by
        intro t ht
        have hconf := hYconf t ht
        have hw : ‖(Y t).2‖ ≤ C₀ * ‖v‖ := by
          have e : (Y t).2 = (Y t - ((p, 0) : Point n × Point n)).2 := by simp [Prod.snd_sub]
          rw [e]; exact le_trans (by rw [Prod.norm_def]; exact le_max_right _ _) hconf
        have hymem : (Y t).1 ∈ Metric.closedBall p R := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have e : (Y t).1 - p = (Y t - ((p, 0) : Point n × Point n)).1 := by simp [Prod.fst_sub]
          calc ‖(Y t).1 - p‖ ≤ C₀ * ‖v‖ := by
                rw [e]; exact le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) hconf
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀
            _ = R := by rw [hRdef]
        have he : (geodesicField g gi (Y t)).2
            = -(fun i => ∑ j, ∑ k, christoffel g gi i j k (Y t).1 * (Y t).2 j * (Y t).2 k
                : Point n) := by
          funext i; simp [geodesicField]
        rw [he, norm_neg]
        calc ‖(fun i => ∑ j, ∑ k, christoffel g gi i j k (Y t).1 * (Y t).2 j * (Y t).2 k : Point n)‖
            ≤ Mc * (n : ℝ) ^ 2 * (‖(Y t).2‖ * ‖(Y t).2‖) :=
              bilin_sup_bound (fun i j k => christoffel g gi i j k (Y t).1) (Y t).2 (Y t).2 Mc0
                (fun i j k => hMc (Y t).1 hymem i j k)
          _ ≤ Mc * (n : ℝ) ^ 2 * (C₀ * ‖v‖ * (C₀ * ‖v‖)) := by
              gcongr
          _ = Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by ring
      intro s hs
      have hres : ‖(Y s).2 - (Y (0 : ℝ)).2‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * ‖s - 0‖ :=
        Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun τ => (Y τ).2) (f' := fun t => (geodesicField g gi (Y t)).2)
          (s := Set.Icc (0 : ℝ) 1) (C := Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2) (x := 0) (y := s)
          (fun t ht => (hfd t ht).hasDerivWithinAt) hf'bd (convex_Icc 0 1) (by simp) hs
      have hY02 : (Y (0 : ℝ)).2 = v := by rw [hY0]
      rw [hY02] at hres
      calc ‖(Y s).2 - v‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * ‖s - 0‖ := hres
        _ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * 1 := by
            gcongr
            rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1]; exact hs.2
        _ = Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by ring
    have hpos_tube : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖(Y s).1 - p - s • v‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by
      have hfd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (fun τ => (Y τ).1 - τ • v) ((Y t).2 - v) t := by
        intro t ht
        have h1 : HasDerivAt (fun τ => (Y τ).1) ((geodesicField g gi (Y t)).1) t :=
          (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t
            (hYd t (hIcc_Ioo t ht))
        have h2 : HasDerivAt (fun τ : ℝ => τ • v) v t := by
          simpa using (hasDerivAt_id t).smul_const v
        have h3 := h1.sub h2
        have he : (geodesicField g gi (Y t)).1 = (Y t).2 := rfl
        rwa [he] at h3
      intro s hs
      have hres : ‖((Y s).1 - s • v) - ((Y (0 : ℝ)).1 - (0 : ℝ) • v)‖
          ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * ‖s - 0‖ :=
        Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun τ => (Y τ).1 - τ • v) (f' := fun t => (Y t).2 - v)
          (s := Set.Icc (0 : ℝ) 1) (C := Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2) (x := 0) (y := s)
          (fun t ht => (hfd t ht).hasDerivWithinAt) hvel_tube (convex_Icc 0 1) (by simp) hs
      have hf0 : (Y (0 : ℝ)).1 - (0 : ℝ) • v = p := by rw [hY0]; simp
      rw [hf0] at hres
      have heq : (Y s).1 - s • v - p = (Y s).1 - p - s • v := by abel
      rw [← heq]
      calc ‖(Y s).1 - s • v - p‖ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * ‖s - 0‖ := hres
        _ ≤ Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 * 1 := by
            gcongr
            rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1]; exact hs.2
        _ = Mc * (n : ℝ) ^ 2 * C₀ ^ 2 * ‖v‖ ^ 2 := by ring
    -- The residual `q = Y − M` derivative data.
    have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun τ => Y τ - M τ)
          (geodesicField g gi (Y t)
            - ((v - t • Γv + (t ^ 2 / 2) • a3, -Γv + t • a3) : Point n × Point n)) t :=
      fun t ht => (hYd t (hIcc_Ioo t ht)).sub (hM t)
    have hf : ContinuousOn (fun τ => Y τ - M τ) (Set.Icc (0 : ℝ) 1) :=
      fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt
    have hf' : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt (fun τ => Y τ - M τ)
        (geodesicField g gi (Y x)
          - ((v - x • Γv + (x ^ 2 / 2) • a3, -Γv + x • a3) : Point n × Point n)) (Set.Ici x) x :=
      fun x hx => (hfderiv x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt
    have ha : ‖(fun τ => Y τ - M τ) 0‖ ≤ 0 := by
      show ‖Y 0 - M 0‖ ≤ 0
      have hM0 : M 0 = (p, v) := by
        show (p + (0 : ℝ) • v - ((0 : ℝ) ^ 2 / 2) • Γv + ((0 : ℝ) ^ 3 / 6) • a3,
              v - (0 : ℝ) • Γv + ((0 : ℝ) ^ 2 / 2) • a3) = (p, v)
        simp
      rw [hY0, hM0, sub_self, norm_zero]
    -- The crux: the inhomogeneous bound on the residual derivative.
    have bound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        ‖geodesicField g gi (Y x)
            - ((v - x • Γv + (x ^ 2 / 2) • a3, -Γv + x • a3) : Point n × Point n)‖
          ≤ (1 + Bcoef * ‖v‖) * ‖Y x - M x‖ + Acoef * ‖v‖ ^ 4 := by
      intro x hx
      have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      have hx0 : (0 : ℝ) ≤ x := hx.1
      have hx1 : x < 1 := hx.2
      have hxle1 : x ≤ 1 := hx1.le
      have hconf := hYconf x hxIcc
      set X : Point n := (Y x).1 with hXdef
      set U : Point n := (Y x).2 with hUdef
      set ustar : Point n := v - x • Γv with hustardef
      have hUC0 : ‖U‖ ≤ C₀ * ‖v‖ := by
        have e : U = (Y x - ((p, 0) : Point n × Point n)).2 := by rw [hUdef]; simp [Prod.snd_sub]
        rw [e]; exact le_trans (by rw [Prod.norm_def]; exact le_max_right _ _) hconf
      have hXpC0 : ‖X - p‖ ≤ C₀ * ‖v‖ := by
        have e : X - p = (Y x - ((p, 0) : Point n × Point n)).1 := by rw [hXdef]; simp [Prod.fst_sub]
        rw [e]; exact le_trans (by rw [Prod.norm_def]; exact le_max_left _ _) hconf
      have hXmem : X ∈ Metric.closedBall p R := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖X - p‖ ≤ C₀ * ‖v‖ := hXpC0
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀
          _ = R := by rw [hRdef]
      have hustar_bd : ‖ustar‖ ≤ Cu * ‖v‖ := by
        rw [hustardef]
        have hxΓ : ‖x • Γv‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
          calc x * ‖Γv‖ ≤ 1 * ‖Γv‖ := mul_le_mul_of_nonneg_right hxle1 (norm_nonneg _)
            _ = ‖Γv‖ := one_mul _
            _ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := hΓv_bound
        calc ‖v - x • Γv‖ ≤ ‖v‖ + ‖x • Γv‖ := norm_sub_le _ _
          _ ≤ ‖v‖ + Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by linarith [hxΓ]
          _ ≤ Cu * ‖v‖ := by
              rw [hCudef, add_mul, one_mul]
              have hvv : ‖v‖ ^ 2 ≤ ρ * ‖v‖ := by
                rw [sq]; exact mul_le_mul_of_nonneg_right hvρ (norm_nonneg _)
              have hco : (0 : ℝ) ≤ Mc * (n : ℝ) ^ 2 := mul_nonneg Mc0 (hn 2)
              nlinarith [mul_le_mul_of_nonneg_left hvv hco]
      have hMx2 : (M x).2 = v - x • Γv + (x ^ 2 / 2) • a3 := by rw [hMdef]
      -- the analysis vectors.
      set GXUU : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k X * U j * U k with hGXUUdef
      set GXuu : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k X * ustar j * ustar k
        with hGXuudef
      set GPuu : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * ustar j * ustar k
        with hGPuudef
      set Dvvv : Point n :=
        fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l
        with hDvvvdef
      set BGv : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * Γv j * v k with hBGvdef
      set BvG : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * v j * Γv k with hBvGdef
      set BGG : Point n := fun i => ∑ j, ∑ k, christoffel g gi i j k p * Γv j * Γv k with hBGGdef
      set Dstar : Point n :=
        fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * ustar j * ustar k
          * (X - p) l with hDstardef
      set Rrem : Point n :=
        fun i => ∑ j, ∑ k, (christoffel g gi i j k X - christoffel g gi i j k p
          - ∑ l, pd (fun z => christoffel g gi i j k z) l p * (X - p) l) * ustar j * ustar k
        with hRremdef
      -- the three sum-algebra identities.
      have ha3eq : a3 = -Dvvv + BGv + BvG := by
        funext i
        simp only [ha3def, hDvvvdef, hBGvdef, hBvGdef, Pi.add_apply, Pi.neg_apply, hGvj]
      have hI1 : GPuu = Γv - x • BvG - x • BGv + x ^ 2 • BGG :=
        bilin_sub_smul_expand (fun i j k => christoffel g gi i j k p) v Γv x
      have hI2raw : GXuu - GPuu - Dstar = Rrem :=
        bilin_taylor_repack (fun i j k => christoffel g gi i j k X)
          (fun i j k => christoffel g gi i j k p)
          (fun i j k l => pd (fun z => christoffel g gi i j k z) l p) ustar (X - p)
      have hI2eq : GXuu = GPuu + Dstar + Rrem := by rw [← hI2raw]; abel
      have hStepB : Γv - x • a3 - GXuu = (x • Dvvv - Dstar) - x ^ 2 • BGG - Rrem := by
        rw [ha3eq, hI2eq, hI1]; simp only [smul_add, smul_neg]; abel
      -- the tube-derived first-order bounds at this `x`.
      have hvu : ‖v - ustar‖ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := by
        have e : v - ustar = x • Γv := by rw [hustardef]; abel
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0]
        calc x * ‖Γv‖ ≤ 1 * ‖Γv‖ := mul_le_mul_of_nonneg_right hxle1 (norm_nonneg _)
          _ = ‖Γv‖ := one_mul _
          _ ≤ Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 := hΓv_bound
      have hxvd : ‖x • v - (X - p)‖ ≤ Pc * ‖v‖ ^ 2 := by
        have e : x • v - (X - p) = -((Y x).1 - p - x • v) := by rw [hXdef]; abel
        rw [e, norm_neg, hPcdef]; exact hpos_tube x hxIcc
      have ha3_bd : ‖a3‖ ≤ A3c * ‖v‖ ^ 3 := by
        rw [ha3eq]
        have hDvvv_bd : ‖Dvvv‖ ≤ Nc * (n : ℝ) ^ 3 * ‖v‖ ^ 3 := by
          have h := christoffel_pd_trilin_bound g gi p v v v Nc0 hNc
          calc ‖Dvvv‖ ≤ Nc * (n : ℝ) ^ 3 * (‖v‖ * ‖v‖ * ‖v‖) := h
            _ = Nc * (n : ℝ) ^ 3 * ‖v‖ ^ 3 := by ring
        have hBGv_bd : ‖BGv‖ ≤ Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3 := by
          have h := christoffel_bilin_bound g gi p Γv v Mc0 (fun i j k => hMc p hpmem i j k)
          calc ‖BGv‖ ≤ Mc * (n : ℝ) ^ 2 * (‖Γv‖ * ‖v‖) := h
            _ ≤ Mc * (n : ℝ) ^ 2 * (Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖v‖) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hΓv_bound (norm_nonneg _)) (mul_nonneg Mc0 (hn 2))
            _ = Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3 := by ring
        have hBvG_bd : ‖BvG‖ ≤ Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3 := by
          have h := christoffel_bilin_bound g gi p v Γv Mc0 (fun i j k => hMc p hpmem i j k)
          calc ‖BvG‖ ≤ Mc * (n : ℝ) ^ 2 * (‖v‖ * ‖Γv‖) := h
            _ ≤ Mc * (n : ℝ) ^ 2 * (‖v‖ * (Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hΓv_bound (norm_nonneg _)) (mul_nonneg Mc0 (hn 2))
            _ = Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3 := by ring
        calc ‖-Dvvv + BGv + BvG‖ ≤ ‖-Dvvv + BGv‖ + ‖BvG‖ := norm_add_le _ _
          _ ≤ (‖-Dvvv‖ + ‖BGv‖) + ‖BvG‖ := add_le_add (norm_add_le _ _) le_rfl
          _ = (‖Dvvv‖ + ‖BGv‖) + ‖BvG‖ := by rw [norm_neg]
          _ ≤ (Nc * (n : ℝ) ^ 3 * ‖v‖ ^ 3 + Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3)
                + Mc ^ 2 * (n : ℝ) ^ 4 * ‖v‖ ^ 3 :=
              add_le_add (add_le_add hDvvv_bd hBGv_bd) hBvG_bd
          _ = A3c * ‖v‖ ^ 3 := by rw [hA3cdef]; ring
      -- bracket 1: the `∂Γ` trilinear discrepancy `x·Dvvv − Dstar`.
      have hΔeq' : x • Dvvv - Dstar
          = (fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
                * v j * v k * ((x • v - (X - p)) l) : Point n)
            + (fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
                * (v - ustar) j * v k * ((X - p) l) : Point n)
            + (fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
                * ustar j * (v - ustar) k * ((X - p) l) : Point n) :=
        tri_shared_telescope (fun i j k l => pd (fun z => christoffel g gi i j k z) l p)
          v ustar (X - p) x
      have hΔD_bd : ‖x • Dvvv - Dstar‖
          ≤ (Nc * (n : ℝ) ^ 3 * Pc + Nc * Mc * C₀ * (n : ℝ) ^ 5
              + Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5) * ‖v‖ ^ 4 := by
        have hNcn3 : (0 : ℝ) ≤ Nc * (n : ℝ) ^ 3 := mul_nonneg Nc0 (hn 3)
        have hA := christoffel_pd_trilin_bound g gi p v v (x • v - (X - p)) Nc0 hNc
        have hB := christoffel_pd_trilin_bound g gi p (v - ustar) v (X - p) Nc0 hNc
        have hCc := christoffel_pd_trilin_bound g gi p ustar (v - ustar) (X - p) Nc0 hNc
        have hAb : ‖(fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
              * v j * v k * ((x • v - (X - p)) l) : Point n)‖ ≤ Nc * (n : ℝ) ^ 3 * Pc * ‖v‖ ^ 4 := by
          refine hA.trans ?_
          calc Nc * (n : ℝ) ^ 3 * (‖v‖ * ‖v‖ * ‖x • v - (X - p)‖)
              ≤ Nc * (n : ℝ) ^ 3 * (‖v‖ * ‖v‖ * (Pc * ‖v‖ ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hxvd (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
                  hNcn3
            _ = Nc * (n : ℝ) ^ 3 * Pc * ‖v‖ ^ 4 := by ring
        have hBb : ‖(fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
              * (v - ustar) j * v k * ((X - p) l) : Point n)‖
            ≤ Nc * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4 := by
          refine hB.trans ?_
          calc Nc * (n : ℝ) ^ 3 * (‖v - ustar‖ * ‖v‖ * ‖X - p‖)
              ≤ Nc * (n : ℝ) ^ 3 * (Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2 * ‖v‖ * (C₀ * ‖v‖)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (mul_le_mul_of_nonneg_right hvu (norm_nonneg _)) hXpC0
                    (norm_nonneg _)
                    (mul_nonneg (mul_nonneg (mul_nonneg Mc0 (hn 2)) (sq_nonneg _)) (norm_nonneg _)))
                  hNcn3
            _ = Nc * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4 := by ring
        have hCb : ‖(fun i => ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p
              * ustar j * (v - ustar) k * ((X - p) l) : Point n)‖
            ≤ Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4 := by
          refine hCc.trans ?_
          calc Nc * (n : ℝ) ^ 3 * (‖ustar‖ * ‖v - ustar‖ * ‖X - p‖)
              ≤ Nc * (n : ℝ) ^ 3 * (Cu * ‖v‖ * (Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2) * (C₀ * ‖v‖)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul (mul_le_mul hustar_bd hvu (norm_nonneg _)
                    (mul_nonneg hCu0 (norm_nonneg _))) hXpC0 (norm_nonneg _)
                    (mul_nonneg (mul_nonneg hCu0 (norm_nonneg _))
                      (mul_nonneg (mul_nonneg Mc0 (hn 2)) (sq_nonneg _))))
                  hNcn3
            _ = Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4 := by ring
        rw [hΔeq']
        calc ‖_ + _ + _‖ ≤ (‖_‖ + ‖_‖) + ‖_‖ :=
              (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ (Nc * (n : ℝ) ^ 3 * Pc * ‖v‖ ^ 4 + Nc * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4)
                + Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5 * ‖v‖ ^ 4 :=
              add_le_add (add_le_add hAb hBb) hCb
          _ = (Nc * (n : ℝ) ^ 3 * Pc + Nc * Mc * C₀ * (n : ℝ) ^ 5
                + Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5) * ‖v‖ ^ 4 := by ring
      -- bracket 2: `x²·Γ_p(Γv,Γv)`.
      have hBGG_bd : ‖x ^ 2 • BGG‖ ≤ Mc ^ 3 * (n : ℝ) ^ 6 * ‖v‖ ^ 4 := by
        have hBGG_norm : ‖BGG‖ ≤ Mc ^ 3 * (n : ℝ) ^ 6 * ‖v‖ ^ 4 := by
          have h := christoffel_bilin_bound g gi p Γv Γv Mc0 (fun i j k => hMc p hpmem i j k)
          calc ‖BGG‖ ≤ Mc * (n : ℝ) ^ 2 * (‖Γv‖ * ‖Γv‖) := h
            _ ≤ Mc * (n : ℝ) ^ 2
                * ((Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2) * (Mc * (n : ℝ) ^ 2 * ‖v‖ ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hΓv_bound hΓv_bound (norm_nonneg _)
                    (mul_nonneg (mul_nonneg Mc0 (hn 2)) (sq_nonneg _))) (mul_nonneg Mc0 (hn 2))
            _ = Mc ^ 3 * (n : ℝ) ^ 6 * ‖v‖ ^ 4 := by ring
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc x ^ 2 * ‖BGG‖ ≤ 1 * ‖BGG‖ :=
              mul_le_mul_of_nonneg_right (by nlinarith [hx0, hxle1]) (norm_nonneg _)
          _ = ‖BGG‖ := one_mul _
          _ ≤ Mc ^ 3 * (n : ℝ) ^ 6 * ‖v‖ ^ 4 := hBGG_norm
      -- bracket 3: the second-order Taylor remainder `Rrem`.
      have hRcoef : ∀ i j k, |christoffel g gi i j k X - christoffel g gi i j k p
          - ∑ l, pd (fun z => christoffel g gi i j k z) l p * (X - p) l|
            ≤ (M2 : ℝ) * (n : ℝ) * ‖X - p‖ ^ 2 := by
        intro i j k
        refine christoffel_taylor_bound g gi p X i j k M20
          (fun y => (hC i j k).differentiable (by simp) y) ?_
        intro l θ hθ
        have hmem1 : p + θ • (X - p) ∈ Metric.closedBall p R := by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hθ.1]
          calc θ * ‖X - p‖ ≤ 1 * ‖X - p‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
            _ = ‖X - p‖ := one_mul _
            _ ≤ C₀ * ‖v‖ := hXpC0
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀
            _ = R := by rw [hRdef]
        have := hM2 (p + θ • (X - p)) hmem1 p hpmem i j k l
        rwa [add_sub_cancel_left] at this
      have hRrem_bd : ‖Rrem‖ ≤ M2 * (n : ℝ) ^ 3 * C₀ ^ 2 * Cu ^ 2 * ‖v‖ ^ 4 := by
        have hMc0' : (0 : ℝ) ≤ (M2 : ℝ) * (n : ℝ) * ‖X - p‖ ^ 2 :=
          mul_nonneg (mul_nonneg M20 (Nat.cast_nonneg n)) (sq_nonneg _)
        have h := bilin_sup_bound
          (fun i j k => christoffel g gi i j k X - christoffel g gi i j k p
            - ∑ l, pd (fun z => christoffel g gi i j k z) l p * (X - p) l) ustar ustar hMc0' hRcoef
        refine h.trans ?_
        have hXp2 : ‖X - p‖ ^ 2 ≤ C₀ ^ 2 * ‖v‖ ^ 2 := by
          calc ‖X - p‖ ^ 2 = ‖X - p‖ * ‖X - p‖ := by ring
            _ ≤ (C₀ * ‖v‖) * (C₀ * ‖v‖) :=
                mul_le_mul hXpC0 hXpC0 (norm_nonneg _) (mul_nonneg hC₀ (norm_nonneg _))
            _ = C₀ ^ 2 * ‖v‖ ^ 2 := by ring
        have hus2 : ‖ustar‖ * ‖ustar‖ ≤ Cu ^ 2 * ‖v‖ ^ 2 := by
          calc ‖ustar‖ * ‖ustar‖ ≤ (Cu * ‖v‖) * (Cu * ‖v‖) :=
                mul_le_mul hustar_bd hustar_bd (norm_nonneg _) (mul_nonneg hCu0 (norm_nonneg _))
            _ = Cu ^ 2 * ‖v‖ ^ 2 := by ring
        have e1 : (M2 : ℝ) * (n : ℝ) * ‖X - p‖ ^ 2 * (n : ℝ) ^ 2 * (‖ustar‖ * ‖ustar‖)
            = ((M2 : ℝ) * (n : ℝ) * (n : ℝ) ^ 2) * (‖X - p‖ ^ 2 * (‖ustar‖ * ‖ustar‖)) := by ring
        have e2 : M2 * (n : ℝ) ^ 3 * C₀ ^ 2 * Cu ^ 2 * ‖v‖ ^ 4
            = ((M2 : ℝ) * (n : ℝ) * (n : ℝ) ^ 2) * ((C₀ ^ 2 * ‖v‖ ^ 2) * (Cu ^ 2 * ‖v‖ ^ 2)) := by
          ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hXp2 hus2 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
          (by positivity)
      -- bracket 4: `Γ_X(u*,u*) − Γ_X(U,U)`.
      have hbr3raw : ‖GXuu - GXUU‖
          ≤ Mc * (n : ℝ) ^ 2 * (‖ustar - U‖ * (‖ustar‖ + ‖U‖))
            + (0 : ℝ) * (n : ℝ) ^ 2 * (‖X - X‖ * ‖U‖ ^ 2) :=
        christoffel_quad_diff_bound g gi X X ustar U Mc0 (le_refl (0 : ℝ))
          (fun i j k => hMc X hXmem i j k) (fun i j k => by simp)
      have hbr3 : ‖GXuu - GXUU‖ ≤ Mc * (n : ℝ) ^ 2 * (‖ustar - U‖ * (‖ustar‖ + ‖U‖)) := by
        simpa using hbr3raw
      have hustarU : ‖ustar - U‖ ≤ (1 / 2 : ℝ) * A3c * ‖v‖ ^ 3 + ‖Y x - M x‖ := by
        have e2 : (Y x - M x).2 = U - (v - x • Γv + (x ^ 2 / 2) • a3) := by
          rw [Prod.snd_sub, hMx2, ← hUdef]
        have e : ustar - U = -((x ^ 2 / 2) • a3) - (Y x - M x).2 := by
          rw [e2, hustardef]; abel
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
        have ha3half : ‖(x ^ 2 / 2) • a3‖ ≤ (1 / 2 : ℝ) * A3c * ‖v‖ ^ 3 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          calc x ^ 2 / 2 * ‖a3‖ ≤ (1 / 2 : ℝ) * ‖a3‖ :=
                mul_le_mul_of_nonneg_right (by nlinarith [hx0, hxle1]) (norm_nonneg _)
            _ ≤ (1 / 2 : ℝ) * (A3c * ‖v‖ ^ 3) :=
                mul_le_mul_of_nonneg_left ha3_bd (by norm_num)
            _ = (1 / 2 : ℝ) * A3c * ‖v‖ ^ 3 := by ring
        have hsnd : ‖(Y x - M x).2‖ ≤ ‖Y x - M x‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
        linarith [ha3half, hsnd]
      have hbr3_bd : ‖GXuu - GXUU‖
          ≤ (1 / 2 : ℝ) * Mc * (n : ℝ) ^ 2 * (Cu + C₀) * A3c * ‖v‖ ^ 4
            + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
        refine hbr3.trans ?_
        have hsum : ‖ustar‖ + ‖U‖ ≤ (Cu + C₀) * ‖v‖ := by
          calc ‖ustar‖ + ‖U‖ ≤ Cu * ‖v‖ + C₀ * ‖v‖ := add_le_add hustar_bd hUC0
            _ = (Cu + C₀) * ‖v‖ := by ring
        have hstep : ‖ustar - U‖ * (‖ustar‖ + ‖U‖)
            ≤ ((1 / 2 : ℝ) * A3c * ‖v‖ ^ 3 + ‖Y x - M x‖) * ((Cu + C₀) * ‖v‖) :=
          mul_le_mul hustarU hsum (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA3c0) (by positivity))
              (norm_nonneg _))
        calc Mc * (n : ℝ) ^ 2 * (‖ustar - U‖ * (‖ustar‖ + ‖U‖))
            ≤ Mc * (n : ℝ) ^ 2
                * (((1 / 2 : ℝ) * A3c * ‖v‖ ^ 3 + ‖Y x - M x‖) * ((Cu + C₀) * ‖v‖)) :=
              mul_le_mul_of_nonneg_left hstep (mul_nonneg Mc0 (hn 2))
          _ = (1 / 2 : ℝ) * Mc * (n : ℝ) ^ 2 * (Cu + C₀) * A3c * ‖v‖ ^ 4
                + (Mc * (n : ℝ) ^ 2 * (Cu + C₀)) * ‖v‖ * ‖Y x - M x‖ := by ring
          _ = (1 / 2 : ℝ) * Mc * (n : ℝ) ^ 2 * (Cu + C₀) * A3c * ‖v‖ ^ 4
                + Bcoef * ‖v‖ * ‖Y x - M x‖ := by rw [hBcoefdef]
      -- assemble the `Err` bound.
      have hErr : ‖Γv - x • a3 - GXUU‖ ≤ Acoef * ‖v‖ ^ 4 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by
        have hsplit : Γv - x • a3 - GXUU
            = (x • Dvvv - Dstar) - x ^ 2 • BGG - Rrem + (GXuu - GXUU) := by
          have e : Γv - x • a3 - GXUU = (Γv - x • a3 - GXuu) + (GXuu - GXUU) := by abel
          rw [e, hStepB]
        have htri : ‖Γv - x • a3 - GXUU‖
            ≤ ‖x • Dvvv - Dstar‖ + ‖x ^ 2 • BGG‖ + ‖Rrem‖ + ‖GXuu - GXUU‖ := by
          rw [hsplit]
          refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
          refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
          exact norm_sub_le _ _
        refine htri.trans ?_
        calc ‖x • Dvvv - Dstar‖ + ‖x ^ 2 • BGG‖ + ‖Rrem‖ + ‖GXuu - GXUU‖
            ≤ (Nc * (n : ℝ) ^ 3 * Pc + Nc * Mc * C₀ * (n : ℝ) ^ 5
                  + Nc * Cu * Mc * C₀ * (n : ℝ) ^ 5) * ‖v‖ ^ 4
                + Mc ^ 3 * (n : ℝ) ^ 6 * ‖v‖ ^ 4
                + M2 * (n : ℝ) ^ 3 * C₀ ^ 2 * Cu ^ 2 * ‖v‖ ^ 4
                + ((1 / 2 : ℝ) * Mc * (n : ℝ) ^ 2 * (Cu + C₀) * A3c * ‖v‖ ^ 4
                  + Bcoef * ‖v‖ * ‖Y x - M x‖) :=
              add_le_add (add_le_add (add_le_add hΔD_bd hBGG_bd) hRrem_bd) hbr3_bd
          _ = Acoef * ‖v‖ ^ 4 + Bcoef * ‖v‖ * ‖Y x - M x‖ := by rw [hAcoefdef]; ring
      -- close the two components of the residual derivative norm.
      have hid : geodesicField g gi (Y x)
          - ((v - x • Γv + (x ^ 2 / 2) • a3, -Γv + x • a3) : Point n × Point n)
        = ((Y x).2 - (v - x • Γv + (x ^ 2 / 2) • a3),
            Γv - x • a3
              - (fun i => ∑ j, ∑ k, christoffel g gi i j k (Y x).1 * (Y x).2 j * (Y x).2 k)) :=
        expJet2_residual_deriv_eq g gi Y Γv a3 v x
      rw [hid]
      simp only [← hXdef, ← hUdef]
      rw [Prod.norm_def]
      apply max_le
      · have e : U - (v - x • Γv + (x ^ 2 / 2) • a3) = (Y x - M x).2 := by
          rw [Prod.snd_sub, hMx2, ← hUdef]
        rw [e]
        have h1 : ‖(Y x - M x).2‖ ≤ ‖Y x - M x‖ := by rw [Prod.norm_def]; exact le_max_right _ _
        have h2 : (0 : ℝ) ≤ Bcoef * ‖v‖ * ‖Y x - M x‖ :=
          mul_nonneg (mul_nonneg hBcoef0 (norm_nonneg _)) (norm_nonneg _)
        have h3 : (0 : ℝ) ≤ Acoef * ‖v‖ ^ 4 := mul_nonneg hAcoef0 (by positivity)
        have hexp : (1 + Bcoef * ‖v‖) * ‖Y x - M x‖
            = ‖Y x - M x‖ + Bcoef * ‖v‖ * ‖Y x - M x‖ := by ring
        rw [hexp]; linarith [h1]
      · rw [← hGXUUdef]
        have hexp : (1 + Bcoef * ‖v‖) * ‖Y x - M x‖
            = ‖Y x - M x‖ + Bcoef * ‖v‖ * ‖Y x - M x‖ := by ring
        rw [hexp]; linarith [hErr, norm_nonneg (Y x - M x)]
    -- inhomogeneous Grönwall.
    have hg1 := (norm_le_gronwallBound_of_norm_deriv_right_le hf hf' ha bound) 1
      (by norm_num [Set.mem_Icc])
    rw [sub_zero] at hg1
    -- project the position component of `r₃ 1`.
    have htarget : expMap g gi hC p v - p - v + (1 / 2 : ℝ) • Γv - (1 / 6 : ℝ) • a3
        = (Y 1 - M 1).1 := by
      rw [Prod.fst_sub]
      have hM1 : (M 1).1 = p + v - (1 / 2 : ℝ) • Γv + (1 / 6 : ℝ) • a3 := by
        show p + (1 : ℝ) • v - ((1 : ℝ) ^ 2 / 2) • Γv + ((1 : ℝ) ^ 3 / 6) • a3
            = p + v - (1 / 2 : ℝ) • Γv + (1 / 6 : ℝ) • a3
        simp only [one_smul, one_pow]
      have hexpeq : expMap g gi hC p v = (Y 1).1 := by simp only [expMap, hYdef]
      rw [hM1, hexpeq]; abel
    have h2 : gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 4) 1 ≤ Cfinal * ‖v‖ ^ 4 := by
      rw [gronwallBound_zero_linear]
      have hKpos : 0 ≤ 1 + Bcoef * ‖v‖ := by
        have := mul_nonneg hBcoef0 (norm_nonneg v); linarith
      have hAv0 : 0 ≤ Acoef * ‖v‖ ^ 4 := mul_nonneg hAcoef0 (by positivity)
      have hKle : 1 + Bcoef * ‖v‖ ≤ Kmax := by
        rw [hKmaxdef]
        have : Bcoef * ‖v‖ ≤ Bcoef * ρ := mul_le_mul_of_nonneg_left hvρ hBcoef0
        linarith
      calc Acoef * ‖v‖ ^ 4 * gronwallBound 0 (1 + Bcoef * ‖v‖) 1 1
          ≤ Acoef * ‖v‖ ^ 4 * Real.exp (1 + Bcoef * ‖v‖) :=
            mul_le_mul_of_nonneg_left (gronwallBound_zero_one_le_exp _ hKpos) hAv0
        _ ≤ Acoef * ‖v‖ ^ 4 * Real.exp Kmax :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKle) hAv0
        _ = Cfinal * ‖v‖ ^ 4 := by rw [hCfinaldef]; ring
    rw [htarget]
    calc ‖(Y 1 - M 1).1‖
        ≤ ‖Y 1 - M 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ gronwallBound 0 (1 + Bcoef * ‖v‖) (Acoef * ‖v‖ ^ 4) 1 := hg1
      _ ≤ Cfinal * ‖v‖ ^ 4 := h2
  -- Package `O(‖v‖⁴)` into `o(‖v‖³)`.
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hev1 : ∀ᶠ v in 𝓝 (0 : Point n), ‖v‖ ≤ ρ :=
    Metric.eventually_nhds_iff.mpr ⟨ρ, hρpos, fun v hv => by
      rw [dist_zero_right] at hv; exact hv.le⟩
  have hev2 : ∀ᶠ v in 𝓝 (0 : Point n), ‖v‖ ≤ c / (Cfinal + 1) :=
    Metric.eventually_nhds_iff.mpr ⟨c / (Cfinal + 1), div_pos hc (by linarith [hCfinal0]),
      fun v hv => by rw [dist_zero_right] at hv; exact hv.le⟩
  filter_upwards [hev1, hev2] with v hv1 hv2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hCv : Cfinal * ‖v‖ ≤ c := by
    calc Cfinal * ‖v‖ ≤ Cfinal * (c / (Cfinal + 1)) := mul_le_mul_of_nonneg_left hv2 hCfinal0
      _ = Cfinal / (Cfinal + 1) * c := by ring
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right
          (by rw [div_le_one (by linarith [hCfinal0])]; linarith [hCfinal0]) hc.le
      _ = c := one_mul c
  refine le_trans (hbound v hv1) ?_
  calc Cfinal * ‖v‖ ^ 4 = Cfinal * ‖v‖ * ‖v‖ ^ 3 := by ring
    _ ≤ c * ‖v‖ ^ 3 := mul_le_mul_of_nonneg_right hCv (by positivity)

/-! ### EXP-JET3a — setup for the localized first-variation / operator-valued fundamental solution

  Toward EXP-JET3 (the Jacobian field expansion `fderiv exp_p y = 1 + B(y,·) + ½T(y,y,·) + o(‖y‖²)`),
  the crux is the localized first variation `HasFDerivAt (w ↦ Y_w t) (Φ_v t ∘ ι) v` for `v` near 0,
  where `Φ_v` is the operator-valued fundamental solution of the linearized (Jacobi) equation
  `Φ' = DF(Y_v(t))·Φ`, `Φ_v 0 = 1`, along the FIXED confined tube `Y_v = expTube p v`, and
  `ι k = (0,k)`, `π (x,u) = x`, `L v := π ∘ (Φ_v 1) ∘ ι`.  GPT-5.5-pro flagged `Φ_v` as a
  NONAUTONOMOUS linear ODE and worried Mathlib's Picard–Lindelöf is autonomous-only.

  **KEY FINDING (this increment):** Mathlib's Picard–Lindelöf `IsPicardLindelof f t₀ x₀ a r L K` is
  ALREADY stated for a TIME-DEPENDENT field `f : ℝ → E → E` (`Mathlib/Analysis/ODE/PicardLindelof.lean`;
  the autonomous corollaries wrap `(fun _ ↦ f)` via `IsPicardLindelof.of_contDiffAt_one`).  So the
  nonautonomous fundamental solution `Φ_v` (field `Ψ_v t M = (DF(Y_v t)).comp M`, linear ⇒ globally
  Lipschitz in `M`, continuous in `t` since `Y_v` and `fderiv F` are continuous) is NOT blocked by a
  missing Mathlib theorem — it is a (large) instantiation-plus-assembly effort, not an infrastructure gap.

  This increment lands the flow-independent SETUP pieces that build green:
  * `expJetIota` / `expJetPi` — the inclusion `ι` and projection `π` (`inr` / `fst` as CLMs);
  * `geodesicField_differentiable` / `hasFDerivAt_geodesicField_fderiv` — `DF = fderiv F` exists
    everywhere (`F` is `C^∞`);
  * `expJet_linVariation_residual_deriv` — the residual ODE identity `R' = DF(Y₁)·R + N` with
    `N = F(Y₂) − F(Y₁) − DF(Y₁)(Y₂ − Y₁)`, for `R = (Y₂ − Y₁) − J` and ANY `J` solving the Jacobi
    equation `J' = DF(Y₁)·J` along `Y₁` (pure calculus + `DF` linearity);
  * `geodesicField_uniform_C1_remainder` — the genuine analytic ingredient: the UNIFORM first-order
    Taylor (C¹) remainder of `F` on any convex compact set `S`, `∀ε>0 ∃δ>0`, `‖F a − F b − DF(b)(a−b)‖
    ≤ ε‖a−b‖` whenever `a,b∈S`, `‖a−b‖<δ` (Heine–Cantor uniform continuity of `fderiv F` on `S` +
    the mean-value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` on the segment).

  CHECKPOINT (NOT yet built): the fundamental solution `Φ_v` as a function with `Φ_v 0 = 1` and
  `Φ_v' = DF(Y_v)·Φ_v` uniformly over `‖v‖ ≤ ρ₀`, and the target
  `HasFDerivAt (expMap g gi hC p) (π ∘ (Φ_v 1) ∘ ι) v` near 0.  The remaining work is: instantiate the
  nonautonomous `IsPicardLindelof` for `Ψ_v` on `[0,1]` (bounds/Lipschitz from the compact tube),
  extend to the unit interval uniformly in `v`, take `J_k := Φ_v(·)(ι k)`, and run the inhomogeneous
  Grönwall on `R_k` with `‖Z_k‖ ≤ Ctw‖k‖` (`geodesic_twopoint_gronwall`) and `‖N_k‖ ≤ εCtw‖k‖`
  (`geodesicField_uniform_C1_remainder`) to get `‖R_k(1)‖ = o(‖k‖)`, then project with `π`.

  HONEST CAPTION (binding): flow-independent setup toward the Jacobian-field expansion (EXP-JET3),
  itself a step toward discharging `hgauge`.  It does NOT yet build `Φ_v`, does NOT give the localized
  first variation, does NOT give the Jacobian expansion, does NOT build the pullback metric, and does
  NOT move numerical-G (species count `N`, granularity scale `Λ_s`, the `E/ξ` term remain). -/

/-- **The inclusion `ι : Point n →L[ℝ] State`**, `ι h = (0, h)`.  Injects a velocity perturbation as
    the initial condition `J_k(0) = (0,k)` of the first-variation (Jacobi) field along the tube. -/
noncomputable def expJetIota : Point n →L[ℝ] (Point n × Point n) :=
  ContinuousLinearMap.inr ℝ (Point n) (Point n)

@[simp] theorem expJetIota_apply (h : Point n) :
    expJetIota (n := n) h = ((0, h) : Point n × Point n) := rfl

/-- **The projection `π : State →L[ℝ] Point n`**, `π (x,u) = x`.  Reads off the position component of
    the fundamental solution at `t = 1` (`L v := π ∘ (Φ_v 1) ∘ ι`). -/
noncomputable def expJetPi : (Point n × Point n) →L[ℝ] Point n :=
  ContinuousLinearMap.fst ℝ (Point n) (Point n)

@[simp] theorem expJetPi_apply (z : Point n × Point n) : expJetPi (n := n) z = z.1 := rfl

/-- **The geodesic field is differentiable everywhere.**  `F = geodesicField g gi` is `C^∞`
    (`contDiff_geodesicField`), hence differentiable; `DF := fderiv ℝ F` is well-defined (not junk). -/
theorem geodesicField_differentiable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    Differentiable ℝ (geodesicField g gi) :=
  (contDiff_geodesicField g gi hC).differentiable (by simp)

/-- **`DF = fderiv F` is a genuine Fréchet derivative of `F` at every phase point.**  The linear
    coefficient `A_v(t) = DF(Y_v(t))` of the nonautonomous Jacobi ODE `Φ' = A_v(t)·Φ` is therefore
    well-defined and honest (never junk off a differentiability set). -/
theorem hasFDerivAt_geodesicField_fderiv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (z : Point n × Point n) :
    HasFDerivAt (geodesicField g gi) (fderiv ℝ (geodesicField g gi) z) z :=
  (geodesicField_differentiable g gi hC z).hasFDerivAt

/-- **EXP-JET3c — the closed-form Fréchet derivative of the geodesic field at a general phase point.**
    `DF(x,u)(ξ,η) = (η, i ↦ −∑_{jk} [(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·u_j·u_k + Γ^i_{jk}(x)·η_j·u_k
    + Γ^i_{jk}(x)·u_j·η_k])`.  The first component is the linear velocity slot (`(ξ,η) ↦ η`); the
    acceleration component differentiates the quadratic-in-`u`, Christoffel-composed form
    `−∑_{jk} Γ^i_{jk}(x)·u_j·u_k` by the product rule (`HasFDerivAt.mul`), with
    `fderiv Γ^i_{jk}(x)·ξ = ∑_l ∂_l Γ^i_{jk}(x)·ξ_l` (`fderiv_apply_eq_sum_pd`).

    This is the honest closed form of `A_v(t) = DF(Y_v t)` — the coefficient of the Jacobi ODE — the
    foundation for identifying the order-0/1/2 coefficients `A₀ = DF(e)`, `A₁`, `A₂` of the uniform
    `DF(Y_y t)` expansion (EXP-JET3c).  Specialising to `(x,u) = (p,0)` recovers `DF(e) = A₀`
    (`linF`, the `η`-in-first-slot nilpotent), since every acceleration term carries a factor `u = 0`.

    HONEST: this is the pointwise closed-form Jacobi coefficient; it does NOT by itself give the
    uniform order-2 expansion, NOT the Jacobian 2-jet, NOT the pullback metric, NOT numerical-G. -/
theorem geodesicField_fderiv_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x u ξ η : Point n) :
    fderiv ℝ (geodesicField g gi) ((x, u) : Point n × Point n) ((ξ, η) : Point n × Point n)
      = (η, (fun i => -∑ j, ∑ k,
          ((∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * u j * u k
            + christoffel g gi i j k x * η j * u k
            + christoffel g gi i j k x * u j * η k) : Point n)) := by
  have hΓdiff : ∀ i j k, DifferentiableAt ℝ (fun z : Point n => christoffel g gi i j k z) x :=
    fun i j k => ((hC i j k).differentiable (by simp)).differentiableAt
  -- per-term product-rule derivative of `q ↦ Γ^i_{jk}(q.1)·q.2 j·q.2 k`.
  have hterm := fun i j k =>
    ((((hΓdiff i j k).hasFDerivAt).comp (x, u) hasFDerivAt_fst).mul
        (((ContinuousLinearMap.proj (R := ℝ) j).comp
          (ContinuousLinearMap.snd ℝ (Point n) (Point n))).hasFDerivAt)).mul
        (((ContinuousLinearMap.proj (R := ℝ) k).comp
          (ContinuousLinearMap.snd ℝ (Point n) (Point n))).hasFDerivAt)
  -- the acceleration component's derivative (per `i`, negated double sum of term derivatives).
  have hAcc := hasFDerivAt_pi.2 (fun i =>
    (HasFDerivAt.fun_sum (u := (univ : Finset (Fin n)))
      (fun j _ => HasFDerivAt.fun_sum (u := (univ : Finset (Fin n)))
        (fun k _ => hterm i j k))).neg)
  have hF : HasFDerivAt (geodesicField g gi) _ (x, u) := hasFDerivAt_snd.prodMk hAcc
  rw [hF.fderiv]
  refine Prod.ext ?_ ?_
  · simp
  · funext i
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp_apply, Pi.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [fderiv_apply_eq_sum_pd (fun z => christoffel g gi i j k z) x ξ (hΓdiff i j k)]
    ring

/-- **EXP-JET3c (STEP 1 core) — the operator-norm bound `‖DF(x,u) − A₀‖ ≤ Nc·n³·‖u‖² + 2·Mc·n²·‖u‖`.**
    With `A₀ = linF` (`DF(e)`), the Jacobi coefficient `DF(x,u)` differs from `A₀` only in its
    acceleration block, which is bounded (in operator norm) by a polynomial in `‖u‖` vanishing at
    `u = 0`: given `|Γ^i_{jk}(x)| ≤ Mc` and `|∂_l Γ^i_{jk}(x)| ≤ Nc`,
    `‖DF(x,u) − A₀‖ ≤ Nc·n³·‖u‖² + 2·(Mc·n²)·‖u‖`.

    Proof: `(DF(x,u) − A₀)(ξ,η) = (0, Acc)` (the velocity slots `η` cancel; `A₀(ξ,η) = (η,0)`), with the
    acceleration block `Acc = −∑_{jk}[(∑_l ∂_lΓ·ξ_l)u_j u_k + Γ·η_j u_k + Γ·u_j η_k]`, so
    `‖(DF(x,u) − A₀)(ξ,η)‖ = ‖Acc‖`, split into the ∂Γ-trilinear form (`christoffel_pd_trilin_bound`,
    `≤ Nc·n³·‖u‖²·‖ξ‖`) and two Γ-bilinear forms (`christoffel_bilin_bound`, `≤ Mc·n²·‖u‖·‖η‖` each),
    with `‖ξ‖, ‖η‖ ≤ ‖(ξ,η)‖`; `ContinuousLinearMap.opNorm_le_bound` reads off the operator bound.

    Composed with the tube value 2-jet (`‖(Y_v t).2‖ = ‖u‖ = O(‖v‖)`, `expTube_value_two_jet`), this is
    the order-0 remainder `‖DF(Y_v t) − A₀‖ ≤ C·‖v‖` of the uniform `DF(Y_v t)` expansion.  HONEST: the
    operator-norm "A₀ is leading" bound; it does NOT by itself identify the order-1/2 coefficients
    `A₁, A₂`, NOT the full Jacobian 2-jet, NOT the pullback metric, NOT numerical-G (`N`, `Λ_s`, `E/ξ`). -/
theorem geodesicField_fderiv_sub_linF_opNorm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x u : Point n) {Mc Nc : ℝ} (hMc0 : 0 ≤ Mc) (hNc0 : 0 ≤ Nc)
    (hMc : ∀ i j k, |christoffel g gi i j k x| ≤ Mc)
    (hNc : ∀ i j k l, |pd (fun z => christoffel g gi i j k z) l x| ≤ Nc) :
    ‖fderiv ℝ (geodesicField g gi) ((x, u) : Point n × Point n) - linF‖
      ≤ Nc * (n : ℝ) ^ 3 * ‖u‖ ^ 2 + 2 * (Mc * (n : ℝ) ^ 2) * ‖u‖ := by
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hNcn : 0 ≤ Nc * (n : ℝ) ^ 3 := mul_nonneg hNc0 (by positivity)
  have hMcn : 0 ≤ Mc * (n : ℝ) ^ 2 := mul_nonneg hMc0 (by positivity)
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact add_nonneg (mul_nonneg hNcn (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num) hMcn) hu0)
  intro z
  obtain ⟨ξ, η⟩ := z
  have hξ : ‖ξ‖ ≤ ‖((ξ, η) : Point n × Point n)‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have hη : ‖η‖ ≤ ‖((ξ, η) : Point n × Point n)‖ := by rw [Prod.norm_def]; exact le_max_right _ _
  -- `(DF(x,u) − A₀)(ξ,η) = (0, Acc)`, so its norm is `‖Acc‖`.
  rw [ContinuousLinearMap.sub_apply, geodesicField_fderiv_apply g gi hC x u ξ η, linF_apply,
    Prod.mk_sub_mk, sub_self, sub_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  -- split `Acc = −(TA + TB + TC)`.
  have hfun : (fun i => -∑ j, ∑ k,
        ((∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * u j * u k
          + christoffel g gi i j k x * η j * u k
          + christoffel g gi i j k x * u j * η k) : Point n)
      = -((fun i => ∑ j, ∑ k, ∑ l,
              pd (fun z => christoffel g gi i j k z) l x * u j * u k * ξ l : Point n)
          + (fun i => ∑ j, ∑ k, christoffel g gi i j k x * η j * u k : Point n)
          + (fun i => ∑ j, ∑ k, christoffel g gi i j k x * u j * η k : Point n)) := by
    funext i
    simp only [Pi.neg_apply, Pi.add_apply]
    rw [neg_inj]
    have hdist : ∑ j, ∑ k,
          ((∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * u j * u k
            + christoffel g gi i j k x * η j * u k + christoffel g gi i j k x * u j * η k)
        = (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * u j * u k)
          + (∑ j, ∑ k, christoffel g gi i j k x * η j * u k)
          + (∑ j, ∑ k, christoffel g gi i j k x * u j * η k) := by
      simp only [Finset.sum_add_distrib]
    rw [hdist]
    have hTA : (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * u j * u k)
        = ∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l x * u j * u k * ξ l := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hTA]
  rw [hfun, norm_neg]
  have hTAbound := christoffel_pd_trilin_bound g gi x u u ξ hNc0 hNc
  have hTBbound := christoffel_bilin_bound g gi x η u hMc0 hMc
  have hTCbound := christoffel_bilin_bound g gi x u η hMc0 hMc
  have h1 : Nc * (n : ℝ) ^ 3 * (‖u‖ * ‖u‖ * ‖ξ‖)
      ≤ Nc * (n : ℝ) ^ 3 * ‖u‖ ^ 2 * ‖((ξ, η) : Point n × Point n)‖ := by
    have hstep : ‖u‖ * ‖u‖ * ‖ξ‖ ≤ ‖u‖ * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ :=
      mul_le_mul_of_nonneg_left hξ (by positivity)
    calc Nc * (n : ℝ) ^ 3 * (‖u‖ * ‖u‖ * ‖ξ‖)
        ≤ Nc * (n : ℝ) ^ 3 * (‖u‖ * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖) :=
          mul_le_mul_of_nonneg_left hstep hNcn
      _ = Nc * (n : ℝ) ^ 3 * ‖u‖ ^ 2 * ‖((ξ, η) : Point n × Point n)‖ := by rw [sq]; ring
  have h2 : Mc * (n : ℝ) ^ 2 * (‖η‖ * ‖u‖)
      ≤ Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ := by
    have hstep : ‖η‖ * ‖u‖ ≤ ‖((ξ, η) : Point n × Point n)‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_right hη hu0
    calc Mc * (n : ℝ) ^ 2 * (‖η‖ * ‖u‖)
        ≤ Mc * (n : ℝ) ^ 2 * (‖((ξ, η) : Point n × Point n)‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left hstep hMcn
      _ = Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ := by ring
  have h3 : Mc * (n : ℝ) ^ 2 * (‖u‖ * ‖η‖)
      ≤ Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ := by
    have hstep : ‖u‖ * ‖η‖ ≤ ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ :=
      mul_le_mul_of_nonneg_left hη hu0
    calc Mc * (n : ℝ) ^ 2 * (‖u‖ * ‖η‖)
        ≤ Mc * (n : ℝ) ^ 2 * (‖u‖ * ‖((ξ, η) : Point n × Point n)‖) :=
          mul_le_mul_of_nonneg_left hstep hMcn
      _ = Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ := by ring
  refine le_trans norm_add₃_le ?_
  refine le_trans (add_le_add (add_le_add hTAbound hTBbound) hTCbound) ?_
  calc Nc * (n : ℝ) ^ 3 * (‖u‖ * ‖u‖ * ‖ξ‖) + Mc * (n : ℝ) ^ 2 * (‖η‖ * ‖u‖)
        + Mc * (n : ℝ) ^ 2 * (‖u‖ * ‖η‖)
      ≤ Nc * (n : ℝ) ^ 3 * ‖u‖ ^ 2 * ‖((ξ, η) : Point n × Point n)‖
        + Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖
        + Mc * (n : ℝ) ^ 2 * ‖u‖ * ‖((ξ, η) : Point n × Point n)‖ :=
        add_le_add (add_le_add h1 h2) h3
    _ = (Nc * (n : ℝ) ^ 3 * ‖u‖ ^ 2 + 2 * (Mc * (n : ℝ) ^ 2) * ‖u‖)
          * ‖((ξ, η) : Point n × Point n)‖ := by ring

/-- **The first-variation residual ODE identity `R' = DF(Y₁)·R + N`.**  For two geodesic integral
    curves `Y₁, Y₂` and ANY curve `J` solving the linearized (Jacobi) equation `J' = DF(Y₁ t)·J` along
    `Y₁`, the residual `R = (Y₂ − Y₁) − J` obeys `R'(t) = DF(Y₁ t)(R t) + N(t)` with the first-order
    Taylor remainder `N(t) = F(Y₂ t) − F(Y₁ t) − DF(Y₁ t)(Y₂ t − Y₁ t)`.  Pure calculus:
    `R' = (F(Y₂) − F(Y₁)) − DF(Y₁)(J)` and `DF(Y₁)(R) + N = DF(Y₁)(Y₂−Y₁−J) + N = F(Y₂) − F(Y₁) −
    DF(Y₁)(J)` by linearity of `DF = fderiv F`.  This is the exact ODE the EXP-JET3 inhomogeneous
    Grönwall integrates once `J := Φ_v(·)(ι k)` is supplied by the fundamental solution.

    HONEST: this is the residual identity for an ABSTRACT Jacobi solution `J`; it does NOT construct
    `J`/`Φ_v` (the nonautonomous fundamental solution) — that is the checkpointed remaining work. -/
theorem expJet_linVariation_residual_deriv (g gi : Point n → Fin n → Fin n → ℝ)
    {Y₁ Y₂ J : ℝ → Point n × Point n} {t : ℝ}
    (h1 : HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hJ : HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y₁ t) (J t)) t) :
    HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
      (fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t - J t)
        + (geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
            - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t))) t := by
  have hbase : HasDerivAt (fun τ => Y₂ τ - Y₁ τ - J τ)
      (geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
        - fderiv ℝ (geodesicField g gi) (Y₁ t) (J t)) t := (h2.sub h1).sub hJ
  have key : fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t - J t)
        + (geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
            - fderiv ℝ (geodesicField g gi) (Y₁ t) (Y₂ t - Y₁ t))
      = geodesicField g gi (Y₂ t) - geodesicField g gi (Y₁ t)
          - fderiv ℝ (geodesicField g gi) (Y₁ t) (J t) := by
    rw [map_sub]; abel
  rw [key]; exact hbase

/-- **Uniform first-order (C¹) Taylor remainder of the geodesic field on a convex compact set.**  For
    `S` convex and compact and `ε > 0`, there is `δ > 0` such that for all `a, b ∈ S` with `‖a−b‖ < δ`,
    `‖F a − F b − DF(b)(a−b)‖ ≤ ε‖a−b‖`, `F = geodesicField g gi`, `DF = fderiv ℝ F`.

    Proof: `F` is `C^∞`, so `fderiv F` is continuous, hence UNIFORMLY continuous on the compact `S`
    (Heine–Cantor, `IsCompact.uniformContinuousOn_of_continuous`), giving `δ` with `‖DF x − DF b‖ ≤ ε`
    for `x, b ∈ S`, `‖x−b‖ ≤ δ`.  On the segment `[b,a] ⊆ S` (convexity) every point is within `δ` of
    `b`, so the mean-value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` applied to
    `z ↦ F z − DF(b) z` (derivative `DF z − DF b`, norm `≤ ε`) yields the bound.

    This is the uniform-remainder ingredient that will bound the inhomogeneous term
    `‖N_k(t)‖ ≤ εCtw‖k‖` in the EXP-JET3 first-variation residual Grönwall.

    HONEST: this is the analytic C¹-remainder of `F` on the tube; it does NOT by itself build the
    fundamental solution `Φ_v` or the localized first variation. -/
theorem geodesicField_uniform_C1_remainder
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hconv : Convex ℝ S) (hcomp : IsCompact S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ a ∈ S, ∀ b ∈ S, ‖a - b‖ < δ →
      ‖geodesicField g gi a - geodesicField g gi b
          - fderiv ℝ (geodesicField g gi) b (a - b)‖ ≤ ε * ‖a - b‖ := by
  set F := geodesicField g gi with hFdef
  have hFdiff : Differentiable ℝ F := (contDiff_geodesicField g gi hC).differentiable (by simp)
  have hdFcont : Continuous (fderiv ℝ F) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have huc : UniformContinuousOn (fderiv ℝ F) S :=
    hcomp.uniformContinuousOn_of_continuous hdFcont.continuousOn
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp huc ε hε
  refine ⟨δ, hδ0, fun a ha b hb hab => ?_⟩
  have hs'sub : segment ℝ b a ⊆ S := hconv.segment_subset hb ha
  have hHderiv : ∀ x ∈ segment ℝ b a,
      HasFDerivWithinAt (fun z => F z - fderiv ℝ F b z)
        (fderiv ℝ F x - fderiv ℝ F b) (segment ℝ b a) x := fun x hx =>
    (((hFdiff x).hasFDerivAt).sub ((fderiv ℝ F b).hasFDerivAt)).hasFDerivWithinAt
  have hbound : ∀ x ∈ segment ℝ b a, ‖fderiv ℝ F x - fderiv ℝ F b‖ ≤ ε := by
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    have hsub : (b + θ • (a - b)) - b = θ • (a - b) := by abel
    have hxb : ‖(b + θ • (a - b)) - b‖ ≤ ‖a - b‖ := by
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ = ‖a - b‖ := one_mul _
    have hxmemS : b + θ • (a - b) ∈ S :=
      hs'sub (by rw [segment_eq_image']; exact ⟨θ, hθ, rfl⟩)
    have hd := hδ (b + θ • (a - b)) hxmemS b hb
      (by rw [dist_eq_norm]; exact le_trans hxb hab.le)
    rwa [dist_eq_norm] at hd
  calc ‖F a - F b - fderiv ℝ F b (a - b)‖
      = ‖(fun z => F z - fderiv ℝ F b z) a - (fun z => F z - fderiv ℝ F b z) b‖ := by
          congr 1; simp only [map_sub]; abel
    _ ≤ ε * ‖a - b‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
          hHderiv hbound (convex_segment b a) (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)

/-! ### EXP-JET3b — the operator-valued Jacobi field `Ψ_v`, its Picard–Lindelöf data, and the LOCAL
    fundamental solution `Φ_v`

  Toward EXP-JET3 (the localized first variation `HasFDerivAt exp_p (L v) v` near 0, `L v = π ∘ Φ_v(1)
  ∘ ι`), this increment builds the operator-valued Jacobi field `Ψ_v t M = DF(Y_v t) ∘ M` on the
  operator space `State →L State` (`State = Point n × Point n`, `Y_v = expTube p v`, `DF = fderiv F`),
  assembles its Picard–Lindelöf data (linearity ⇒ globally Lipschitz in `M`; uniform boundedness on a
  ball; continuity in `t`; the finite sup `KdF = sup_{[0,1]} ‖DF(Y_v t)‖`), and produces the LOCAL
  operator-valued fundamental solution `Φ_v` on a short interval `[0, T]` via the FULL operator-normed
  `IsPicardLindelof` instantiation — the "main cost" of the whole construction.

  **THE INTERVAL OBSTRUCTION (the exact checkpointed step).**  Mathlib's Picard–Lindelöf structure
  carries `mul_max_le : L·max(tmax−t₀, t₀−tmin) ≤ a − r`, and for a LINEAR operator ODE `Φ' = Ψ_v t Φ`
  the field's norm bound on `closedBall(1, a)` is `L = KdF·(1 + a)` (linear growth), so reaching `t = 1`
  in ONE application would need `KdF·(1 + a) ≤ a`, i.e. `KdF < 1` — FALSE for the general geodesic tube.
  A single application therefore only reaches a short interval `T ≲ 1/KdF`; extending to `[0, 1]`
  requires CONCATENATING `≈ ⌈KdF⌉` local solutions (Grönwall-glued continuation), for which Mathlib has
  NO ready theorem (there is no global/continuation existence lemma for globally-Lipschitz fields).
  Time-rescaling does not help (it scales `KdF` by the same factor).  This concatenation, and the
  subsequent first-variation residual Grönwall `HasFDerivAt exp_p (L v) v`, are the remaining EXP-JET3b
  work — a substantial assembly, not a missing theorem.

  HONEST CAPTION (binding): the operator field `Ψ_v` + its PL data + the LOCAL (short-interval)
  fundamental solution — a step toward the Jacobian-field expansion, itself a step toward discharging
  `hgauge`.  It does NOT reach the `[0,1]` fundamental solution `Φ_v(1)`, does NOT give the localized
  first variation `HasFDerivAt exp_p (L v) v`, does NOT build the pullback metric, and does NOT move
  numerical-G (species count `N`, granularity scale `Λ_s`, the `E/ξ` term remain). -/

/-- **The operator-valued nonautonomous Jacobi field** `Ψ_v t M = DF(Y_v t) ∘ M` on the operator
    space `State →L State`, `State = Point n × Point n`, `Y_v = expTube p v`, `DF = fderiv F`.  This
    is the field of the linear (matrix) ODE `Φ' = Ψ_v t Φ` whose fundamental solution `Φ_v` (with
    `Φ_v 0 = 1`) transports the first-variation (Jacobi) fields along the confined tube. -/
noncomputable def expJetPsi (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) :
    ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)) →
        ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
  fun t M => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).comp M

@[simp] theorem expJetPsi_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (t : ℝ) (M : (Point n × Point n) →L[ℝ] (Point n × Point n)) :
    expJetPsi g gi hC p v t M
      = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).comp M := rfl

/-- **`Ψ_v t` is Lipschitz in `M` with constant `‖DF(Y_v t)‖`** (linearity of the operator field):
    `‖Ψ_v t M − Ψ_v t N‖ ≤ ‖DF(Y_v t)‖·‖M − N‖`, from `DF∘M − DF∘N = DF∘(M − N)` and the operator-norm
    submultiplicativity `‖DF∘(M − N)‖ ≤ ‖DF‖·‖M − N‖`. -/
theorem expJetPsi_norm_sub_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (t : ℝ)
    (M N : (Point n × Point n) →L[ℝ] (Point n × Point n)) :
    ‖expJetPsi g gi hC p v t M - expJetPsi g gi hC p v t N‖
      ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ := by
  have hsub : expJetPsi g gi hC p v t M - expJetPsi g gi hC p v t N
      = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).comp (M - N) := by
    simp only [expJetPsi_apply, ← ContinuousLinearMap.compL_apply, ← map_sub]
  rw [hsub]
  exact (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).opNorm_comp_le (M - N)

/-- **`Ψ_v t` bound** `‖Ψ_v t M‖ ≤ ‖DF(Y_v t)‖·‖M‖` — operator-norm submultiplicativity. -/
theorem expJetPsi_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (t : ℝ) (M : (Point n × Point n) →L[ℝ] (Point n × Point n)) :
    ‖expJetPsi g gi hC p v t M‖
      ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M‖ := by
  simp only [expJetPsi_apply]
  exact (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)).opNorm_comp_le M

/-- **The confined geodesic tube is continuous on `[0,1]`** (it solves the ODE on `(-2,2) ⊇ [0,1]`). -/
theorem expTube_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    ContinuousOn (expTube g gi hC p v) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨_, hYd, _⟩ := expTube_spec g gi hC p v hv
  intro t ht
  have hmem : t ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact (hYd t hmem).continuousAt.continuousWithinAt

/-- **The Jacobi coefficient `‖DF(Y_v t)‖` is uniformly bounded on `[0,1]`** by a finite `KdF ≥ 0`.
    `t ↦ DF(Y_v t) = fderiv F ∘ Y_v` is continuous on the compact `[0,1]` (`F` is `C^∞`, `Y_v`
    continuous), hence its norm attains a finite bound (`IsCompact.exists_bound_of_continuousOn`). -/
theorem expJet_fderiv_tube_bddAbove (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    ∃ KdF : ℝ, 0 ≤ KdF ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hcomp : ContinuousOn
      (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) :=
    hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  obtain ⟨C, hC'⟩ := isCompact_Icc.exists_bound_of_continuousOn hcomp
  exact ⟨max C 0, le_max_right _ _, fun t ht => le_trans (hC' t ht) (le_max_left _ _)⟩

/-- **`t ↦ Ψ_v t M` is continuous on `[0,1]`** for fixed `M`: `t ↦ DF(Y_v t)` is continuous on `[0,1]`
    and right-composition `A ↦ A ∘ M` is a continuous linear map. -/
theorem expJetPsi_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (M : (Point n × Point n) →L[ℝ] (Point n × Point n)) :
    ContinuousOn (fun t => expJetPsi g gi hC p v t M) (Set.Icc (0 : ℝ) 1) := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hcomp : ContinuousOn
      (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Set.Icc (0 : ℝ) 1) :=
    hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)
  have key : (fun t => expJetPsi g gi hC p v t M)
      = (fun t => ((ContinuousLinearMap.compL ℝ (Point n × Point n) (Point n × Point n)
          (Point n × Point n)).flip M)
            (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) := by
    funext t
    rw [expJetPsi_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  rw [key]
  exact (((ContinuousLinearMap.compL ℝ (Point n × Point n) (Point n × Point n)
    (Point n × Point n)).flip M).continuous).comp_continuousOn hcomp

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b — the LOCAL operator-valued fundamental solution `Φ_v`.**  For `‖v‖ ≤ expRho` there is
    a short time `T > 0` and an operator-valued curve `Φ_v : ℝ → (State →L State)` with `Φ_v 0 = 1`
    (identity) solving the linearized Jacobi ODE `Φ_v' t = Ψ_v t (Φ_v t) = DF(Y_v t) ∘ Φ_v t` on
    `[0, T]`.  Built by the FULL operator-normed `IsPicardLindelof` instantiation: on `closedBall(1, 1)`
    the field `Ψ_v` is `KdF`-Lipschitz (`expJetPsi_norm_sub_le`), bounded by `2·KdF`
    (`expJetPsi_norm_le` + `‖M‖ ≤ 2`), continuous in `t` (`expJetPsi_continuousOn`), with the interval
    constraint `2·KdF·T ≤ 1` met by `T = min 1 (1/(2(KdF+1)))`.

    HONEST: this is the LOCAL (short-interval) fundamental solution — the operator-normed PL
    instantiation that is the main cost.  It does NOT reach `Φ_v(1)` (that needs the concatenation
    continuation past the `mul_max_le` interval bound — see the section doc), NOT the localized first
    variation `HasFDerivAt exp_p (L v) v`, NOT the pullback metric, NOT numerical-G. -/
theorem expJetFund_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    ∃ T > (0 : ℝ), ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) T) t := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  set T : ℝ := min 1 (1 / (2 * (KdF + 1))) with hTdef
  have hT0 : 0 < T := lt_min one_pos (by positivity)
  have hTle1 : T ≤ 1 := min_le_left _ _
  have hTle2 : T ≤ 1 / (2 * (KdF + 1)) := min_le_right _ _
  -- the ℝ≥0 parameters of the Picard–Lindelöf structure.
  set Lnn : NNReal := ⟨2 * KdF, by linarith⟩ with hLnn
  set Knn : NNReal := ⟨KdF, hKdF0⟩ with hKnn
  have hIccsub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc_right hTle1
  -- assemble `IsPicardLindelof` for the operator field on `[0, T]`, centred at the identity.
  have hpl : IsPicardLindelof (expJetPsi g gi hC p v)
      (tmin := (0 : ℝ)) (tmax := T) ⟨0, ⟨le_refl 0, hT0.le⟩⟩
      (ContinuousLinearMap.id ℝ (Point n × Point n)) 1 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `M` on `closedBall(1,1)` with constant `KdF`.
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      calc ‖expJetPsi g gi hC p v t M - expJetPsi g gi hC p v t N‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            expJetPsi_norm_sub_le g gi hC p v t M N
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `M`.
      intro M _
      exact (expJetPsi_continuousOn g gi hC p v hv M).mono hIccsub
    · -- uniform bound `‖Ψ_v t M‖ ≤ 2·KdF` on `closedBall(1,1)`.
      intro t ht M hM
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hMid : ‖M - ContinuousLinearMap.id ℝ (Point n × Point n)‖ ≤ 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hM
      have hMnorm : ‖M‖ ≤ 2 := by
        have hsplit : M = (M - ContinuousLinearMap.id ℝ (Point n × Point n))
            + ContinuousLinearMap.id ℝ (Point n × Point n) := by abel
        calc ‖M‖ = ‖(M - ContinuousLinearMap.id ℝ (Point n × Point n))
              + ContinuousLinearMap.id ℝ (Point n × Point n)‖ := by rw [← hsplit]
          _ ≤ ‖M - ContinuousLinearMap.id ℝ (Point n × Point n)‖
              + ‖ContinuousLinearMap.id ℝ (Point n × Point n)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add hMid ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      have hbnd : ‖expJetPsi g gi hC p v t M‖ ≤ KdF * 2 :=
        (expJetPsi_norm_le g gi hC p v t M).trans
          (mul_le_mul (hKdF t htIcc) hMnorm (norm_nonneg _) hKdF0)
      show ‖expJetPsi g gi hC p v t M‖ ≤ 2 * KdF
      linarith [hbnd]
    · -- the interval constraint `2·KdF·T ≤ 1`.
      show (Lnn : ℝ) * max (T - ((⟨0, ⟨le_refl 0, hT0.le⟩⟩ : Set.Icc (0 : ℝ) T) : ℝ))
          (((⟨0, ⟨le_refl 0, hT0.le⟩⟩ : Set.Icc (0 : ℝ) T) : ℝ) - 0) ≤ (1 : NNReal) - (0 : NNReal)
      simp only [hLnn, NNReal.coe_one, NNReal.coe_zero, sub_zero, sub_self,
        max_eq_left hT0.le]
      have h2 : (0 : ℝ) < 2 * (KdF + 1) := by positivity
      calc 2 * KdF * T ≤ 2 * KdF * (1 / (2 * (KdF + 1))) :=
            mul_le_mul_of_nonneg_left hTle2 (by positivity)
        _ ≤ 1 := by rw [mul_one_div, div_le_one h2]; nlinarith [hKdF0]
  obtain ⟨Φ, hΦ0, hΦd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨T, hT0, Φ, hΦ0, hΦd⟩

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b (concatenation building block) — the shifted normalized local propagator `U_j`.**
    For a uniform Jacobi bound `KdF` on `[0,1]` (threaded externally so ONE `N` fixes the step) and any
    subinterval `[t₀, t₀+T] ⊆ [0,1]` whose width satisfies `2·KdF·T ≤ 1`, there is an operator-valued
    curve `Φ : ℝ → (State →L State)` with `Φ t₀ = 1` (identity) solving the linearized Jacobi ODE
    `Φ' t = Ψ_v t (Φ t) = DF(Y_v t) ∘ Φ t` on `[t₀, t₀+T]`, built by the FULL operator-normed
    `IsPicardLindelof` instantiation centred at the identity on `closedBall(1,1)`.

    This is the NORMALIZED propagator `U_j` (`U_j(τ_j)=1`, stays in the FIXED ball `closedBall(1,1)`,
    so the field bound is `‖A_v∘U‖ ≤ KdF·(1+1) = 2·KdF` and the interval room `2·KdF·T ≤ 1` holds with
    a fixed step) of the `[0,1]` concatenation route: pick `N` with `2(KdF+1) ≤ N`, `h := 1/N`,
    `τ j := j/N`, and every `[τ_j, τ_{j+1}]` is such a propagator.  `expJetFund_local` is the `t₀ = 0`
    special case.

    HONEST: the normalized local propagator on ONE subinterval — the reusable brick of the `[0,1]`
    concatenation (the gluing `M_{j+1} := U_j(τ_{j+1})∘M_j`, `seg_j := U_j∘M_j`, global integral
    equation by induction + FTC remains the checkpointed step); it does NOT yet reach `Φ_v(1)`, NOT the
    localized first variation, NOT the pullback metric, NOT numerical-G. -/
theorem expJetFund_shifted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1)
    (hstep : 2 * KdF * T ≤ 1) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ t₀ = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc t₀ (t₀ + T)) t := by
  set Lnn : NNReal := ⟨2 * KdF, by linarith⟩ with hLnn
  set Knn : NNReal := ⟨KdF, hKdF0⟩ with hKnn
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hpl : IsPicardLindelof (expJetPsi g gi hC p v)
      (tmin := t₀) (tmax := t₀ + T) ⟨t₀, ⟨le_refl t₀, by linarith⟩⟩
      (ContinuousLinearMap.id ℝ (Point n × Point n)) 1 0 Lnn Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lipschitz in `M` on `closedBall(1,1)` with constant `KdF`.
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro M _ N _
      simp only [dist_eq_norm, hKnn]
      calc ‖expJetPsi g gi hC p v t M - expJetPsi g gi hC p v t N‖
          ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ * ‖M - N‖ :=
            expJetPsi_norm_sub_le g gi hC p v t M N
        _ ≤ KdF * ‖M - N‖ := mul_le_mul_of_nonneg_right (hKdF t htIcc) (norm_nonneg _)
    · -- continuity in `t` for fixed `M`.
      intro M _
      exact (expJetPsi_continuousOn g gi hC p v hv M).mono hIccsub
    · -- uniform bound `‖Ψ_v t M‖ ≤ 2·KdF` on `closedBall(1,1)`.
      intro t ht M hM
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := hIccsub ht
      have hMid : ‖M - ContinuousLinearMap.id ℝ (Point n × Point n)‖ ≤ 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hM
      have hMnorm : ‖M‖ ≤ 2 := by
        have hsplit : M = (M - ContinuousLinearMap.id ℝ (Point n × Point n))
            + ContinuousLinearMap.id ℝ (Point n × Point n) := by abel
        calc ‖M‖ = ‖(M - ContinuousLinearMap.id ℝ (Point n × Point n))
              + ContinuousLinearMap.id ℝ (Point n × Point n)‖ := by rw [← hsplit]
          _ ≤ ‖M - ContinuousLinearMap.id ℝ (Point n × Point n)‖
              + ‖ContinuousLinearMap.id ℝ (Point n × Point n)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add hMid ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      have hbnd : ‖expJetPsi g gi hC p v t M‖ ≤ KdF * 2 :=
        (expJetPsi_norm_le g gi hC p v t M).trans
          (mul_le_mul (hKdF t htIcc) hMnorm (norm_nonneg _) hKdF0)
      show ‖expJetPsi g gi hC p v t M‖ ≤ 2 * KdF
      linarith [hbnd]
    · -- the interval constraint `2·KdF·T ≤ 1`.
      show (Lnn : ℝ) * max ((t₀ + T) - ((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ :
              Set.Icc t₀ (t₀ + T)) : ℝ))
          (((⟨t₀, ⟨le_refl t₀, by linarith⟩⟩ : Set.Icc t₀ (t₀ + T)) : ℝ) - t₀)
            ≤ (1 : NNReal) - (0 : NNReal)
      have hmax : max ((t₀ + T) - t₀) (t₀ - t₀) = T := by
        rw [sub_self, show (t₀ + T) - t₀ = T by ring, max_eq_left hT.le]
      simp only [hLnn, NNReal.coe_one, NNReal.coe_zero, sub_zero]
      rw [hmax]
      show 2 * KdF * T ≤ (1 : ℝ)
      exact hstep
  obtain ⟨Φ, hΦ0, hΦd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Φ, hΦ0, hΦd⟩

set_option maxHeartbeats 1000000 in
/-- **EXP-JET3b — the shifted normalized local propagator in INTEGRAL form (the gluing brick).**
    Same hypotheses as `expJetFund_shifted`, additionally packaging the normalized propagator `U_j` on
    `[t₀, t₀+T]` with (i) `U_j(t₀) = 1`, (ii) continuity on the interval, (iii) the differential law
    `U_j' = Ψ_v U_j`, and — the piece the `[0,1]` concatenation actually consumes — (iv) the LOCAL
    INTEGRAL EQUATION `U_j(t) = 1 + ∫_{t₀}^t Ψ_v(s)(U_j s) ds`, obtained from (iii) by FTC-2
    (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, integrand continuous by
    `ContinuousOn.clm_comp`).

    The `[0,1]` fundamental solution then glues these by right multiplication `M_{j+1} := U_j(τ_{j+1})∘M_j`,
    `seg_j := U_j∘M_j` (which inherits (iv) shifted by `M_j` because right-composition commutes with the
    integral, `ContinuousLinearMap.integral_comp_comm`), and proves the GLOBAL integral equation
    `Φ_v(t) = 1 + ∫_0^t Ψ_v(s)(Φ_v s) ds` on `[0, τ_j]` by induction on `j`
    (`intervalIntegral.integral_add_adjacent_intervals` + `intervalIntegral.integral_congr`), then FTC
    on `[0,1]`.  That induction + the first-variation Grönwall is the remaining EXP-JET3b work.

    HONEST: still ONE subinterval — the local integral equation that the global gluing consumes; it does
    NOT yet reach `Φ_v(1)`, NOT the localized first variation, NOT the pullback metric, NOT numerical-G. -/
theorem expJetFund_shifted_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (t₀ T : ℝ) (ht₀ : 0 ≤ t₀) (hT : 0 < T) (hsum : t₀ + T ≤ 1)
    (hstep : 2 * KdF * T ≤ 1) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ t₀ = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      ContinuousOn Φ (Set.Icc t₀ (t₀ + T)) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc t₀ (t₀ + T)) t) ∧
      (∀ t ∈ Set.Icc t₀ (t₀ + T),
        Φ t = ContinuousLinearMap.id ℝ (Point n × Point n)
          + ∫ s in t₀..t, expJetPsi g gi hC p v s (Φ s)) := by
  obtain ⟨Φ, hΦ0, hΦd⟩ :=
    expJetFund_shifted g gi hC p v hv KdF hKdF0 hKdF t₀ T ht₀ hT hsum hstep
  have hIccsub : Set.Icc t₀ (t₀ + T) ⊆ Set.Icc (0 : ℝ) 1 := Set.Icc_subset_Icc ht₀ hsum
  have hΦcont : ContinuousOn Φ (Set.Icc t₀ (t₀ + T)) := fun s hs => (hΦd s hs).continuousWithinAt
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) (Set.Icc t₀ (t₀ + T)) :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hIccsub
  have hintegrand : ContinuousOn (fun s => expJetPsi g gi hC p v s (Φ s))
      (Set.Icc t₀ (t₀ + T)) := by
    have hcc : ContinuousOn
        (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)).comp (Φ s))
        (Set.Icc t₀ (t₀ + T)) := hDFtube.clm_comp hΦcont
    simpa only [expJetPsi_apply] using hcc
  refine ⟨Φ, hΦ0, hΦcont, hΦd, fun t ht => ?_⟩
  have hab : t₀ ≤ t := ht.1
  have hsubt : Set.Icc t₀ t ⊆ Set.Icc t₀ (t₀ + T) := Set.Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn Φ (Set.Icc t₀ t) := hΦcont.mono hsubt
  have hderiv : ∀ x ∈ Set.Ioo t₀ t,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v x (Φ x)) (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc t₀ (t₀ + T) := hsubt ⟨hx.1.le, hx.2.le⟩
    have hnhds : Set.Icc t₀ (t₀ + T) ∈ nhds x :=
      Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 ht.2)
    exact ((hΦd x hxIcc).hasDerivAt hnhds).hasDerivWithinAt
  have hint : IntervalIntegrable (fun s => expJetPsi g gi hC p v s (Φ s))
      MeasureTheory.volume t₀ t := (hintegrand.mono hsubt).intervalIntegrable_of_Icc hab
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  rw [hΦ0] at hftc
  rw [hftc]; abel

/-! ### EXP-JET3b (STEP A) — the `[0,1]` operator-valued fundamental solution `Φ_v`

  Concatenating `N` shifted normalized propagators (`expJetFund_shifted_integral`) into a single
  `[0,1]` operator-valued curve `Φ_v` obeying the GLOBAL integral equation
  `Φ_v t = 1 + ∫₀ᵗ Ψ_v s (Φ_v s) ds`, from which FTC-1 gives the derivative law
  `HasDerivWithinAt Φ_v (Ψ_v t (Φ_v t)) (Icc 0 1) t` on all of `[0,1]` (junctions automatic).

  The construction is a finite induction on the partition `τ j = j/N` (step `h = 1/N`,
  `N ≥ 2(KdF+1)` so each subinterval has `2·KdF·h ≤ 1`): the glued curve on `[0,τ_{j+1}]` is
  `Φ_{j+1}(t) = if t ≤ τ_j then Φ_j t else U_j(t) ∘ Φ_j(τ_j)`, and the global integral equation is
  pasted from the sub-interval one via `integral_add_adjacent_intervals` + `integral_congr` +
  right-composition/integral commutation (`ContinuousLinearMap.intervalIntegral_comp_comm`).

  HONEST CAPTION (binding): the `[0,1]` fundamental solution `Φ_v` — a step toward the localized
  first variation `HasFDerivAt exp_p (L v) v` (EXP-JET3), itself a step toward discharging `hgauge`.
  It does NOT yet give the first variation, NOT the Jacobian 2-jet expansion, NOT the pullback metric,
  and does NOT move numerical-G (species count `N`, granularity scale `Λ_s`, the `E/ξ` term remain). -/

/-- **Continuity of the operator integrand** `s ↦ Ψ_v s (Φ s)` on any `A ⊆ [0,1]` where `Φ` is
    continuous: `DF(Y_v ·)` is continuous on `[0,1]` and right-composition is continuous
    (`ContinuousOn.clm_comp`). -/
theorem expJetPsi_comp_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) {A : Set ℝ} (hA : A ⊆ Set.Icc (0 : ℝ) 1)
    {Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))} (hΦ : ContinuousOn Φ A) :
    ContinuousOn (fun s => expJetPsi g gi hC p v s (Φ s)) A := by
  have hdFcont : Continuous (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).continuous_fderiv (by simp)
  have hDFtube : ContinuousOn
      (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) A :=
    (hdFcont.comp_continuousOn (expTube_continuousOn g gi hC p v hv)).mono hA
  have hcc := hDFtube.clm_comp hΦ
  simpa only [expJetPsi_apply] using hcc

set_option maxHeartbeats 2000000 in
/-- **The partition induction (concatenation gluing).**  For a `[0,1]`-uniform Jacobi bound `KdF`
    and a step count `N` with `2·KdF·(1/N) ≤ 1`, there is, for every `j ≤ N`, an operator-valued
    curve `Φ` on `[0, j/N]` with `Φ 0 = 1`, continuous, obeying the GLOBAL integral equation
    `Φ t = 1 + ∫₀ᵗ Ψ_v s (Φ s) ds`.  Proved by induction on `j`: the `[0, (j+1)/N]` curve glues
    `Φ_j` and the shifted propagator `U_j` on `[j/N, (j+1)/N]` by right-composition with `Φ_j(j/N)`. -/
private theorem expJetFund_glue (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p)
    (KdF : ℝ) (hKdF0 : 0 ≤ KdF)
    (hKdF : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ KdF)
    (N : ℕ) (hN0 : 0 < N) (hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1) :
    ∀ j : ℕ, j ≤ N →
      ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
        Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
        ContinuousOn Φ (Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ))) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((j : ℝ) / (N : ℝ)),
          Φ t = ContinuousLinearMap.id ℝ (Point n × Point n)
            + ∫ s in (0 : ℝ)..t, expJetPsi g gi hC p v s (Φ s)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun _ => ContinuousLinearMap.id ℝ (Point n × Point n), rfl, continuousOn_const, ?_⟩
    intro t ht
    have h0 : ((0 : ℕ) : ℝ) / (N : ℝ) = 0 := by rw [Nat.cast_zero, zero_div]
    rw [h0] at ht
    have htz : t = 0 := le_antisymm ht.2 ht.1
    subst htz
    simp only [intervalIntegral.integral_same, add_zero]
  | succ k ih =>
    intro hk
    obtain ⟨Φj, hΦj0, hΦjcont, hΦjint⟩ := ih (Nat.le_of_succ_le hk)
    have hτnn : 0 ≤ (k : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg k) hNpos.le
    have hInpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hsucc : ((k + 1 : ℕ) : ℝ) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
      push_cast; ring
    have hτk1le1 : (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) ≤ 1 :=
      hsucc ▸ (by rw [div_le_one hNpos]; exact_mod_cast hk)
    obtain ⟨U, hU0, hUcont, hUderiv, hUint⟩ :=
      expJetFund_shifted_integral g gi hC p v hv KdF hKdF0 hKdF
        ((k : ℝ) / (N : ℝ)) (1 / (N : ℝ)) hτnn hInpos hτk1le1 hstep
    set Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
      fun t => if t ≤ (k : ℝ) / (N : ℝ) then Φj t
        else (U t).comp (Φj ((k : ℝ) / (N : ℝ))) with hΦ'def
    have hΦ'_lo : ∀ s, s ≤ (k : ℝ) / (N : ℝ) → Φ' s = Φj s := by
      intro s hs; rw [hΦ'def]; exact if_pos hs
    have hΦ'_hi : ∀ s, ¬ (s ≤ (k : ℝ) / (N : ℝ)) →
        Φ' s = (U s).comp (Φj ((k : ℝ) / (N : ℝ))) := by
      intro s hs; rw [hΦ'def]; exact if_neg hs
    -- EqOn on the two closed pieces
    have hEqLo : Set.EqOn Φ' Φj (Set.Icc (0 : ℝ) ((k : ℝ) / (N : ℝ))) :=
      fun s hs => hΦ'_lo s hs.2
    have hEqHi : Set.EqOn Φ' (fun t => (U t).comp (Φj ((k : ℝ) / (N : ℝ))))
        (Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      intro s hs
      by_cases hsle : s ≤ (k : ℝ) / (N : ℝ)
      · have hseq : s = (k : ℝ) / (N : ℝ) := le_antisymm hsle hs.1
        rw [hΦ'_lo s hsle, hseq]
        show Φj ((k : ℝ) / (N : ℝ))
          = (U ((k : ℝ) / (N : ℝ))).comp (Φj ((k : ℝ) / (N : ℝ)))
        rw [hU0, ContinuousLinearMap.id_comp]
      · rw [hΦ'_hi s hsle]
    -- continuity of the glued curve on [0, (k+1)/N]
    have hUcomp : ContinuousOn (fun t => (U t).comp (Φj ((k : ℝ) / (N : ℝ))))
        (Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      hUcont.clm_comp continuousOn_const
    have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))) := by
      have hunion : Set.Icc (0 : ℝ) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))
          = Set.Icc (0 : ℝ) ((k : ℝ) / (N : ℝ))
            ∪ Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
        (Set.Icc_union_Icc_eq_Icc hτnn (by linarith)).symm
      rw [hunion]
      exact (hΦjcont.congr hEqLo).union_of_isClosed (hUcomp.congr hEqHi)
        isClosed_Icc isClosed_Icc
    -- integrand continuity for interval integrability
    have hcontψ' : ContinuousOn (fun s => expJetPsi g gi hC p v s (Φ' s))
        (Set.Icc (0 : ℝ) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
      expJetPsi_comp_continuousOn g gi hC p v hv
        (Set.Icc_subset_Icc_right hτk1le1) hΦ'cont
    rw [hsucc]
    refine ⟨Φ', ?_, hΦ'cont, ?_⟩
    · rw [hΦ'_lo 0 hτnn]; exact hΦj0
    · intro t ht
      by_cases htle : t ≤ (k : ℝ) / (N : ℝ)
      · -- t in [0, τk]: the curve is Φj there
        rw [hΦ'_lo t htle]
        have hcong : (∫ s in (0 : ℝ)..t, expJetPsi g gi hC p v s (Φ' s))
            = ∫ s in (0 : ℝ)..t, expJetPsi g gi hC p v s (Φj s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ht.1] at hs
          show expJetPsi g gi hC p v s (Φ' s) = expJetPsi g gi hC p v s (Φj s)
          rw [hΦ'_lo s (le_trans hs.2 htle)]
        rw [hcong]
        exact hΦjint t ⟨ht.1, htle⟩
      · -- t in (τk, τk + 1/N]: the curve is U(t) ∘ Φj(τk)
        have htlt : (k : ℝ) / (N : ℝ) < t := not_le.mp htle
        have htmem : t ∈ Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
          ⟨htlt.le, ht.2⟩
        rw [hΦ'_hi t htle]
        -- integrability on the two adjacent pieces
        have hII1 : IntervalIntegrable (fun s => expJetPsi g gi hC p v s (Φ' s))
            MeasureTheory.volume 0 ((k : ℝ) / (N : ℝ)) :=
          (hcontψ'.mono (Set.Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc hτnn
        have hII2 : IntervalIntegrable (fun s => expJetPsi g gi hC p v s (Φ' s))
            MeasureTheory.volume ((k : ℝ) / (N : ℝ)) t :=
          (hcontψ'.mono (Set.Icc_subset_Icc hτnn ht.2)).intervalIntegrable_of_Icc htlt.le
        have hsplit : (∫ s in (0 : ℝ)..t, expJetPsi g gi hC p v s (Φ' s))
            = (∫ s in (0 : ℝ)..((k : ℝ) / (N : ℝ)), expJetPsi g gi hC p v s (Φ' s))
              + ∫ s in ((k : ℝ) / (N : ℝ))..t, expJetPsi g gi hC p v s (Φ' s) :=
          (intervalIntegral.integral_add_adjacent_intervals hII1 hII2).symm
        -- first piece = Φj(τk) - 1
        have hI1 : (∫ s in (0 : ℝ)..((k : ℝ) / (N : ℝ)), expJetPsi g gi hC p v s (Φ' s))
            = Φj ((k : ℝ) / (N : ℝ)) - ContinuousLinearMap.id ℝ (Point n × Point n) := by
          have hc : (∫ s in (0 : ℝ)..((k : ℝ) / (N : ℝ)), expJetPsi g gi hC p v s (Φ' s))
              = ∫ s in (0 : ℝ)..((k : ℝ) / (N : ℝ)), expJetPsi g gi hC p v s (Φj s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le hτnn] at hs
            show expJetPsi g gi hC p v s (Φ' s) = expJetPsi g gi hC p v s (Φj s)
            rw [hΦ'_lo s hs.2]
          rw [hc, hΦjint ((k : ℝ) / (N : ℝ)) ⟨hτnn, le_refl _⟩]; abel
        -- second piece = U(t) ∘ Φj(τk) - Φj(τk)
        set RM : ((Point n × Point n) →L[ℝ] (Point n × Point n))
            →L[ℝ] ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
          (ContinuousLinearMap.compL ℝ (Point n × Point n) (Point n × Point n)
            (Point n × Point n)).flip (Φj ((k : ℝ) / (N : ℝ))) with hRM
        have hcontU : ContinuousOn (fun s => expJetPsi g gi hC p v s (U s))
            (Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ))) :=
          expJetPsi_comp_continuousOn g gi hC p v hv
            (Set.Icc_subset_Icc hτnn hτk1le1) hUcont
        have hII_U : IntervalIntegrable (fun s => expJetPsi g gi hC p v s (U s))
            MeasureTheory.volume ((k : ℝ) / (N : ℝ)) t :=
          (hcontU.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc htlt.le
        have hI2 : (∫ s in ((k : ℝ) / (N : ℝ))..t, expJetPsi g gi hC p v s (Φ' s))
            = (U t).comp (Φj ((k : ℝ) / (N : ℝ))) - Φj ((k : ℝ) / (N : ℝ)) := by
          have hc : (∫ s in ((k : ℝ) / (N : ℝ))..t, expJetPsi g gi hC p v s (Φ' s))
              = ∫ s in ((k : ℝ) / (N : ℝ))..t, RM (expJetPsi g gi hC p v s (U s)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [Set.uIcc_of_le htlt.le] at hs
            have hsmem : s ∈ Set.Icc ((k : ℝ) / (N : ℝ)) ((k : ℝ) / (N : ℝ) + 1 / (N : ℝ)) :=
              ⟨hs.1, le_trans hs.2 ht.2⟩
            show expJetPsi g gi hC p v s (Φ' s)
              = RM (expJetPsi g gi hC p v s (U s))
            rw [hEqHi hsmem]
            show (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)).comp
                ((U s).comp (Φj ((k : ℝ) / (N : ℝ))))
              = RM ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)).comp (U s))
            rw [hRM, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
            exact (ContinuousLinearMap.comp_assoc _ _ _).symm
          rw [hc, RM.intervalIntegral_comp_comm hII_U,
            show (∫ s in ((k : ℝ) / (N : ℝ))..t, expJetPsi g gi hC p v s (U s))
                = U t - ContinuousLinearMap.id ℝ (Point n × Point n) from by
              rw [hUint t htmem]; abel, hRM,
            ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
            ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
        rw [hsplit, hI1, hI2]; abel

set_option maxHeartbeats 2000000 in
/-- **EXP-JET3b (STEP A) — the `[0,1]` operator-valued fundamental solution `Φ_v`.**  For
    `‖v‖ ≤ expRho` there is an operator-valued curve `Φ_v : ℝ → (State →L State)` with `Φ_v 0 = 1`,
    continuous on `[0,1]`, obeying the GLOBAL integral equation
    `Φ_v t = 1 + ∫₀ᵗ Ψ_v s (Φ_v s) ds` on `[0,1]`, and — by FTC-1 — the derivative law
    `HasDerivWithinAt Φ_v (Ψ_v t (Φ_v t)) (Icc 0 1) t` for every `t ∈ [0,1]`.  Built by
    concatenating `N ≥ 2(KdF+1)` shifted normalized propagators (`expJetFund_glue`).

    HONEST: the `[0,1]` fundamental solution — a step toward the localized first variation
    `HasFDerivAt exp_p (L v) v` (EXP-JET3).  It does NOT yet give the first variation, NOT the
    Jacobian 2-jet expansion, NOT the pullback metric, NOT numerical-G. -/
theorem expJetFund (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      ContinuousOn Φ (Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Φ t = ContinuousLinearMap.id ℝ (Point n × Point n)
          + ∫ s in (0 : ℝ)..t, expJetPsi g gi hC p v s (Φ s)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) := by
  obtain ⟨KdF, hKdF0, hKdF⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (KdF + 1))
  have hpos : (0 : ℝ) < 2 * (KdF + 1) := by linarith
  have hNRpos : (0 : ℝ) < (N : ℝ) := hpos.trans_le hN
  have hN0 : 0 < N := by exact_mod_cast hNRpos
  have hstep : 2 * KdF * (1 / (N : ℝ)) ≤ 1 := by
    have h2 : 2 * KdF * (1 / (N : ℝ)) = (2 * KdF) / (N : ℝ) := by ring
    rw [h2, div_le_one hNRpos]; linarith [hN]
  obtain ⟨Φ, hΦ0, hΦcont, hΦint⟩ := expJetFund_glue g gi hC p v hv KdF hKdF0 hKdF N hN0 hstep N le_rfl
  have hNN : (N : ℝ) / (N : ℝ) = 1 := div_self hNRpos.ne'
  rw [hNN] at hΦcont hΦint
  refine ⟨Φ, hΦ0, hΦcont, hΦint, ?_⟩
  have hψcont : ContinuousOn (fun s => expJetPsi g gi hC p v s (Φ s)) (Set.Icc (0 : ℝ) 1) :=
    expJetPsi_comp_continuousOn g gi hC p v hv (subset_refl _) hΦcont
  intro t ht
  haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
  have hII : IntervalIntegrable (fun s => expJetPsi g gi hC p v s (Φ s))
      MeasureTheory.volume 0 t :=
    (hψcont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hmeas := hψcont.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
    measurableSet_Icc t
  have hFTC := intervalIntegral.integral_hasDerivWithinAt_right (s := Set.Icc (0 : ℝ) 1)
    hII hmeas (hψcont t ht)
  have hconst := hFTC.const_add (ContinuousLinearMap.id ℝ (Point n × Point n))
  exact hconst.congr (fun s hs => hΦint s hs) (hΦint t ht)

set_option maxHeartbeats 4000000 in
/-- **EXP-JET3b (STEP B) — the localized first variation `HasFDerivAt exp_p (L v) v`.**  For
    `‖v‖ < expRho`, the geodesic exponential map has Fréchet derivative `L v = π ∘ Φ_v(1) ∘ ι` at `v`,
    where `Φ_v` is the `[0,1]` operator-valued fundamental solution (`expJetFund`) of the Jacobi ODE
    along the tube `Y_v`.  The Jacobi field `J_k(t) = Φ_v(t)(0,k)` (`J_k 0 = (0,k)`) transports the
    first variation; the residual `R_k = (Y_{v+k} − Y_v) − J_k` obeys `R_k 0 = 0`,
    `R_k' = DF(Y_v)·R_k + N_k` with `‖N_k(t)‖ ≤ ε·‖Y_{v+k} − Y_v‖ ≤ ε·Ctw·‖k‖`
    (`geodesicField_uniform_C1_remainder` + the two-point Grönwall `geodesic_twopoint_gronwall`);
    the inhomogeneous Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) gives `‖R_k 1‖ = o(‖k‖)`,
    and `exp_p(v+k) − exp_p(v) − L v·k = π(R_k 1)` closes the little-o.

    Stated existentially in `Φ_v` (the fundamental solution is not canonically named): the derivative
    is `π ∘ Φ_v(1) ∘ ι` for THE fundamental solution `Φ_v` returned alongside.

    HONEST: the localized first variation — the genuine subtlety of EXP-JET3.  It does NOT yet give the
    full Jacobian 2-jet expansion `fderiv exp_p y = 1 + B(y,·) + …`, NOT the pullback metric, NOT
    numerical-G (`N`, `Λ_s`, `E/ξ` remain). -/
theorem hasFDerivAt_expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) (hv : ‖v‖ < expRho g gi hC p) :
    ∃ Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)),
      Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) ∧
      HasFDerivAt (expMap g gi hC p)
        (expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) v := by
  have hv_le : ‖v‖ ≤ expRho g gi hC p := hv.le
  obtain ⟨Φ, hΦ0, _hΦcont, _hΦint, hΦderiv⟩ := expJetFund g gi hC p v hv_le
  refine ⟨Φ, hΦ0, hΦderiv, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- constants: confinement, Lipschitz on a fixed convex compact ball S, the Jacobi bound KdF.
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * (‖v‖ + 1) + 1 with hRbdef
  have hRb0 : 0 ≤ Rb := by rw [hRbdef]; positivity
  obtain ⟨Ktube, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn
        (s := Metric.closedBall ((p, 0) : Point n × Point n) Rb)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨KdF, hKdF0, hKdFb⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv_le
  set Ctw : ℝ := Real.exp (Ktube : ℝ) with hCtwdef
  have hCtw0 : 0 < Ctw := Real.exp_pos _
  -- the Grönwall proportionality constant β' = gronwallBound 0 KdF 1 1 ≥ 0.
  set β' : ℝ := gronwallBound 0 KdF 1 1 with hβ'def
  have hβ'0 : 0 ≤ β' := by
    rw [hβ'def]
    rcases eq_or_ne KdF 0 with hK | hK
    · rw [hK, gronwallBound_K0]; norm_num
    · rw [gronwallBound_of_K_ne_0 hK]
      have hKpos : 0 < KdF := (hKdF0).lt_of_ne (Ne.symm hK)
      have hexp : (1 : ℝ) ≤ Real.exp (KdF * 1) := by
        rw [mul_one]; exact Real.one_le_exp hKpos.le
      have hprod : 0 ≤ 1 / KdF * (Real.exp (KdF * 1) - 1) :=
        mul_nonneg (by positivity) (by linarith)
      simpa using hprod
  set Mc : ℝ := Ctw * β' with hMcdef
  have hMc0 : 0 ≤ Mc := by rw [hMcdef]; exact mul_nonneg hCtw0.le hβ'0
  set ε : ℝ := c / (Mc + 1) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hc (by linarith)
  have hεMc : ε * Mc ≤ c := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < Mc + 1)]
    nlinarith [hc, hMc0]
  -- the uniform C¹ remainder of the field on S.
  obtain ⟨δε, hδε0, hδεb⟩ := geodesicField_uniform_C1_remainder g gi hC
    (convex_closedBall ((p, 0) : Point n × Point n) Rb)
    (isCompact_closedBall ((p, 0) : Point n × Point n) Rb) hεpos
  -- the eventual neighbourhood radius for k.
  set ρ : ℝ := min (expRho g gi hC p - ‖v‖) (min 1 (δε / Ctw)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (by linarith) (lt_min one_pos (by positivity))
  rw [Metric.eventually_nhds_iff]
  refine ⟨ρ, hρpos, ?_⟩
  intro k hk
  rw [dist_eq_norm, sub_zero] at hk
  have hk1 : ‖k‖ < expRho g gi hC p - ‖v‖ := lt_of_lt_of_le hk (by rw [hρdef]; exact min_le_left _ _)
  have hk2 : ‖k‖ ≤ 1 :=
    (lt_of_lt_of_le hk (by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _))).le
  have hk3 : ‖k‖ < δε / Ctw :=
    lt_of_lt_of_le hk (by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hkCtw : ‖k‖ * Ctw < δε := (lt_div_iff₀ hCtw0).mp hk3
  have hvk_le : ‖v + k‖ ≤ expRho g gi hC p :=
    le_of_lt (lt_of_le_of_lt (norm_add_le v k) (by linarith))
  -- the two confined tubes.
  obtain ⟨hY0v, hderivv, hconfv⟩ := expTube_spec g gi hC p v hv_le
  obtain ⟨hY0vk, hderivvk, hconfvk⟩ := expTube_spec g gi hC p (v + k) hvk_le
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- both tubes lie in S on [0,1].
  have hSv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      expTube g gi hC p v t ∈ Metric.closedBall ((p, 0) : Point n × Point n) Rb := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconfv t ht
      _ ≤ Rb := by rw [hRbdef]; nlinarith [hC₀, norm_nonneg v]
  have hSvk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      expTube g gi hC p (v + k) t ∈ Metric.closedBall ((p, 0) : Point n × Point n) Rb := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p (v + k) t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v + k‖ := hconfvk t ht
      _ ≤ expConst g gi hC p * (‖v‖ + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC₀
          calc ‖v + k‖ ≤ ‖v‖ + ‖k‖ := norm_add_le v k
            _ ≤ ‖v‖ + 1 := by linarith
      _ ≤ Rb := by rw [hRbdef]; linarith
  -- two-point Grönwall separation bound ‖Y_{v+k} − Y_v‖ ≤ ‖k‖·Ctw on [0,1].
  have hdist0 : dist (expTube g gi hC p (v + k) 0) (expTube g gi hC p v 0) = ‖k‖ := by
    rw [hY0vk, hY0v, dist_eq_norm, Prod.mk_sub_mk, sub_self, add_sub_cancel_left,
      Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) Rb) (K := Ktube) hLip
      (fun t ht => hderivvk t (hIcc_Ioo t ht)) (fun t ht => hderivv t (hIcc_Ioo t ht)) hSvk hSv
  have htwo : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖ ≤ ‖k‖ * Ctw := by
    intro t ht
    have h := htwopoint t ht
    rw [hdist0, dist_eq_norm] at h
    have hexple : Real.exp ((Ktube : ℝ) * t) ≤ Ctw := by
      rw [hCtwdef]; apply Real.exp_le_exp.mpr
      calc (Ktube : ℝ) * t ≤ (Ktube : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        _ = (Ktube : ℝ) := mul_one _
    calc ‖expTube g gi hC p (v + k) t - expTube g gi hC p v t‖
        ≤ ‖k‖ * Real.exp ((Ktube : ℝ) * t) := h
      _ ≤ ‖k‖ * Ctw := mul_le_mul_of_nonneg_left hexple (norm_nonneg _)
  -- the Jacobi field J_k(t) = Φ_v(t)(0,k), solving J' = DF(Y_v)·J.
  have hJderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun τ => Φ τ ((0, k) : Point n × Point n))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t ((0, k) : Point n × Point n)))
        (Set.Icc 0 1) t := by
    intro t ht
    have h := (hΦderiv t ht).clm_apply
      (hasDerivAt_const t ((0, k) : Point n × Point n)).hasDerivWithinAt
    simpa only [expJetPsi_apply, ContinuousLinearMap.comp_apply, map_zero, add_zero] using h
  -- the residual R_k = (Y_{v+k} − Y_v) − J_k.
  set R : ℝ → Point n × Point n :=
    fun τ => expTube g gi hC p (v + k) τ - expTube g gi hC p v τ - Φ τ ((0, k) : Point n × Point n)
    with hRdef
  have hR0 : R 0 = 0 := by
    simp only [hRdef]
    rw [hY0vk, hY0v, hΦ0, ContinuousLinearMap.id_apply]
    simp [Prod.mk_sub_mk]
  have hRderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (R t)
          + (geodesicField g gi (expTube g gi hC p (v + k) t)
              - geodesicField g gi (expTube g gi hC p v t)
              - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
                  (expTube g gi hC p (v + k) t - expTube g gi hC p v t)))
        (Set.Icc 0 1) t := by
    intro t ht
    have hd_vk : HasDerivWithinAt (expTube g gi hC p (v + k))
        (geodesicField g gi (expTube g gi hC p (v + k) t)) (Set.Icc 0 1) t :=
      (hderivvk t (hIcc_Ioo t ht)).hasDerivWithinAt
    have hd_v : HasDerivWithinAt (expTube g gi hC p v)
        (geodesicField g gi (expTube g gi hC p v t)) (Set.Icc 0 1) t :=
      (hderivv t (hIcc_Ioo t ht)).hasDerivWithinAt
    have hbase := (hd_vk.sub hd_v).sub (hJderiv t ht)
    have hval : geodesicField g gi (expTube g gi hC p (v + k) t)
          - geodesicField g gi (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (Φ t ((0, k) : Point n × Point n))
        = fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (R t)
          + (geodesicField g gi (expTube g gi hC p (v + k) t)
              - geodesicField g gi (expTube g gi hC p v t)
              - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
                  (expTube g gi hC p (v + k) t - expTube g gi hC p v t)) := by
      rw [hRdef]
      simp only [map_sub]
      abel
    rw [hval] at hbase
    exact hbase
  -- the inhomogeneous residual Grönwall.
  have hRcont : ContinuousOn R (Set.Icc 0 1) :=
    fun t ht => (hRderiv t ht).continuousWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x) (R x)
        + (geodesicField g gi (expTube g gi hC p (v + k) x)
            - geodesicField g gi (expTube g gi hC p v x)
            - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)
                (expTube g gi hC p (v + k) x - expTube g gi hC p v x))‖
      ≤ KdF * ‖R x‖ + ε * Ctw * ‖k‖ := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
    have hlt : ‖expTube g gi hC p (v + k) x - expTube g gi hC p v x‖ < δε :=
      lt_of_le_of_lt (htwo x hxIcc) hkCtw
    have hNk := hδεb (expTube g gi hC p (v + k) x) (hSvk x hxIcc)
      (expTube g gi hC p v x) (hSv x hxIcc) hlt
    have hDFbound : ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x) (R x)‖
        ≤ KdF * ‖R x‖ :=
      le_trans ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)).le_opNorm (R x))
        (mul_le_mul_of_nonneg_right (hKdFb x hxIcc) (norm_nonneg _))
    calc ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x) (R x)
            + (geodesicField g gi (expTube g gi hC p (v + k) x)
                - geodesicField g gi (expTube g gi hC p v x)
                - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)
                    (expTube g gi hC p (v + k) x - expTube g gi hC p v x))‖
        ≤ ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x) (R x)‖
          + ‖geodesicField g gi (expTube g gi hC p (v + k) x)
              - geodesicField g gi (expTube g gi hC p v x)
              - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v x)
                  (expTube g gi hC p (v + k) x - expTube g gi hC p v x)‖ := norm_add_le _ _
      _ ≤ KdF * ‖R x‖ + ε * (‖k‖ * Ctw) :=
          add_le_add hDFbound (le_trans hNk (mul_le_mul_of_nonneg_left (htwo x hxIcc) hεpos.le))
      _ = KdF * ‖R x‖ + ε * Ctw * ‖k‖ := by ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := R)
    (f' := fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t) (R t)
        + (geodesicField g gi (expTube g gi hC p (v + k) t)
            - geodesicField g gi (expTube g gi hC p v t)
            - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
                (expTube g gi hC p (v + k) t - expTube g gi hC p v t)))
    (δ := 0) (K := KdF) (ε := ε * Ctw * ‖k‖) (a := 0) (b := 1)
    hRcont
    (fun x hx => (hRderiv x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, hx.2,
        fun y hy => ⟨le_trans hx.1 hy.2, le_of_lt hy.1⟩⟩))
    (by rw [hR0]; simp)
    hbound
  have hR1 := hgron 1 (by norm_num [Set.mem_Icc])
  rw [sub_zero, gronwallBound_zero_linear, ← hβ'def] at hR1
  have hR1' : ‖R 1‖ ≤ c * ‖k‖ := by
    calc ‖R 1‖ ≤ ε * Ctw * ‖k‖ * β' := hR1
      _ = ε * Mc * ‖k‖ := by rw [hMcdef]; ring
      _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_right hεMc (norm_nonneg _)
  -- project onto the position component.
  have hproj : expMap g gi hC p (v + k) - expMap g gi hC p v
      - (expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) k = expJetPi (R 1) := by
    simp only [expMap, ContinuousLinearMap.comp_apply, expJetIota_apply, expJetPi_apply, hRdef,
      Prod.fst_sub]
  rw [hproj]
  calc ‖expJetPi (R 1)‖ = ‖(R 1).1‖ := by rw [expJetPi_apply]
    _ ≤ ‖R 1‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ c * ‖k‖ := hR1'

end QIQTH.ExpMap
