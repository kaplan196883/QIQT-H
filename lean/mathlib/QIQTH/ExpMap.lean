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
open Finset

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

/-- **The geodesic exponential map** `exp_p(v)` = the position at parameter `1` of the geodesic with
    initial phase point `(p, v)`.  DEFINED here as a total function; its geodesic meaning at `t=1` is
    established only for small `v` (see the scaffolding caveat above). -/
noncomputable def expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n) : Point n :=
  (geodesicSol g gi hC (p, v) 1).1

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

end QIQTH.ExpMap
