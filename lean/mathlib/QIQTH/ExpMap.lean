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

end QIQTH.ExpMap
