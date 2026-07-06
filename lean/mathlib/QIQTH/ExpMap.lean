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

end QIQTH.ExpMap
