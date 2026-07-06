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

end QIQTH.ExpMap
