/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# HT3 brick-1 — the Klein–Gordon SYMPLECTIC FORM on Cauchy data

This is **HT3 brick-1** of `THE_HTKK_PHYSICAL_PLAN.md`: the classical Klein–Gordon symplectic
(Wronskian) form on a Cauchy slice, together with its antisymmetry, bilinearity, and time-slice
independence.  It is the FOUNDATION of the canonical KG → one-particle map `j_ℏ` (the named
frontier whose completion would turn the `hTkk` localization coefficient from a calibrated ansatz
into a Lean theorem — the physics coefficient is already known-derived; this is the formalization).

Represent a KG solution by its Cauchy data on a slice, `(ψ₀, π₀) : (ℝ → ℝ) × (ℝ → ℝ)` (field +
its time-derivative).  The KG symplectic form between data `(ψ₀, π₀)` and `(χ₀, ρ₀)` is

    σ((ψ₀,π₀),(χ₀,ρ₀))  =  ∫ (ψ₀ · ρ₀ − χ₀ · π₀) dx     (`kgSympl ψ₀ π₀ χ₀ ρ₀`).

## What is proved

* `kgSympl_antisymm` — antisymmetry `σ(a,b) = −σ(b,a)` (no integrability needed; pure `integral_neg`).
* `kgSympl_add_left` / `kgSympl_smul_left` — bilinearity in the left argument (add needs integrability
  of each summand's integrand; scalar multiplication is unconditional).  The right-argument versions
  follow by antisymmetry.
* `kgSympl_density_conservation` — the KEY physics: for two KG SOLUTIONS `ψ, χ : ℝ → ℝ → ℝ` (indexed
  `(t,x)`) obeying the `1+1` wave equation `∂²_t = ∂²_x − μ` (μ = m²), the symplectic **density**
  `ψ·∂_tχ − χ·∂_tψ` has t-derivative equal to the x-derivative of the **flux** `ψ·∂_xχ − χ·∂_xψ`:
  both equal `ψ·∂²_xχ − χ·∂²_xψ`.  The `μ` (mass) terms cancel — this is the conservation law
  `∂_t(density) = ∂_x(flux)` that makes σ time-slice independent.  Fully axiom-free; the wave
  equation and regularity are carried `HasDerivAt` hypotheses, never axioms.
* `kgSympl_slice_independent` — the slice-independence capstone: given (i) the conservation physics
  above (via the carried KG equations), (ii) differentiation under the integral sign as a carried
  analytic hypothesis, and (iii) spatial decay `∫ ∂_x(flux) = 0` as a carried hypothesis, the
  symplectic form `S(t) = σ` of the time-`t` Cauchy data is INDEPENDENT of `t` (`HasDerivAt S 0 t`).
  The proof genuinely USES the KG equations (the `μ`-cancellation) to rewrite the differentiated
  integrand into the flux-derivative before the decay hypothesis kills it.

## Scope firewall (HONEST)

This is the KG symplectic form + antisymmetry/bilinearity + slice-independence — brick-1 of the
canonical `j_ℏ` (KG → one-particle) map.  It does **NOT** build `j_ℏ` (the positive-frequency
projection — the next, hard brick), **NOT** the boost-charge identity, **NOT** the `2π/ℏ` modular
coefficient, **NOT** numerical-`G`/QG.  The KG equation of motion and the spatial decay /
differentiate-under-integral steps are carried as HYPOTHESES, never axioms.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace QIQTH.KGSymplectic

open MeasureTheory

/-- **The Klein–Gordon symplectic form on Cauchy data.**

For Cauchy data `(ψ₀, π₀)` and `(χ₀, ρ₀)` (field + time-derivative on a slice), the KG symplectic
(Wronskian) form is `σ = ∫ (ψ₀ · ρ₀ − χ₀ · π₀) dx`.  This is the classical bilinear form whose
one-particle positive-frequency polarization gives the canonical map `j_ℏ` via
`2ℏ·Im⟨j_ℏψ, j_ℏχ⟩ = σ(ψ,χ)`. -/
noncomputable def kgSympl (ψ₀ π₀ χ₀ ρ₀ : ℝ → ℝ) : ℝ :=
  ∫ x, ψ₀ x * ρ₀ x - χ₀ x * π₀ x ∂(volume : Measure ℝ)

/-- **Antisymmetry** of the KG symplectic form: `σ((ψ₀,π₀),(χ₀,ρ₀)) = −σ((χ₀,ρ₀),(ψ₀,π₀))`.

No integrability hypothesis is needed: the integrand of the right-hand form is the pointwise
negation of the left, so `integral_neg` suffices. -/
theorem kgSympl_antisymm (ψ₀ π₀ χ₀ ρ₀ : ℝ → ℝ) :
    kgSympl ψ₀ π₀ χ₀ ρ₀ = - kgSympl χ₀ ρ₀ ψ₀ π₀ := by
  unfold kgSympl
  rw [← integral_neg]
  congr 1
  funext x
  ring

/-- **Left additivity (bilinearity, left argument)** of the KG symplectic form:
`σ((ψ₀+ψ₀', π₀+π₀'), (χ₀,ρ₀)) = σ((ψ₀,π₀),(χ₀,ρ₀)) + σ((ψ₀',π₀'),(χ₀,ρ₀))`.

Integrability of each summand's integrand is carried (as required by `integral_add`). -/
theorem kgSympl_add_left (ψ₀ ψ₀' π₀ π₀' χ₀ ρ₀ : ℝ → ℝ)
    (h1 : Integrable (fun x => ψ₀ x * ρ₀ x - χ₀ x * π₀ x) (volume : Measure ℝ))
    (h2 : Integrable (fun x => ψ₀' x * ρ₀ x - χ₀ x * π₀' x) (volume : Measure ℝ)) :
    kgSympl (fun x => ψ₀ x + ψ₀' x) (fun x => π₀ x + π₀' x) χ₀ ρ₀
      = kgSympl ψ₀ π₀ χ₀ ρ₀ + kgSympl ψ₀' π₀' χ₀ ρ₀ := by
  unfold kgSympl
  rw [← integral_add h1 h2]
  congr 1
  funext x
  ring

/-- **Left homogeneity (bilinearity, left argument)** of the KG symplectic form:
`σ((c·ψ₀, c·π₀), (χ₀,ρ₀)) = c · σ((ψ₀,π₀),(χ₀,ρ₀))`.

Unconditional — `integral_const_mul` needs no integrability hypothesis. -/
theorem kgSympl_smul_left (c : ℝ) (ψ₀ π₀ χ₀ ρ₀ : ℝ → ℝ) :
    kgSympl (fun x => c * ψ₀ x) (fun x => c * π₀ x) χ₀ ρ₀
      = c * kgSympl ψ₀ π₀ χ₀ ρ₀ := by
  unfold kgSympl
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- **KG symplectic-density conservation (the physics core of slice-independence).**

For two `1+1` Klein–Gordon SOLUTIONS `ψ, χ : ℝ → ℝ → ℝ` (indexed `(t,x)`) with the carried first and
second `t`- and `x`-derivatives (`ψt, ψtt, ψx, ψxx`, similarly for `χ`), all given as `HasDerivAt`
hypotheses, and each satisfying the wave equation `∂²_t = ∂²_x − μ` (`μ = m²`):

The symplectic **density** `ψ·∂_tχ − χ·∂_tψ` has, at `(t,x)`, a `t`-derivative equal to the
`x`-derivative of the symplectic **flux** `ψ·∂_xχ − χ·∂_xψ` — both equal `ψ·∂²_xχ − χ·∂²_xψ`.

Concretely, this returns the pair of `HasDerivAt` facts sharing the common value
`V = ψ·χxx − χ·ψxx`.  The mass (`μ`) terms cancel: this is precisely the conservation law
`∂_t(density) = ∂_x(flux)` behind time-slice independence of the KG symplectic form. -/
theorem kgSympl_density_conservation
    (ψ χ ψt ψtt ψx ψxx χt χtt χx χxx : ℝ → ℝ → ℝ) (μ : ℝ)
    (hψt : ∀ t x, HasDerivAt (fun s => ψ s x) (ψt t x) t)
    (hψtt : ∀ t x, HasDerivAt (fun s => ψt s x) (ψtt t x) t)
    (hχt : ∀ t x, HasDerivAt (fun s => χ s x) (χt t x) t)
    (hχtt : ∀ t x, HasDerivAt (fun s => χt s x) (χtt t x) t)
    (hψx : ∀ t x, HasDerivAt (fun y => ψ t y) (ψx t x) x)
    (hψxx : ∀ t x, HasDerivAt (fun y => ψx t y) (ψxx t x) x)
    (hχx : ∀ t x, HasDerivAt (fun y => χ t y) (χx t x) x)
    (hχxx : ∀ t x, HasDerivAt (fun y => χx t y) (χxx t x) x)
    (hKGψ : ∀ t x, ψtt t x = ψxx t x - μ * ψ t x)
    (hKGχ : ∀ t x, χtt t x = χxx t x - μ * χ t x)
    (t x : ℝ) :
    HasDerivAt (fun s => ψ s x * χt s x - χ s x * ψt s x)
        (ψ t x * χxx t x - χ t x * ψxx t x) t
      ∧ HasDerivAt (fun y => ψ t y * χx t y - χ t y * ψx t y)
        (ψ t x * χxx t x - χ t x * ψxx t x) x := by
  refine ⟨?_, ?_⟩
  · -- t-derivative of the density; the μ terms cancel via the wave equation
    have hd : HasDerivAt (fun s => ψ s x * χt s x - χ s x * ψt s x)
        ((ψt t x * χt t x + ψ t x * χtt t x) - (χt t x * ψt t x + χ t x * ψtt t x)) t :=
      ((hψt t x).mul (hχtt t x)).sub ((hχt t x).mul (hψtt t x))
    have heq : (ψt t x * χt t x + ψ t x * χtt t x) - (χt t x * ψt t x + χ t x * ψtt t x)
        = ψ t x * χxx t x - χ t x * ψxx t x := by
      rw [hKGψ t x, hKGχ t x]; ring
    rwa [heq] at hd
  · -- x-derivative of the flux; the cross terms cancel algebraically
    have hd : HasDerivAt (fun y => ψ t y * χx t y - χ t y * ψx t y)
        ((ψx t x * χx t x + ψ t x * χxx t x) - (χx t x * ψx t x + χ t x * ψxx t x)) x :=
      ((hψx t x).mul (hχxx t x)).sub ((hχx t x).mul (hψxx t x))
    have heq : (ψx t x * χx t x + ψ t x * χxx t x) - (χx t x * ψx t x + χ t x * ψxx t x)
        = ψ t x * χxx t x - χ t x * ψxx t x := by ring
    rwa [heq] at hd

/-- **Time-slice independence of the KG symplectic form (capstone).**

Let `S t = ∫ (ψ(t,·)·∂_tχ(t,·) − χ(t,·)·∂_tψ(t,·)) dx` be the KG symplectic form of the time-`t`
Cauchy data of two `1+1` KG solutions `ψ, χ`.  Given

* the wave equations `hKGψ, hKGχ` (`∂²_t = ∂²_x − μ`, the μ = m² terms cancel — the genuine physics),
* differentiation under the integral sign, carried as `hSderiv` (`S` is differentiable with derivative
  the integral of the pointwise `t`-derivative of the symplectic density), and
* spatial decay, carried as `hFlux` (the flux `ψ·∂²_xχ − χ·∂²_xψ` integrates to `0` on each slice —
  the boundary term of an FTC, exactly as in `HTkkPhysical.nullTriangle_ftc`),

the symplectic form is INDEPENDENT of `t`:  `HasDerivAt S 0 t` for all `t`.

The proof uses the carried KG equations to rewrite the differentiated density integrand into the
flux-derivative integrand (the `μ`-cancellation), whereupon the decay hypothesis makes it vanish.
HONEST: differentiate-under-integral and spatial decay are carried analytic HYPOTHESES, never
axioms; only the classical KG conservation physics is discharged here. -/
theorem kgSympl_slice_independent
    (ψ χ ψt ψtt χt χtt ψxx χxx : ℝ → ℝ → ℝ) (μ : ℝ)
    (hKGψ : ∀ t x, ψtt t x = ψxx t x - μ * ψ t x)
    (hKGχ : ∀ t x, χtt t x = χxx t x - μ * χ t x)
    (S : ℝ → ℝ)
    (hSderiv : ∀ t, HasDerivAt S
      (∫ x, (ψt t x * χt t x + ψ t x * χtt t x)
              - (χt t x * ψt t x + χ t x * ψtt t x) ∂(volume : Measure ℝ)) t)
    (hFlux : ∀ t, (∫ x, ψ t x * χxx t x - χ t x * ψxx t x ∂(volume : Measure ℝ)) = 0) :
    ∀ t, HasDerivAt S 0 t := by
  intro t
  have hfun : (fun x => (ψt t x * χt t x + ψ t x * χtt t x)
                          - (χt t x * ψt t x + χ t x * ψtt t x))
            = (fun x => ψ t x * χxx t x - χ t x * ψxx t x) := by
    funext x
    rw [hKGψ t x, hKGχ t x]; ring
  have h := hSderiv t
  rw [hfun, hFlux t] at h
  exact h

end QIQTH.KGSymplectic
