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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Sqrt
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

/-!
## HT3 brick-2 — the FOURIER-SIDE positive-frequency coefficient theorem

This section is **HT3 brick-2** of `THE_HTKK_PHYSICAL_PLAN.md`: the algebraic core proving that
the Klein–Gordon symplectic form equals `2ℏ · Im` of the one-particle (positive-frequency) inner
product — the *canonical-normalization* property that makes the localization coefficient of the
`hTkk` map **derived**, not calibrated.

On Fourier-side Cauchy data `Ψ π Χ Ρ : ℝ → ℂ` (the spatial Fourier transforms of *real* fields, hence
**conjugate-symmetric**, `Ψ(−k) = conj(Ψ k)` etc. — carried as hypotheses), with the dispersion
`ω k = √(k²+m²)` and the positive-frequency coefficient
`a(Ψ,π) k = (ω·Ψ + i·π) / √(2ℏω)`, the theorem is

    2ℏ · (∫ conj(a(Ψ,π))·a(Χ,Ρ) dk).im  =  σ_K(Ψ,π,Χ,Ρ)  :=  (∫ (conj Ψ·Ρ − conj Χ·π) dk).re .

**Scope firewall (HONEST).**  This is the Fourier-side coefficient physics ONLY.  It does **NOT**
build the `Lp`/rapidity `j_ℏ` map (the multi-month Mathlib wall — brick-4), **NOT** the Parseval
bridge to the position-space `kgSympl` (brick-3), **NOT** the boost-charge identity, **NOT** the
`2π/ℏ` modular coefficient, **NOT** numerical-`G`/QG.  Conjugate symmetry and integrability of the
product terms are carried as HYPOTHESES, never axioms.  Pure pointwise `|a|²` algebra + evenness of
`ω` under `k ↦ −k`.
-/

open scoped ComplexConjugate

/-- **The KG one-particle dispersion** `ω_k = √(k² + m²)`. -/
noncomputable def kgOmega (m k : ℝ) : ℝ := Real.sqrt (k ^ 2 + m ^ 2)

/-- `ω_k > 0` for `m > 0`. -/
lemma kgOmega_pos (m k : ℝ) (hm : 0 < m) : 0 < kgOmega m k := by
  unfold kgOmega
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg k) (pow_pos hm 2))

/-- `ω` is **even** in `k`: `ω_{−k} = ω_k` (from `(−k)² = k²`). -/
lemma kgOmega_even (m k : ℝ) : kgOmega m (-k) = kgOmega m k := by
  unfold kgOmega; congr 1; ring

/-- **The Fourier-side positive-frequency coefficient**
`a(Ψ,π) k = (ω_k·Ψ k + i·π k) / √(2ℏ ω_k)`.  This is the one-particle annihilation amplitude of
the mode with Cauchy data `(Ψ,π)` (in the Fourier picture); its canonical `√(2ℏω)` normalization is
what the coefficient theorem below verifies against the symplectic form. -/
noncomputable def posFreqCoeff (m ℏ : ℝ) (Ψ π : ℝ → ℂ) (k : ℝ) : ℂ :=
  ((kgOmega m k : ℂ) * Ψ k + Complex.I * π k) / (Real.sqrt (2 * ℏ * kgOmega m k) : ℂ)

/-- **The Fourier symplectic pairing** `σ_K = (∫ (conj Ψ·Ρ − conj Χ·π) dk).re`. -/
noncomputable def sigmaK (Ψ π Χ Ρ : ℝ → ℂ) : ℝ :=
  (∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k) ∂(volume : Measure ℝ)).re

/-- **The Fourier "diagonal" density** `ω·(conj Ψ·Χ) + (conj π·Ρ)/ω`, whose imaginary part is the
piece that VANISHES on integration by conjugate symmetry + evenness of `ω`. -/
noncomputable def htDiag (m : ℝ) (Ψ π Χ Ρ : ℝ → ℂ) (k : ℝ) : ℂ :=
  (kgOmega m k : ℂ) * (starRingEnd ℂ (Ψ k) * Χ k)
    + starRingEnd ℂ (π k) * Ρ k / (kgOmega m k : ℂ)

/-- An **odd real integrand integrates to zero** on `(ℝ, volume)`: if `g(−x) = −g x` then
`∫ g = 0`.  Proof: `volume` is `neg`-invariant (`measurePreserving_neg`), so `∫ g(−·) = ∫ g`, while
oddness gives `∫ g(−·) = −∫ g`; hence `∫ g = −∫ g`. -/
private lemma integral_odd_eq_zero (g : ℝ → ℝ) (hodd : ∀ x, g (-x) = - g x) :
    (∫ x, g x ∂(volume : Measure ℝ)) = 0 := by
  have h1 : ∫ x, g (-x) ∂(volume : Measure ℝ) = ∫ x, g x ∂(volume : Measure ℝ) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding g
    simpa using h
  have h2 : ∫ x, g (-x) ∂(volume : Measure ℝ) = - ∫ x, g x ∂(volume : Measure ℝ) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  rw [h1] at h2
  linarith

/-- **Conjugate symmetry of the diagonal density.**  Under `k ↦ −k`, using conjugate symmetry of the
Cauchy data and evenness of `ω`, `htDiag(−k) = conj(htDiag k)`.  Hence `(htDiag(−k)).im = −(htDiag k).im`,
so its imaginary part is an ODD function of `k`. -/
private lemma htDiag_conj_symm (m : ℝ) (Ψ π Χ Ρ : ℝ → ℂ)
    (hconjΨ : ∀ k, Ψ (-k) = starRingEnd ℂ (Ψ k))
    (hconjπ : ∀ k, π (-k) = starRingEnd ℂ (π k))
    (hconjΧ : ∀ k, Χ (-k) = starRingEnd ℂ (Χ k))
    (hconjΡ : ∀ k, Ρ (-k) = starRingEnd ℂ (Ρ k)) (k : ℝ) :
    htDiag m Ψ π Χ Ρ (-k) = starRingEnd ℂ (htDiag m Ψ π Χ Ρ k) := by
  simp only [htDiag, kgOmega_even, hconjΨ, hconjπ, hconjΧ, hconjΡ, map_add, map_mul, map_div₀,
    Complex.conj_ofReal, Complex.conj_conj]

/-- Cancellation helper: `2ℏ · (P / (2ℏ ω)) = P / ω` for `ℏ, ω ≠ 0`. -/
private lemma cancel_two_hbar (ℏ ω P : ℂ) (h : ℏ ≠ 0) (hω : ω ≠ 0) :
    2 * ℏ * (P / (2 * ℏ * ω)) = P / ω := by
  have h2 : (2 : ℂ) * ℏ ≠ 0 := mul_ne_zero two_ne_zero h
  field_simp

/-- **HT3 brick-2 — the Fourier-side positive-frequency coefficient theorem.**

For conjugate-symmetric Fourier-side Cauchy data `Ψ π Χ Ρ : ℝ → ℂ` (the transforms of real fields),
`m > 0`, `ℏ > 0`, with integrability of the inner-product integrand, of the diagonal density's
imaginary part, and of the symplectic integrand,

    2ℏ · (∫ conj(posFreqCoeff Ψ π)·posFreqCoeff Χ Ρ dk).im  =  σ_K(Ψ,π,Χ,Ρ) .

This is the **canonical-normalization identity** `σ = 2ℏ·Im⟨a,a⟩` on the Fourier side: the KG
symplectic pairing equals `2ℏ` times the imaginary part of the one-particle inner product of the
`√(2ℏω)`-normalized positive-frequency coefficients.  It is what fixes the `hTkk` localization
coefficient's normalization (up to the `ℏ` unit), turning it from a calibration into a derived
quantity — the coefficient physics, in Lean.

**Proof.**  Pointwise, `2ℏ·conj(a(Ψ,π))·a(Χ,Ρ) = htDiag + i·(conj Ψ·Ρ − conj π·Χ)` (the `√(2ℏω)`
denominator is real, `Complex.I_sq` supplies the `−i²`).  Taking `.im` and integrating: the `htDiag`
imaginary part integrates to `0` (odd in `k` by conjugate symmetry + evenness of `ω`), and
`(i·z).im = z.re` turns the off-diagonal into `(conj Ψ·Ρ − conj π·Χ).re = (conj Ψ·Ρ − conj Χ·π).re`
(the two agree because they differ by a purely imaginary term), i.e. `σ_K`. -/
theorem two_hbar_im_inner_posFreq_eq_sigmaK
    (m ℏ : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (Ψ π Χ Ρ : ℝ → ℂ)
    (hconjΨ : ∀ k, Ψ (-k) = starRingEnd ℂ (Ψ k))
    (hconjπ : ∀ k, π (-k) = starRingEnd ℂ (π k))
    (hconjΧ : ∀ k, Χ (-k) = starRingEnd ℂ (Χ k))
    (hconjΡ : ∀ k, Ρ (-k) = starRingEnd ℂ (Ρ k))
    (hf : Integrable
      (fun k => starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k)
      (volume : Measure ℝ))
    (hdiag : Integrable (fun k => (htDiag m Ψ π Χ Ρ k).im) (volume : Measure ℝ))
    (hsig : Integrable
      (fun k => starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k) (volume : Measure ℝ)) :
    2 * ℏ * (∫ k, starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k
        ∂(volume : Measure ℝ)).im
      = sigmaK Ψ π Χ Ρ := by
  set f : ℝ → ℂ :=
    fun k => starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k) * posFreqCoeff m ℏ Χ Ρ k with hfdef
  -- `(∫ f).im = ∫ (f k).im`
  have step1 : (∫ k, f k ∂(volume : Measure ℝ)).im = ∫ k, (f k).im ∂(volume : Measure ℝ) := by
    have h := integral_im hf
    simpa only [RCLike.im_eq_complex_im] using h.symm
  -- pointwise algebra: `2ℏ·(f k).im = (htDiag k).im + (conj Ψ·Ρ − conj Χ·π).re`
  have hptim : ∀ k, 2 * ℏ * (f k).im
      = (htDiag m Ψ π Χ Ρ k).im
        + (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re := by
    intro k
    have hωpos : 0 < kgOmega m k := kgOmega_pos m k hm
    have hωne : (kgOmega m k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hωpos
    have hℏne : (ℏ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hℏ
    have hDpos : 0 < 2 * ℏ * kgOmega m k := mul_pos (mul_pos two_pos hℏ) hωpos
    have hsqpos : 0 < Real.sqrt (2 * ℏ * kgOmega m k) := Real.sqrt_pos.mpr hDpos
    have hDDr : Real.sqrt (2 * ℏ * kgOmega m k) * Real.sqrt (2 * ℏ * kgOmega m k)
        = 2 * ℏ * kgOmega m k := Real.mul_self_sqrt (le_of_lt hDpos)
    have hDD : (Real.sqrt (2 * ℏ * kgOmega m k) : ℂ) * (Real.sqrt (2 * ℏ * kgOmega m k) : ℂ)
        = 2 * (ℏ : ℂ) * (kgOmega m k : ℂ) := by
      rw [← Complex.ofReal_mul, hDDr]; push_cast; ring
    -- conjugate of the first coefficient
    have hca : starRingEnd ℂ (posFreqCoeff m ℏ Ψ π k)
        = ((kgOmega m k : ℂ) * starRingEnd ℂ (Ψ k) - Complex.I * starRingEnd ℂ (π k))
            / (Real.sqrt (2 * ℏ * kgOmega m k) : ℂ) := by
      simp only [posFreqCoeff, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    -- the numerator identity (this is where `I² = −1` enters)
    have hnum : ((kgOmega m k : ℂ) * starRingEnd ℂ (Ψ k) - Complex.I * starRingEnd ℂ (π k))
          * ((kgOmega m k : ℂ) * Χ k + Complex.I * Ρ k)
        = (kgOmega m k : ℂ) * ((kgOmega m k : ℂ) * (starRingEnd ℂ (Ψ k) * Χ k))
          + starRingEnd ℂ (π k) * Ρ k
          + (kgOmega m k : ℂ) * Complex.I
              * (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (π k) * Χ k) := by
      linear_combination (-(starRingEnd ℂ (π k) * Ρ k)) * Complex.I_sq
    -- the master pointwise complex identity
    have hcplx : 2 * (ℏ : ℂ) * f k
        = htDiag m Ψ π Χ Ρ k
          + Complex.I * (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (π k) * Χ k) := by
      simp only [hfdef]
      rw [hca]
      unfold posFreqCoeff htDiag
      rw [div_mul_div_comm, hDD, cancel_two_hbar (ℏ : ℂ) (kgOmega m k : ℂ) _ hℏne hωne, hnum]
      field_simp
    -- take imaginary parts
    have himeq : (2 * (ℏ : ℂ) * f k).im
        = (htDiag m Ψ π Χ Ρ k).im
          + (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (π k) * Χ k).re := by
      rw [hcplx, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]; ring
    have hscale : (2 * (ℏ : ℂ) * f k).im = 2 * ℏ * (f k).im := by
      rw [show (2 : ℂ) * (ℏ : ℂ) = ((2 * ℏ : ℝ) : ℂ) from by push_cast; ring,
        Complex.im_ofReal_mul]
    have hre : (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (π k) * Χ k).re
        = (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re := by
      have hprod : (starRingEnd ℂ (π k) * Χ k).re = (starRingEnd ℂ (Χ k) * π k).re := by
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
      rw [Complex.sub_re, Complex.sub_re, hprod]
    rw [← hscale, himeq, hre]
  -- the diagonal imaginary part integrates to zero (odd in `k`)
  have hvanish : (∫ k, (htDiag m Ψ π Χ Ρ k).im ∂(volume : Measure ℝ)) = 0 :=
    integral_odd_eq_zero (fun k => (htDiag m Ψ π Χ Ρ k).im) (fun k => by
      show (htDiag m Ψ π Χ Ρ (-k)).im = -(htDiag m Ψ π Χ Ρ k).im
      rw [htDiag_conj_symm m Ψ π Χ Ρ hconjΨ hconjπ hconjΧ hconjΡ k, Complex.conj_im])
  -- the off-diagonal `.re`-integral is `σ_K`
  have hbridge : (∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re
        ∂(volume : Measure ℝ))
      = (∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k)
        ∂(volume : Measure ℝ)).re := by
    have h := integral_re hsig
    simpa only [RCLike.re_eq_complex_re] using h
  calc 2 * ℏ * (∫ k, f k ∂(volume : Measure ℝ)).im
      = 2 * ℏ * (∫ k, (f k).im ∂(volume : Measure ℝ)) := by rw [step1]
    _ = ∫ k, 2 * ℏ * (f k).im ∂(volume : Measure ℝ) :=
        (integral_const_mul (2 * ℏ) _).symm
    _ = ∫ k, ((htDiag m Ψ π Χ Ρ k).im
          + (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re)
          ∂(volume : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall hptim)
    _ = (∫ k, (htDiag m Ψ π Χ Ρ k).im ∂(volume : Measure ℝ))
          + ∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re
            ∂(volume : Measure ℝ) :=
        integral_add hdiag hsig.re
    _ = (∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k).re
          ∂(volume : Measure ℝ)) := by rw [hvanish, zero_add]
    _ = (∫ k, (starRingEnd ℂ (Ψ k) * Ρ k - starRingEnd ℂ (Χ k) * π k)
          ∂(volume : Measure ℝ)).re := hbridge
    _ = sigmaK Ψ π Χ Ρ := by simp only [sigmaK]

end QIQTH.KGSymplectic
