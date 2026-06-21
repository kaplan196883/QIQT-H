import QIQTH.StandardSubspaceModularFlow
import QIQTH.Fock.Localization
import QIQTH.Fock.OneParticle
import QIQTH.Fock.SecondQuantModularFlow
import QIQTH.StripUniqueness
import QIQTH.KMSCorrelation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# One-particle Bisognano–Wichmann — Phase 0: the scalar spectral identity

Toward the one-particle BW identification `modUnitary 𝒦_wedge t = boostUnitary(−2π t)` (the
standard-subspace modular flow IS the geometric Lorentz boost), following GPT-5.5's plan
(Route C — the RvD bridge: it suffices that the wedge RvD operator `R` is the **Fermi function** of the
boost generator `P`, `R = 2/(1+exp(2π P))`, since then `g(R) = log((2−R)/R) = 2π P`).

This file proves the **scalar core** of that spectral identity — fully self-contained, axiom-free:
the modular spectral character `modChar t r = exp(i·t·log((2−r)/r))` evaluated at `r = fermi x`
(`fermi x = 2/(1+e^{2π x})`) is exactly `exp(i·t·2π x)`.  This is the pointwise statement
`g(fermi x) = 2π x` behind `modUnitary(t) = exp(i·t·2π P) = boostUnitary(−2π t)`.

The physical wedge subspace, its standardness, and the operator identity `rvdRC 𝒦 = fermi(2π P)` are the
genuinely analytic inputs (one-particle Reeh–Schlieder / strip-KMS) — those will be isolated as labelled
conditional hypotheses, NOT proved here and NEVER Lean axioms.
-/

namespace QIQTH.Fock.OneParticleBW

open scoped ENNReal
open QIQTH.StandardSubspaceModular

/-- The **Fermi function** of the boost generator's spectral parameter:
    `fermi x = 2/(1 + e^{2π x})`.  This is the spectral form of the wedge RvD operator `R` in the
    momentum (`P = −i d/dθ`) representation: `R = fermi(2π P)`. -/
noncomputable def fermi (x : ℝ) : ℝ := 2 / (1 + Real.exp (2 * Real.pi * x))

theorem fermi_mem_Ioo (x : ℝ) : fermi x ∈ Set.Ioo (0 : ℝ) 2 := by
  have hE : (0 : ℝ) < Real.exp (2 * Real.pi * x) := Real.exp_pos _
  refine ⟨by unfold fermi; positivity, ?_⟩
  unfold fermi
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hE]

/-- **The scalar BW spectral identity** `g(fermi x) = 2π x`, in character form:
    `modChar t (fermi x) = exp(i·t·2π x)`.  Since `(2 − fermi x)/fermi x = e^{2π x}`, the modular
    generator `g(r) = log((2−r)/r)` evaluated at `fermi x` is `2π x` — the pointwise core of
    `modUnitary(t) = boostUnitary(−2π t)`. -/
theorem modChar_fermi (t x : ℝ) :
    modChar t (fermi x) = Complex.exp (Complex.I * (t : ℂ) * ((2 * Real.pi * x : ℝ) : ℂ)) := by
  have hE : (0 : ℝ) < Real.exp (2 * Real.pi * x) := Real.exp_pos _
  have h1E : (1 : ℝ) + Real.exp (2 * Real.pi * x) ≠ 0 := by positivity
  have hratio : (2 - fermi x) / fermi x = Real.exp (2 * Real.pi * x) := by
    unfold fermi
    field_simp
    ring
  have hlog : Real.log ((2 - fermi x) / fermi x) = 2 * Real.pi * x := by
    rw [hratio, Real.log_exp]
  unfold modChar
  rw [Set.piecewise_eq_of_mem _ _ _ (fermi_mem_Ioo x), hlog]

/-! ### Layer 1 — the physical wedge subspace (boost covariance at the L² level) -/

open MeasureTheory QIQTH.Fock.Localization QIQTH.Fock.OneParticle

/-- **L² boost-covariance of the localization** (GPT-5.5's first Layer-1 brick, the sign check):
    `boostUnitary a (KrepL2 f) = KrepL2 (boostTest (−a) f)`.  The geometric boost acts on the
    one-particle wavefunction `Krep f ∈ L²(rapidity)` exactly as the spacetime boost `boostTest (−a)`
    on the test function.  This is the engine for boost-invariance of the physically-defined wedge
    subspace (`𝒦 := closure of {KrepL2 f : f real, supp f ⊆ right wedge}`).  Axiom-free; from
    `Krep_boost` + the flow `θ ↦ θ + (−a) = θ − a`. -/
theorem boostUnitary_KrepL2 (m a : ℝ) (f : V → ℂ)
    (h : MemLp (Krep m f) 2 (volume : Measure ℝ))
    (h' : MemLp (Krep m (boostTest (-a) f)) 2 (volume : Measure ℝ)) :
    boostUnitary a (h.toLp (Krep m f)) = h'.toLp (Krep m (boostTest (-a) f)) := by
  have hae : ⇑(boostUnitary a (h.toLp (Krep m f)))
      =ᵐ[volume] Krep m (boostTest (-a) f) := by
    have h1 := Lp.coeFn_compMeasurePreserving (h.toLp (Krep m f)) (boostFlow.mp (-a))
    have htend : Filter.Tendsto (boostFlow.flow (-a)) (ae volume) (ae volume) :=
      (boostFlow.mp (-a)).quasiMeasurePreserving.tendsto_ae
    have h2 : (⇑(h.toLp (Krep m f)) ∘ boostFlow.flow (-a))
        =ᵐ[volume] (Krep m f ∘ boostFlow.flow (-a)) :=
      htend.eventually h.coeFn_toLp
    have h3 : boostUnitary a (h.toLp (Krep m f))
        = Lp.compMeasurePreserving (boostFlow.flow (-a)) (boostFlow.mp (-a)) (h.toLp (Krep m f)) :=
      MPFlow.unitary_apply boostFlow a (h.toLp (Krep m f))
    rw [h3]
    refine h1.trans (h2.trans ?_)
    filter_upwards with θ
    show Krep m f (θ + (-a)) = Krep m (boostTest (-a) f) θ
    rw [Krep_boost]
  exact Lp.ext (hae.trans h'.coeFn_toLp.symm)

/-! ### Strong continuity of the boost group (first brick of the Stone-generator program) -/

/-- **Pointwise form of the boost action**: `(boostUnitary a ξ)(θ) = ξ(θ − a)` (a.e.).  The rapidity boost
    is the spatial translation `θ ↦ θ − a` on the one-particle wavefunction.  From `MPFlow.unitary_apply`
    (the unitary precomposes with the pullback flow `θ ↦ θ + (−a)`). -/
theorem coeFn_boostUnitary (a : ℝ) (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(boostUnitary a ξ) =ᵐ[volume] fun θ => (ξ : ℝ → ℂ) (θ - a) := by
  have hcmp : boostUnitary a ξ
      = Lp.compMeasurePreserving (boostFlow.flow (-a)) (boostFlow.mp (-a)) ξ :=
    MPFlow.unitary_apply boostFlow a ξ
  rw [hcmp]
  filter_upwards [Lp.coeFn_compMeasurePreserving ξ (boostFlow.mp (-a))] with θ hθ
  rw [hθ]
  show (ξ : ℝ → ℂ) (θ + -a) = (ξ : ℝ → ℂ) (θ - a)
  rw [sub_eq_add_neg]

/-- **The boost unitary IS the canonical `Lp` domain-translation** `DomAddAct.mk t +ᵥ ξ`.  `boostUnitary t`
    is precomposition with `θ ↦ θ + t` (the rapidity-translation flow); Mathlib's `DomAddAct` action is
    precomposition with `θ ↦ t + θ`.  They agree by `add_comm`, identifying the project's boost group with
    Mathlib's continuous domain action — the bridge that makes the boost group's *strong continuity* a
    one-line consequence of Mathlib's `Lp.instContinuousVAddDomAddAct`. -/
theorem boostUnitary_eq_vadd (t : ℝ) (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    boostUnitary t ξ = DomAddAct.mk (-t) +ᵥ ξ := by
  have hcmp : boostUnitary t ξ
      = Lp.compMeasurePreserving (boostFlow.flow (-t)) (boostFlow.mp (-t)) ξ :=
    MPFlow.unitary_apply boostFlow t ξ
  have h1 : ⇑(boostUnitary t ξ) =ᵐ[volume] (fun x => (ξ : ℝ → ℂ) (x + -t)) := by
    rw [hcmp]
    filter_upwards [Lp.coeFn_compMeasurePreserving ξ (boostFlow.mp (-t))] with x hx
    rw [hx]; rfl
  have h2 : ⇑(DomAddAct.mk (-t) +ᵥ ξ) =ᵐ[volume] (fun x => (ξ : ℝ → ℂ) (-t + x)) := by
    filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-t)) ξ] with x hx
    rw [hx, Equiv.symm_apply_apply]; rfl
  apply Lp.ext
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, add_comm]

/-- **★ Strong continuity of the boost group** (vector level): for every one-particle state `ξ`, the orbit
    `t ↦ boostUnitary t ξ` is continuous.  This is the genuine strong continuity of the rapidity-translation
    unitary group — the *first brick of the Stone-generator program* whose later steps would ground the
    boost-charge derivative `hBoostCharge`.  Derived from Mathlib's continuity of the `Lp` domain action
    (`Lp.instContinuousVAddDomAddAct`, valid since Lebesgue measure is translation-invariant, locally finite,
    inner regular) via the identification `boostUnitary_eq_vadd`.  Axiom-free. -/
theorem continuous_boostUnitary_apply (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun t : ℝ => boostUnitary t ξ) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have heq : (fun t : ℝ => boostUnitary t ξ) = fun t : ℝ => DomAddAct.mk (-t) +ᵥ ξ :=
    funext (fun t => boostUnitary_eq_vadd t ξ)
  rw [heq]
  have hmk : Continuous (fun t : ℝ => DomAddAct.mk (-t) : ℝ → DomAddAct ℝ) :=
    DomAddAct.mkHomeomorph.continuous.comp continuous_neg
  exact (continuous_id.vadd continuous_const).comp hmk

/-- **Strong continuity at the wedge-boost rate** (the `t ↦ boostUnitary(−2π t)` form used in the BW flow):
    `boostUnitary(−2π t) ξ → ξ` as `t → 0`.  This is exactly the strong-continuity premise a Stone-generator
    construction of the boost-charge derivative would consume.  Axiom-free. -/
theorem tendsto_boostUnitary_wedge (ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    Filter.Tendsto (fun t : ℝ => boostUnitary (-(2 * Real.pi * t)) ξ) (nhds 0) (nhds ξ) := by
  have hc : Continuous (fun t : ℝ => boostUnitary (-(2 * Real.pi * t)) ξ) :=
    (continuous_boostUnitary_apply ξ).comp (by fun_prop)
  have hval : (fun t : ℝ => boostUnitary (-(2 * Real.pi * t)) ξ) 0 = ξ := by
    show boostUnitary (-(2 * Real.pi * 0)) ξ = ξ
    rw [mul_zero, neg_zero, boostUnitary_zero_apply]
  have h0 : Filter.Tendsto (fun t : ℝ => boostUnitary (-(2 * Real.pi * t)) ξ) (nhds 0)
      (nhds ((fun t : ℝ => boostUnitary (-(2 * Real.pi * t)) ξ) 0)) := hc.continuousAt.tendsto
  rwa [hval] at h0

/-- **★ Matrix-element continuity of the boost group** — the boundary regularity the strip/KMS property
    rests on.  For every pair of one-particle states, the correlation `t ↦ ⟪η, boostUnitary t ξ⟫` is
    continuous on the real axis.  This is the real-axis regularity of the matrix element `F_{η,ξ}(t)` whose
    holomorphic strip extension is asserted by `StripKMS` — so it is a genuine, derived ingredient of the
    wedge-KMS input (the boundary function it constrains is itself continuous), and the scalar shadow of the
    boost group's strong continuity (`continuous_boostUnitary_apply` composed with the continuous inner
    product).  Axiom-free. -/
theorem continuous_inner_boostUnitary (η ξ : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous (fun t : ℝ => inner ℂ η (boostUnitary t ξ)) :=
  continuous_const.inner (continuous_boostUnitary_apply ξ)

/-- **★ The boost matrix coefficient as a concrete translation integral.**  For a one-particle state given
    by a representative `f` (`ξ = f.toLp`), the modular/boost correlation `⟪ξ, boostUnitary s ξ⟫` is the
    cross-correlation integral `∫ conj(f θ)·f(θ − s) dθ`.  This is the inner-product-to-integral bridge
    (`L2.inner_def` + `MemLp.coeFn_toLp` + `coeFn_boostUnitary`, the translation pushed through the
    measure-preserving shift) that turns the abstract boost correlation into an analyzable integral — the
    setup on which the boost-charge *derivative* (Stone generator → `hBoostCharge`) is computed.  Axiom-free. -/
theorem inner_boostUnitary_toLp (f : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ)) (s : ℝ) :
    inner ℂ (hf2.toLp f) (boostUnitary s (hf2.toLp f))
      = ∫ θ, (starRingEnd ℂ) (f θ) * f (θ - s) ∂(volume : Measure ℝ) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hξ : ⇑(hf2.toLp f) =ᵐ[volume] f := hf2.coeFn_toLp
  have hb : ⇑(boostUnitary s (hf2.toLp f)) =ᵐ[volume]
      fun θ => (hf2.toLp f : ℝ → ℂ) (θ - s) := coeFn_boostUnitary s (hf2.toLp f)
  have hξs : (fun θ : ℝ => (hf2.toLp f : ℝ → ℂ) (θ - s)) =ᵐ[volume] fun θ => f (θ - s) :=
    ((measurePreserving_sub_right volume s).quasiMeasurePreserving.tendsto_ae).eventually hξ
  filter_upwards [hξ, hb, hξs] with θ hθ hbθ hθs
  show inner ℂ (⇑(hf2.toLp f) θ) (⇑(boostUnitary s (hf2.toLp f)) θ)
      = (starRingEnd ℂ) (f θ) * f (θ - s)
  rw [hbθ, hθ, hθs, RCLike.inner_apply, mul_comm]

/-- **★★ The boost-charge derivative (the analytic core of `hBoostCharge`).**  For a one-particle state
    `ξ = f.toLp` with `f` smooth enough (differentiable with derivative `f'`, with `f`, `|f|²` integrable and
    `‖f'‖` globally bounded — all satisfied by any Schwartz / compactly-supported-`C¹` `f`), the boost
    correlation `t ↦ ⟪ξ, boostUnitary(−2π t) ξ⟫` is differentiable at `0` with derivative
    `2π·∫ conj(f)·f'`.  This is the **rapidity-momentum expectation** `2π⟪ξ, −i∂_θ ξ⟫` — the boost charge —
    obtained by differentiating the cross-correlation integral under the integral sign
    (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominating function `2π·B·|f|`).  Composed with the
    unitarity fact that this derivative is purely imaginary, it is exactly `hBoostCharge` modulo the single
    physical identification `2π⟪ξ,pξ⟫ = (2π/ℏ)·T_kk` (the stress tensor).  Axiom-free. -/
theorem hasDerivAt_inner_boostUnitary_wedge
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hf_meas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * t)) (hf2.toLp f)))
      (2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)) 0 := by
  have hcorr : (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * t)) (hf2.toLp f)))
      = fun t : ℝ => ∫ θ, (starRingEnd ℂ) (f θ) * f (θ + 2 * Real.pi * t) ∂(volume : Measure ℝ) := by
    funext t
    rw [inner_boostUnitary_toLp f hf2 (-(2 * Real.pi * t))]
    simp only [sub_neg_eq_add]
  rw [hcorr]
  have hconj : AEStronglyMeasurable (fun θ => (starRingEnd ℂ) (f θ)) (volume : Measure ℝ) :=
    Complex.continuous_conj.comp_aestronglyMeasurable hf_meas
  set F : ℝ → ℝ → ℂ := fun t θ => (starRingEnd ℂ) (f θ) * f (θ + 2 * Real.pi * t) with hF
  set F' : ℝ → ℝ → ℂ :=
    fun t θ => (starRingEnd ℂ) (f θ) * ((2 * Real.pi : ℝ) • f' (θ + 2 * Real.pi * t)) with hF'
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (F := F) (F' := F') (bound := fun θ => 2 * Real.pi * B * ‖f θ‖)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall (fun t => hconj.mul
      (hf_meas.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (2 * Real.pi * t)).quasiMeasurePreserving)))
    (by simpa only [hF, mul_zero, add_zero] using hF0_int)
    (hconj.mul ((hf'_meas.comp_quasiMeasurePreserving
        (measurePreserving_add_right volume (2 * Real.pi * 0)).quasiMeasurePreserving).const_smul
        (2 * Real.pi : ℝ)))
    (Filter.Eventually.of_forall (fun θ x _ => ?_))
    (hf_int.norm.const_mul (2 * Real.pi * B))
    (Filter.Eventually.of_forall (fun θ x _ => ?_))).2
  · have hvaleq : (∫ θ, F' 0 θ ∂(volume : Measure ℝ))
        = 2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ) := by
      have hpt : (fun θ => F' 0 θ)
          = fun θ => ((2 * Real.pi : ℝ) : ℂ) * ((starRingEnd ℂ) (f θ) * f' θ) := by
        funext θ; simp only [hF', mul_zero, add_zero, Complex.real_smul]; ring
      rw [hpt, integral_const_mul]; push_cast; ring
    rw [← hvaleq]; exact key
  · rw [hF', norm_mul, RCLike.norm_conj, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    calc ‖f θ‖ * (2 * Real.pi * ‖f' (θ + 2 * Real.pi * x)‖)
        ≤ ‖f θ‖ * (2 * Real.pi * B) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ = 2 * Real.pi * B * ‖f θ‖ := by ring
  · rw [hF, hF']
    have hlin : HasDerivAt (fun t : ℝ => θ + 2 * Real.pi * t) (2 * Real.pi) x := by
      simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi)).const_add θ
    have hcomp : HasDerivAt (fun t : ℝ => f (θ + 2 * Real.pi * t))
        ((2 * Real.pi : ℝ) • f' (θ + 2 * Real.pi * x)) x :=
      (hfd (θ + 2 * Real.pi * x)).scomp x hlin
    exact hcomp.const_mul ((starRingEnd ℂ) (f θ))

/-- **★★★ The boost-charge derivative in its physical `i·(real)` form — `hBoostCharge` grounded.**  The boost
    correlation derivative is **purely imaginary**: `d/dt ⟪ξ, boostUnitary(−2π t) ξ⟫|₀ = i·(boost energy)`,
    with boost energy `= (2π·∫ conj(f)·f')·(−i) =` the real rapidity-momentum expectation.  This is exactly the
    shape of the labelled `hBoostCharge` input — now DERIVED for any smooth wedge state (modulo only the single
    physical identification `boost energy = (2π/ℏ)·T_kk`, the stress tensor).

    The imaginarity is forced by **unitarity** (`GPT-5.5-pro`'s observation): `Re⟪ξ, U(t)ξ⟫ ≤ ‖ξ‖²` with
    equality at `t = 0` (Cauchy–Schwarz `norm_inner_le_norm` + the isometry `‖U(t)ξ‖ = ‖ξ‖`), so the real part
    of the correlation has a maximum at `0`, hence its derivative — the real part of the complex derivative —
    vanishes (`IsLocalMax.hasDerivAt_eq_zero`).  A complex number with zero real part is `i` times its
    imaginary part.  Axiom-free. -/
theorem hasDerivAt_inner_boostUnitary_imaginary
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hf_meas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * t)) (hf2.toLp f)))
      (Complex.I *
        (((2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)).im : ℝ) : ℂ)) 0 := by
  set ξ := hf2.toLp f with hξ
  set D := 2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ) with hDdef
  have hD : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ)) D 0 :=
    hasDerivAt_inner_boostUnitary_wedge f f' hf2 hf_int hF0_int hf_meas hfd hf'_meas B hB
  -- The real part of the correlation has a maximum at 0 (unitarity).
  have hmax : ∀ t : ℝ,
      (inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ) : ℂ).re
        ≤ (inner ℂ ξ (boostUnitary (-(2 * Real.pi * 0)) ξ) : ℂ).re := by
    intro t
    have h0 : (inner ℂ ξ (boostUnitary (-(2 * Real.pi * 0)) ξ) : ℂ).re = ‖ξ‖ * ‖ξ‖ := by
      simp only [mul_zero, neg_zero, boostUnitary_zero_apply]
      exact inner_self_eq_norm_mul_norm (𝕜 := ℂ) ξ
    rw [h0]
    calc (inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ)).re
        ≤ ‖inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ)‖ := Complex.re_le_norm _
      _ ≤ ‖ξ‖ * ‖boostUnitary (-(2 * Real.pi * t)) ξ‖ := norm_inner_le_norm _ _
      _ = ‖ξ‖ * ‖ξ‖ := by rw [LinearIsometryEquiv.norm_map]
  have hRe : HasDerivAt (fun t : ℝ => (inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ) : ℂ).re)
      D.re 0 := by
    have h := (Complex.reCLM.hasFDerivAt.comp 0 hD.hasFDerivAt).hasDerivAt
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.reCLM_apply] using h
  have hlocmax : IsLocalMax
      (fun t : ℝ => (inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ) : ℂ).re) 0 :=
    Filter.Eventually.of_forall hmax
  have hzero : D.re = 0 := hlocmax.hasDerivAt_eq_zero hRe
  have hDeq : D = Complex.I * ((D.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hzero]
  rw [hDeq] at hD
  exact hD

/-- **★★★ The `WedgeKMSFlux` boost-charge slot, DERIVED — only the scalar stress-flux identification stays
    labelled.**  The `hBoostCharge` component of the wedge-KMS bundle (the labelled input of
    `qiqt_gr_from_wedge_kms`) demands exactly
    `HasDerivAt (t ↦ ⟪ξ, boostUnitary(−2π t) ξ⟫) (i·(2π/ℏ)·T_kk) 0`.
    For any smooth wedge state `ξ = f.toLp`, `hasDerivAt_inner_boostUnitary_imaginary` *derives* this — the
    derivative is `i·(boost energy)` — so the ENTIRE boost-charge slot reduces to the single scalar physics
    identification `hTkk : (2π/ℏ)·T_kk = boost energy` (the conserved boost Killing charge equals the
    stress-tensor flux).  This pins the irreducible labelled remainder of input #1 to one real equation —
    everything operator/analytic is machine-checked.  Axiom-free. -/
theorem wedge_hBoostCharge_of_smooth
    (f f' : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hf_int : Integrable f (volume : Measure ℝ))
    (hF0_int : Integrable (fun θ => (starRingEnd ℂ) (f θ) * f θ) (volume : Measure ℝ))
    (hf_meas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hf'_meas : AEStronglyMeasurable f' (volume : Measure ℝ))
    (B : ℝ) (hB : ∀ x, ‖f' x‖ ≤ B) (hbar Tkk : ℝ)
    (hTkk : 2 * Real.pi / hbar * Tkk
        = (2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f θ) * f' θ ∂(volume : Measure ℝ)).im) :
    HasDerivAt
      (fun t : ℝ => inner ℂ (hf2.toLp f) (boostUnitary (-(2 * Real.pi * t)) (hf2.toLp f)))
      (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0 := by
  rw [hTkk]
  exact hasDerivAt_inner_boostUnitary_imaginary f f' hf2 hf_int hF0_int hf_meas hfd hf'_meas B hB

/-- **Invariance engine** (for the boost-invariance of the wedge standard subspace): a continuous
    `ℝ`-linear map `L` that maps a set `W` into itself also maps `closure (span ℝ W)` into itself.
    Applied with `L = boostUnitary a` and `W` = the (boost-closed) wedge generating set, this gives
    `boostUnitary a (𝒦_W) ⊆ 𝒦_W` — the boost-invariance the KMS-uniqueness route needs. -/
theorem mapsTo_closure_span {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (L : M →L[ℝ] M) {W : Set M} (hW : Set.MapsTo L W W) :
    Set.MapsTo L (closure (Submodule.span ℝ W : Set M)) (closure (Submodule.span ℝ W : Set M)) := by
  have hsub : (L : M → M) '' (Submodule.span ℝ W : Set M) ⊆ (Submodule.span ℝ W : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (hW hw)
    | zero => simpa using (Submodule.span ℝ W).zero_mem
    | add x _ y _ hx hy => rw [map_add]; exact (Submodule.span ℝ W).add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact (Submodule.span ℝ W).smul_mem r hx
  intro ψ hψ
  exact closure_mono hsub (image_closure_subset_closure_image L.continuous ⟨ψ, hψ, rfl⟩)

/-- **Boost-invariance of a physically-defined wedge subspace.**  If a set `S` of one-particle vectors is
    closed under the boost (`boostUnitary a` maps `S` into `S` — true for `S` = the `KrepL2` of a
    boost-closed family of wedge test functions, via `boostUnitary_KrepL2`), then the wedge standard
    subspace `𝒦_W := closure (span_ℝ S)` is boost-invariant: `boostUnitary a (𝒦_W) ⊆ 𝒦_W`.  This is the
    invariance the GPT-5-pro KMS-uniqueness route consumes (`V(a)𝒦 = 𝒦`). -/
theorem boostUnitary_mapsTo_closure_span (a : ℝ) {S : Set (Lp ℂ 2 (volume : Measure ℝ))}
    (hS : Set.MapsTo (boostUnitary a) S S) :
    Set.MapsTo (boostUnitary a)
      (closure (Submodule.span ℝ S : Set _)) (closure (Submodule.span ℝ S : Set _)) :=
  mapsTo_closure_span
    ((boostUnitary a).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) hS

/-! ### Layer 1 — the right wedge is boost-invariant (the geometric foundation) -/

/-- **The right wedge** `W_R = {z : z¹ > |z⁰|}` in 1+1D Minkowski `V = Fin 2 → ℝ` (index `0` = time,
    `1` = space), written in light-cone form `z¹ − z⁰ > 0 ∧ z¹ + z⁰ > 0`. -/
def rightWedge : Set V := {z | 0 < z 1 - z 0 ∧ 0 < z 1 + z 0}

/-- **The right wedge is boost-invariant**: `lorentzBoost a` maps `W_R` into itself.  In light-cone
    coordinates `z± = z¹ ± z⁰` the boost acts by the positive scalings `z⁻ ↦ e^{−a}z⁻`, `z⁺ ↦ e^{a}z⁺`,
    so positivity of both is preserved.  This is why the wedge generating set of test functions is
    boost-closed, hence `𝒦_W` is boost-invariant. -/
theorem lorentzBoost_mapsTo_rightWedge (a : ℝ) :
    Set.MapsTo (lorentzBoost a) rightWedge rightWedge := by
  rintro z ⟨h1, h2⟩
  have hcs : Real.cosh a - Real.sinh a = Real.exp (-a) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  have hca : Real.cosh a + Real.sinh a = Real.exp a := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  refine ⟨?_, ?_⟩
  · simp only [rightWedge, Set.mem_setOf_eq, lorentzBoost_zero, lorentzBoost_one]
    have hrw : (Real.sinh a * z 0 + Real.cosh a * z 1) - (Real.cosh a * z 0 + Real.sinh a * z 1)
        = (Real.cosh a - Real.sinh a) * (z 1 - z 0) := by ring
    rw [hrw, hcs]
    have := Real.exp_pos (-a)
    positivity
  · simp only [rightWedge, Set.mem_setOf_eq, lorentzBoost_zero, lorentzBoost_one]
    have hrw : (Real.sinh a * z 0 + Real.cosh a * z 1) + (Real.cosh a * z 0 + Real.sinh a * z 1)
        = (Real.cosh a + Real.sinh a) * (z 1 + z 0) := by ring
    rw [hrw, hca]
    have := Real.exp_pos a
    positivity

/-- **The boost is invertible**: `lorentzBoost (−a) ∘ lorentzBoost a = id` (`cosh²−sinh²=1`). -/
theorem lorentzBoost_neg_boost (a : ℝ) (z : V) : lorentzBoost (-a) (lorentzBoost a z) = z := by
  funext i
  fin_cases i
  · show lorentzBoost (-a) (lorentzBoost a z) 0 = z 0
    simp only [lorentzBoost_zero, lorentzBoost_one, Real.cosh_neg, Real.sinh_neg]
    linear_combination z 0 * Real.cosh_sq_sub_sinh_sq a
  · show lorentzBoost (-a) (lorentzBoost a z) 1 = z 1
    simp only [lorentzBoost_zero, lorentzBoost_one, Real.cosh_neg, Real.sinh_neg]
    linear_combination z 1 * Real.cosh_sq_sub_sinh_sq a

/-- **Boost preserves wedge support**: if `f` is supported in the right wedge, so is its boost
    `boostTest a f = f ∘ lorentzBoost a`.  (From `lorentzBoost_mapsTo_rightWedge` + the boost inverse.)
    This makes the wedge generating set `{KrepL2 f : supp f ⊆ W_R}` boost-closed. -/
theorem support_boostTest_subset (a : ℝ) {f : V → ℂ}
    (hf : Function.support f ⊆ rightWedge) :
    Function.support (boostTest a f) ⊆ rightWedge := by
  intro x hx
  rw [Function.mem_support] at hx
  have hmem : lorentzBoost a x ∈ Function.support f := Function.mem_support.mpr hx
  have h1 := lorentzBoost_mapsTo_rightWedge (-a) (hf hmem)
  rwa [lorentzBoost_neg_boost] at h1

/-! ### Layer 1 — the wedge standard subspace, boost-invariant (assembly) -/

/-- **The wedge generating set**: the one-particle vectors `KrepL2 f` from *real*, *wedge-supported*,
    `L²` test functions.  The physical generators of the wedge standard subspace — defined PURELY from
    wedge test functions (NOT from modular data), per the anti-circularity discipline. -/
def wedgeGenSet (m : ℝ) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {ψ | ∃ (f : V → ℂ) (h : MemLp (Krep m f) 2 (volume : Measure ℝ)),
        Function.support f ⊆ rightWedge ∧ (∀ x, (starRingEnd ℂ) (f x) = f x)
        ∧ ψ = h.toLp (Krep m f)}

/-- **The wedge generating set is boost-closed**: `boostUnitary a` maps it into itself.  For
    `ψ = KrepL2 f`, `boostUnitary a ψ = KrepL2(boostTest(−a) f)` (sign lemma), and `boostTest(−a) f` is
    again real, wedge-supported (`support_boostTest_subset`), and `L²` (translation of an `L²` function). -/
theorem boostUnitary_mapsTo_wedgeGenSet (m a : ℝ) :
    Set.MapsTo (boostUnitary a) (wedgeGenSet m) (wedgeGenSet m) := by
  rintro ψ ⟨f, h, hsupp, hreal, rfl⟩
  have hmemLp' : MemLp (Krep m (boostTest (-a) f)) 2 (volume : Measure ℝ) := by
    have heq : Krep m (boostTest (-a) f) = (Krep m f) ∘ (fun θ => θ + (-a)) := by
      funext θ; exact Krep_boost m (-a) f θ
    rw [heq]
    exact h.comp_measurePreserving (measurePreserving_add_right volume (-a))
  refine ⟨boostTest (-a) f, hmemLp', support_boostTest_subset (-a) hsupp, ?_,
    boostUnitary_KrepL2 m a f h hmemLp'⟩
  intro x
  show (starRingEnd ℂ) (f (lorentzBoost (-a) x)) = f (lorentzBoost (-a) x)
  exact hreal _

/-- **★ The wedge standard subspace `𝒦_W := closure (span_ℝ (wedge generators))` is BOOST-INVARIANT:**
    `boostUnitary a (𝒦_W) ⊆ 𝒦_W` for every rapidity `a`.  This is the `V(a)𝒦 = 𝒦` the GPT-5-pro
    KMS-uniqueness route consumes — now PROVED axiom-free for the physically-defined wedge subspace
    (assembling the sign lemma + invariance engine + wedge geometry).  The remaining inputs of the
    one-particle BW are the (formalizable) KMS-uniqueness lemma and the single labelled strip/KMS
    property of `boostUnitary` on these vectors. -/
theorem boostUnitary_mapsTo_wedgeSubspace (m a : ℝ) :
    Set.MapsTo (boostUnitary a)
      (closure (Submodule.span ℝ (wedgeGenSet m) : Set _))
      (closure (Submodule.span ℝ (wedgeGenSet m) : Set _)) :=
  boostUnitary_mapsTo_closure_span a (boostUnitary_mapsTo_wedgeGenSet m a)

/-! ### The conditional one-particle BW theorem (KMS-uniqueness route, two labelled AQFT inputs) -/

section ConditionalBW
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The KMS strip (rescaled so the boost period is `1`): `{z : 0 < Im z < 1}`. -/
def kmsStrip : Set ℂ := {z : ℂ | 0 < z.im ∧ z.im < 1}

/-- **The standard-subspace KMS strip property** — the single physical labelled AQFT input
    `Hyp_strip_Krep` (BGL §4).  On a dense core `D`, for each `ξ, η ∈ D` the correlation
    `t ↦ ⟪ξ, V t η⟫` extends to a function `F` holomorphic on the strip `0 < Im z < 1`, matching the
    correlation on the real axis and satisfying the KMS boundary flip `F(t+i) = ⟪η, V t ξ⟫` at the top
    edge.  Stated via an existentially-quantified extension `F`, so no Hardy-space machinery is required —
    this is precisely the analytic fact the one-particle Bisognano–Wichmann theorem rests on. -/
def StripKMS (V : ℝ → (H →L[ℂ] H)) (D : Set H) : Prop :=
  Dense D ∧ ∀ ξ ∈ D, ∀ η ∈ D, ∃ F : ℂ → ℂ,
    DifferentiableOn ℂ F kmsStrip ∧
    (∀ t : ℝ, F t = inner ℂ ξ (V t η)) ∧
    (∀ t : ℝ, F ((t : ℂ) + Complex.I) = inner ℂ η (V t ξ))

/-- **The CORRECT one-particle KMS condition — Rieffel–Van Daele (1977), Definition 3.4.**  Faithful to the
    source (refs/RieffelVanDaele): a strongly-continuous unitary group `V` satisfies the KMS condition w.r.t.
    the **real subspace** `K` (`= 𝒦`) iff for every `ξ, η ∈ K` there is `f`
    * **bounded and continuous on the closed strip `{−1 ≤ Im z ≤ 0}`, analytic in the interior**
      (`DiffContOnCl` on the open strip `{−1 < Im < 0}` + a uniform bound `M`), with boundary values
    * `f(t)   = ⟪η, V(t) ξ⟫`   (bottom edge `Im = 0`),
    * `f(t−i) = ⟪V(t) ξ, η⟫`   (top edge `Im = −1`, the plain flip).

    **Convention (corrected 2026-06-21, RvD Def 3.4 read from source pp.194-195):** RvD writes `f(t)=⟨U_tξ, η⟩`
    with `⟨·,·⟩` *linear-first* (forced — `⟨h(z), Δ^{it}ξ⟩` must be entire with `h(z)` entire), which in Mathlib
    `inner` (conj-linear-first) is `inner ℂ η (V_t ξ)` — the orbit `V_tξ` in the LINEAR slot.  This is the
    convention `Δ` actually satisfies: `⟪η, Δ^{iz}ξ⟫` is HOLOMORPHIC and extends to `Im z < 0` (RvD Lemma 3.6,
    `R^{iz}` analytic for `Im z<0`).  The conjugate `⟪V_tξ, η⟫` is anti-holomorphic (extends to the *upper*
    strip), so it would NOT be satisfied by `Δ` on this lower strip — the earlier statement of this kind was
    the conjugate of Def 3.4 and is now corrected.

    This is the fix for the defect `stripKMS_trivial` exposes in `StripKMS`: the boundedness +
    continuity-to-the-closure (absent from `StripKMS`) is exactly what makes the extension **unique**
    (RvD's Schwarz-reflection remark) and the condition a genuine constraint.  RvD **Theorem 3.8** then proves
    `Δ^{it}` is the *unique* such group carrying `K` onto `K` — i.e. this `StripKMSrvd` discharges `hUniq`,
    and crucially RvD prove it with **bounded operators only** (entire vectors + Schwarz reflection), so it is
    NOT blocked on Stone's theorem / unbounded Tomita.  The plain flip is correct here precisely because
    `ξ, η ∈ K` are *real-subspace* vectors (`Δ^{1/2}ξ = Jξ`), per RvD Prop 3.7. -/
def StripKMSrvd (V : ℝ → (H →L[ℂ] H)) (K : Set H) : Prop :=
  ∀ ξ ∈ K, ∀ η ∈ K, ∃ f : ℂ → ℂ,
    DiffContOnCl ℂ f (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
    (∃ M : ℝ, ∀ z : ℂ, ‖f z‖ ≤ M) ∧
    (∀ t : ℝ, f t = inner ℂ η (V t ξ)) ∧
    (∀ t : ℝ, f ((t : ℂ) - Complex.I) = inner ℂ (V t ξ) η)

/-- **From RvD Definition 3.4 to the half-strip reality** (RvD Proposition 3.5 applied to `StripKMSrvd`).
    The plain-flip top-edge value `f(t − i) = ⟪V_t ξ, η⟫` of `StripKMSrvd` is automatically `conj(f(t))`:
    by conjugate symmetry `⟪V_t ξ, η⟫ = conj⟪η, V_t ξ⟫`, and `f(t) = ⟪η, V_t ξ⟫` (the corrected RvD Def 3.4
    convention, orbit in the linear slot).  So
    `real_on_midline_of_conj_flip` (RvD Prop 3.5) upgrades the witness to the *half-strip KMS form*: a
    bounded-holomorphic `f` with real-axis value `f(t) = ⟪V_t ξ, η⟫` **and** `f(t − i/2)` REAL — exactly the
    reality input RvD Theorem 3.8 consumes (`Δ^{1/2} = J` on the standard subspace).  This discharges the
    Prop-3.5 step of the `hUniq` proof from the labelled `StripKMSrvd`, axiom-free. -/
theorem stripKMSrvd_real_midline {V : ℝ → (H →L[ℂ] H)} {K : Set H} (hV : StripKMSrvd V K)
    {ξ η : H} (hξ : ξ ∈ K) (hη : η ∈ K) :
    ∃ f : ℂ → ℂ, DiffContOnCl ℂ f (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
      (∀ t : ℝ, f (t : ℂ) = inner ℂ η (V t ξ)) ∧ (∀ t : ℝ, (f ((t : ℂ) - Complex.I / 2)).im = 0) := by
  obtain ⟨f, hfdcc, ⟨M, hfM⟩, hfreal, hfflip⟩ := hV ξ hξ η hη
  refine ⟨f, hfdcc, hfreal, fun t => ?_⟩
  refine QIQTH.StripUniqueness.real_on_midline_of_conj_flip hfdcc (fun z _ => hfM z) (fun s => ?_) t
  rw [hfflip s, hfreal s]
  exact (inner_conj_symm (𝕜 := ℂ) (V s ξ) η).symm

/-- **★ SOUNDNESS AUDIT — `StripKMS` as defined is TRIVIALLY satisfiable, hence too weak to be the KMS
    condition.**  Because the witness `F` is required to be holomorphic only on the *open* strip while the
    boundary values at `Im = 0` and `Im = 1` are imposed *pointwise* (with no continuity linking interior to
    boundary), one may take `F ≡ 0` on the open strip and simply *override* its values on the two boundary
    lines.  So `StripKMS V D` holds for **every** unitary family `V` (given only that `D` is dense).

    Consequence: the labelled `hStrip` of `oneParticleBW_of_kms`/`oneParticleBW_wedge` is vacuous, so the
    *only* real content there is the `hUniq` hypothesis — which, with a trivially-true `StripKMS`, asserts
    "invariance ⟹ V = Δ^{it}", a FALSE statement (many `𝒦`-invariant unitary groups are not the modular
    flow).  The honest fix is to strengthen `StripKMS` to a *bounded, continuous-to-the-closure* holomorphic
    extension (`DiffContOnCl` + a uniform bound — the regularity now available via
    `diffContOnCl_modCorrExt`/`modCorrExt_norm_le`) and to use the correct **Δ-weighted** top edge
    (`modCorrExt_kms_flip`: `F(t+i) = ∫ modChar t (ω)·(ω/(2−ω)) dμ`), not the plain flip.  This theorem
    records the defect, machine-checked, so the one-particle BW conditional is not read as resting on a
    genuine analytic fact while `StripKMS` stands as written. -/
theorem stripKMS_trivial {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : ℝ → (H →L[ℂ] H)) {D : Set H} (hD : Dense D) : StripKMS V D := by
  refine ⟨hD, fun ξ _ η _ => ⟨fun z => if z.im = 0 then inner ℂ ξ (V z.re η)
      else if z.im = 1 then inner ℂ η (V z.re ξ) else 0, ?_, ?_, ?_⟩⟩
  · refine (differentiableOn_const (0 : ℂ)).congr (fun z hz => ?_)
    obtain ⟨h0, h1⟩ := hz
    rw [if_neg (ne_of_gt h0), if_neg (ne_of_lt h1)]
  · intro t
    simp only [Complex.ofReal_im, Complex.ofReal_re, ↓reduceIte]
  · intro t
    have him : ((t : ℂ) + Complex.I).im = 1 := by simp
    have hre : ((t : ℂ) + Complex.I).re = t := by simp
    simp only [him, hre, one_ne_zero, ↓reduceIte]

/-- **★ Conditional one-particle Bisognano–Wichmann (KMS-uniqueness route).**  For a standard subspace
    `S` and a strongly-continuous unitary group `V`, GIVEN the two labelled AQFT facts that current
    Mathlib cannot prove (kept as explicit hypotheses, NEVER Lean axioms):
    * `hUniq` — the **KMS-uniqueness lemma** for standard subspaces (BGL §2): a `V` that leaves `S`
      invariant and has the KMS strip property IS the modular group;
    * `hStrip` — the **strip/KMS property** of `V` (`StripKMS`, BGL §4);
    together with the boost-INVARIANCE `hInv` (which is PROVED for the wedge subspace,
    `boostUnitary_mapsTo_wedgeSubspace`), the modular flow equals `V`: `modUnitary S t = V t`.

    Instantiated at `S = 𝒦_W`, `V t = boostUnitary(−2π t)` this gives
    `modUnitary 𝒦_W t = boostUnitary(−2π t)` — the one-particle BW identification, hence the `hFlux`
    input of `qiqt_bekenstein_gives_gr` DERIVED modulo exactly these two labelled, citable AQFT facts.
    The genuine contribution is that the invariance is *derived* (not assumed); only the two analytic
    facts remain labelled. -/
theorem oneParticleBW_of_kms (S : StandardSubspace H)
    (V : ℝ → (H →L[ℂ] H)) {D : Set H}
    (hUniq : (∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H)) →
             StripKMS V D → ∀ t, modUnitary S t = V t)
    (hInv : ∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H))
    (hStrip : StripKMS V D) :
    ∀ t, modUnitary S t = V t :=
  hUniq hInv hStrip

/-- The **half-strip reality form** of the KMS condition (the output of RvD Proposition 3.5): for `ξ, η ∈ K`,
    a bounded-holomorphic `f` on `{−1 < Im z < 0}` with `f(t) = ⟪V_t ξ, η⟫` and `f(t − i/2)` REAL.  This is the
    reality input RvD Theorem 3.8 actually consumes; it is PROVABLE from `StripKMSrvd`
    (`stripKMSrvd_halfStripReal`, via Prop 3.5), so labelling it instead of all of `StripKMS` shrinks the
    unproven surface to exactly the Theorem-3.8 core. -/
def HalfStripReal (V : ℝ → (H →L[ℂ] H)) (K : Set H) : Prop :=
  ∀ ξ ∈ K, ∀ η ∈ K, ∃ f : ℂ → ℂ, DiffContOnCl ℂ f (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
    (∀ t : ℝ, f (t : ℂ) = inner ℂ η (V t ξ)) ∧ (∀ t : ℝ, (f ((t : ℂ) - Complex.I / 2)).im = 0)

/-- **`StripKMSrvd` ⟹ `HalfStripReal`** — RvD Proposition 3.5, packaged: the correct full-strip KMS condition
    yields the half-strip reality form (each pair's witness made real on the mid-line). -/
theorem stripKMSrvd_halfStripReal {V : ℝ → (H →L[ℂ] H)} {K : Set H} (hV : StripKMSrvd V K) :
    HalfStripReal V K := fun ξ hξ η hη => stripKMSrvd_real_midline hV hξ hη

/-- **★ Conditional one-particle Bisognano–Wichmann via the CORRECT RvD KMS condition (narrowed core).**
    Replaces the vacuous `StripKMS` of `oneParticleBW_of_kms` with the genuine `StripKMSrvd` (RvD Def 3.4), and
    narrows the single labelled hypothesis to the **RvD Theorem 3.8 core** `hThm38` (half-strip reality +
    `𝒦`-invariance ⟹ modular flow).  The Proposition-3.5 reduction (`StripKMSrvd ⟹ HalfStripReal`) is now
    DISCHARGED axiom-free (`stripKMSrvd_halfStripReal`), so the unproven surface is exactly the Theorem-3.8
    g-function assembly — strictly smaller and more honest than the `StripKMS`/`hUniq` formulation. -/
theorem oneParticleBW_of_stripKMSrvd (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H))
    (hThm38 : (∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H)) →
              HalfStripReal V (S.toClosedSubmodule : Set H) → ∀ t, modUnitary S t = V t)
    (hInv : ∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H))
    (hKMS : StripKMSrvd V (S.toClosedSubmodule : Set H)) :
    ∀ t, modUnitary S t = V t :=
  hThm38 hInv (stripKMSrvd_halfStripReal hKMS)

/-- The **comparison datum** — the exact OUTPUT of RvD Theorem 3.8's `g`-function: for every `t`, `η ∈ 𝒦`,
    and `w ⊥ i𝒦` (`projIK w = 0`), `⟪w, V_t η⟫ = ⟪w, Δ^{it} η⟫`.  This is the single relation that the
    (source-garbled) `g`-pairing / Prop-3.7-device argument produces from the half-strip reality; everything
    downstream of it — `V_t η = Δ^{it} η` on `𝒦` (`IsSeparating`) and the lift to `Δ^{it} = V_t`
    (`IsCyclic`) — is the already-proven `modUnitary_eq_of_orbit_compare`. -/
def ComparisonDatum (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H)) : Prop :=
  ∀ t : ℝ, ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ w : H,
    QIQTH.StandardSubspaceModular.projIK S w = 0 →
    inner ℂ w (V t η) = inner ℂ w (modUnitary S t η)

/-- **★ Conditional one-particle BW with the TIGHTEST honest labelling.**  Everything provable is now proved:
    the Proposition-3.5 reduction (`stripKMSrvd_halfStripReal`), the `Δ`-invariance (`modUnitary_mapsTo_K`),
    and the operator assembly (`modUnitary_eq_of_orbit_compare`: separating ⇒ equal on `𝒦`, cyclic ⇒ equal
    everywhere).  The SOLE labelled hypothesis `hCompare` is the exact `g`-function output
    `HalfStripReal ⟹ ComparisonDatum` — the only genuinely source-garbled step of RvD Theorem 3.8.  This is
    the minimal honest statement of "what remains unproven" on the `hUniq` discharge route. -/
theorem oneParticleBW_of_comparison (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H))
    (hCompare : HalfStripReal V (S.toClosedSubmodule : Set H) → ComparisonDatum S V)
    (hInv : ∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H))
    (hKMS : StripKMSrvd V (S.toClosedSubmodule : Set H)) :
    ∀ t, modUnitary S t = V t := by
  have hcmp : ComparisonDatum S V := hCompare (stripKMSrvd_halfStripReal hKMS)
  intro t
  exact QIQTH.StandardSubspaceModular.modUnitary_eq_of_orbit_compare S t
    (fun η hη => hInv t hη) (fun η hη => modUnitary_mapsTo_K S t η hη)
    (fun η hη w hw => hcmp t η hη w hw)

/-- **Non-vacuity / consistency of the narrowed conditional.**  The modular flow `V = Δ^{it}` itself satisfies
    `ComparisonDatum` (trivially: `⟪w, Δ^{it} η⟫ = ⟪w, Δ^{it} η⟫`).  So the labelled `hCompare` of
    `oneParticleBW_of_comparison` has a *consistent* conclusion — `Δ` is a model — confirming the formulation is
    not a vacuous-premise artifact: its content is the genuine UNIQUENESS (any KMS `V` equals `Δ`), not an empty
    hypothesis.  (`Δ` also satisfies the invariance `modUnitary_mapsTo_K`; with this, the conditional at `V = Δ`
    consistently yields `modUnitary = modUnitary`.) -/
theorem comparisonDatum_modUnitary (S : StandardSubspace H) :
    ComparisonDatum S (modUnitary S) := fun _ _ _ _ _ => rfl

/-- The **g-function constancy output** (RvD Theorem 3.8, the analytic conclusion): for `ξ, η ∈ 𝒦`,
    `⟪V_t η, Δ^{it} J ξ⟫ = ⟪η, J ξ⟫`.  This is exactly what the (analytic) g-function
    `g(z) = ⟨h(z), J d_z(R) ζ⟩` produces by being constant on the half-strip — `g(t) = ⟨U_t η, JΔ^{it}ξ⟩`
    (top edge, real), `g(0) = ⟨η, Jξ⟩` — using `Δ^{it}J = JΔ^{it}` (`modConj_commute_modUnitary`). -/
def GConstancy (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H)) : Prop :=
  ∀ t : ℝ, ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ ξ ∈ (S.toClosedSubmodule : Set H),
    inner ℂ (V t η) (modUnitary S t (modConj S ξ)) = inner ℂ η (modConj S ξ)

/-- **The g-function constancy output yields `ComparisonDatum`** — the operator-algebra wrapper of RvD
    Theorem 3.8, reducing the discharge to the *analytic* g-constancy alone.  Given `⟪V_t η, Δ^{it} J ξ⟫ =
    ⟪η, J ξ⟫` (∀ξ,η∈𝒦): for `w ⊥ i𝒦` set `ξ = Δ^{−it}(J w) ∈ 𝒦` (`J w ∈ 𝒦` since `J𝒦 = (i𝒦)^⊥`,
    `Δ^{−it}` preserves `𝒦`).  Then `J ξ = Δ^{−it} w` and `Δ^{it} J ξ = w` (`JΔ^{it}=Δ^{it}J` + group law), so
    g-constancy reads `⟪V_t η, w⟫ = ⟪η, Δ^{−it} w⟫ = ⟪Δ^{it} η, w⟫` (adjoint); conjugating gives
    `⟪w, V_t η⟫ = ⟪w, Δ^{it} η⟫`.  The `⟪η,Jξ⟫` right-hand side carries the `Δ`-side automatically — no
    separate `Δ`-version needed.  So the ONLY remaining unproven step is the analytic g-constancy itself. -/
theorem comparisonDatum_of_gConstancy (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H))
    (hG : GConstancy S V) : ComparisonDatum S V := by
  intro t η hη w hw
  have hJwK : projK S (modConj S w) = modConj S w :=
    projK_modConj_eq_self_of_perp_IK S hw
  set ξ := modUnitary S (-t) (modConj S w) with hξdef
  have hξmem : ξ ∈ (S.toClosedSubmodule : Set H) :=
    modUnitary_mapsTo_K S (-t) _ ((mem_K_iff_projK S _).mpr hJwK)
  have hmc : modConj S ξ = modUnitary S (-t) w := by
    rw [hξdef, modConj_commute_modUnitary S (-t) (modConj S w), modConj_sq]
  have hkey : modUnitary S t (modConj S ξ) = w := by
    rw [hmc, ← ContinuousLinearMap.mul_apply, ← modUnitary_add S t (-t), add_neg_cancel,
      modUnitary_zero, ContinuousLinearMap.one_apply]
  have hg := hG t η hη ξ hξmem
  rw [hkey, hmc, ← modUnitary_adjoint S t, ContinuousLinearMap.adjoint_inner_right] at hg
  rw [← inner_conj_symm w (V t η), ← inner_conj_symm w (modUnitary S t η)]
  exact congrArg (starRingEnd ℂ) hg

open Filter in
/-- **Full `GConstancy` from the two named RvD inputs** (the end-to-end assembly of the device g-function
    discharge).  Given a strongly-continuous contraction group `V` (`hcont`/`hbd`/`hgrp`/`hV0`), the orbit
    invariance of `𝒦` (`hKinv`), the **bottom-edge KMS reality** `h1` (the mid-line `Im z = −1/2` reality of the
    device g-function, supplied by `HalfStripReal`), and the **`√R`-range density in `𝒦`** `hdense` (every
    `ξ ∈ 𝒦` is a limit of `√R ζ_k ∈ 𝒦`, available since `R` is injective), the `GConstancy` proposition holds.
    Chains `gConstancy_eta_of_bottom` (η-side, `h1`) → `gConstancy_xi_of_density` (ξ-side, `hdense`).  Together
    with `comparisonDatum_of_gConstancy` this is the complete RvD Theorem 3.8 g-function argument, reducing the
    `hUniq` discharge to exactly the two named inputs — every analytic and density step machine-checked. -/
theorem gConstancy_of_inputs (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H))
    (hcont : ∀ η ∈ (S.toClosedSubmodule : Set H), Continuous (fun t => V t η))
    (hbd : ∀ η : H, ∀ t, ‖V t η‖ ≤ ‖η‖) (hgrp : ∀ η : H, ∀ s t, V s (V t η) = V (s + t) η)
    (hV0 : ∀ η : H, V 0 η = η)
    (hKinv : ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ n : ℝ, 0 < n → ∀ s : ℝ,
      projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    (h1 : ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ ζ : H,
      projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ → ∀ n : ℝ, 0 < n → ∀ z : ℂ, z.im = -(1 / 2) →
        (modConjBilin S (QIQTH.deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0)
    (hdense : ∀ ξ ∈ (S.toClosedSubmodule : Set H), ∃ ζs : ℕ → H,
      (∀ k, projK S (rvdSqrtR S (ζs k)) = rvdSqrtR S (ζs k)) ∧
        Tendsto (fun k => rvdSqrtR S (ζs k)) atTop (nhds ξ)) :
    GConstancy S V := by
  intro t η hη ξ hξ
  exact gConstancy_xi_of_density S η t
    (fun ζ hsq => gConstancy_eta_of_bottom S ζ η (hcont η hη) (hbd η) (hgrp η) (hV0 η) hsq
      (hKinv η hη) (h1 η hη ζ hsq) t) hdense ξ hξ

open Filter in
/-- **★ One-particle Bisognano–Wichmann via the device g-function, reduced to the two named RvD inputs.**
    The modular flow IS the candidate flow, `modUnitary S t = V t`, GIVEN: the strongly-continuous contraction
    group `V` with `𝒦`-invariance (`hInv`), the correct full-strip KMS condition (`hKMS : StripKMSrvd`), and
    the two RvD Theorem 3.8 inputs that drive the g-function — the **bottom-edge KMS reality** `h1` (mid-line
    `Im z = −1/2` reality) and the **`√R`-range density in `𝒦`** `hdense`.  `gConstancy_of_inputs` yields the
    full `GConstancy`, `comparisonDatum_of_gConstancy` the `ComparisonDatum`, and `oneParticleBW_of_comparison`
    the flow identification.  This is the COMPLETE device g-function discharge of `hUniq`: every analytic,
    constancy, and density step machine-checked and axiom-free, the labelled surface narrowed to exactly
    `h1` + `hdense`. -/
theorem oneParticleBW_of_inputs (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H))
    (hcont : ∀ η ∈ (S.toClosedSubmodule : Set H), Continuous (fun t => V t η))
    (hbd : ∀ η : H, ∀ t, ‖V t η‖ ≤ ‖η‖) (hgrp : ∀ η : H, ∀ s t, V s (V t η) = V (s + t) η)
    (hV0 : ∀ η : H, V 0 η = η)
    (hKinv : ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ n : ℝ, 0 < n → ∀ s : ℝ,
      projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    (h1 : ∀ η ∈ (S.toClosedSubmodule : Set H), ∀ ζ : H,
      projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ → ∀ n : ℝ, 0 < n → ∀ z : ℂ, z.im = -(1 / 2) →
        (modConjBilin S (QIQTH.deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0)
    (hdense : ∀ ξ ∈ (S.toClosedSubmodule : Set H), ∃ ζs : ℕ → H,
      (∀ k, projK S (rvdSqrtR S (ζs k)) = rvdSqrtR S (ζs k)) ∧
        Tendsto (fun k => rvdSqrtR S (ζs k)) atTop (nhds ξ))
    (hInv : ∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set H) (S.toClosedSubmodule : Set H))
    (hKMS : StripKMSrvd V (S.toClosedSubmodule : Set H)) :
    ∀ t, modUnitary S t = V t :=
  oneParticleBW_of_comparison S V
    (fun _ => comparisonDatum_of_gConstancy S V
      (gConstancy_of_inputs S V hcont hbd hgrp hV0 hKinv h1 hdense))
    hInv hKMS

/-- **Top-edge reality of the g-function** (RvD Theorem 3.8, the real-axis edge `g(t) = ⟪U_t η, Δ^{it} J ξ⟫`
    is real).  For `ξ, η ∈ 𝒦` with `V_t η ∈ 𝒦`: `Δ^{it} J ξ = J(Δ^{it} ξ)` (`modConj_commute_modUnitary`)
    lies in `(i𝒦)^⊥` (since `Δ^{it}ξ ∈ 𝒦` and `J𝒦 = (i𝒦)^⊥`), so pairing it against `V_t η ∈ 𝒦` is real
    (`inner_real_of_mem_K_perp_IK`, RvD Prop 2.3).  This is geometric — no analysis; it is the real-axis edge
    of the genuine *device-vector* g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩` (unlike the discredited fixed-`Jξ`
    `corrJ`, here the second-slot vector is the `z`-varying `Δ^{it}Jξ`). -/
theorem gTopEdge_real (S : StandardSubspace H) (V : ℝ → (H →L[ℂ] H)) (t : ℝ) {ξ η : H}
    (hξ : projK S ξ = ξ) (hVη : projK S (V t η) = V t η) :
    (inner ℂ (V t η) (modUnitary S t (modConj S ξ))).im = 0 := by
  rw [(modConj_commute_modUnitary S t ξ).symm]
  exact inner_real_of_mem_K_perp_IK S hVη (projIK_modConj_eq_zero_of_mem_K S
    ((mem_K_iff_projK S _).mp (modUnitary_mapsTo_K S t ξ ((mem_K_iff_projK S ξ).mpr hξ))))

end ConditionalBW

/-- **★ One-particle Bisognano–Wichmann for the WEDGE subspace (boost-invariance supplied from the
    proved lemma).**  For a standard subspace `S` on the one-particle space whose real subspace is the
    physical wedge subspace `𝒦_W = closure(span_ℝ wedgeGenSet)` (`hcarrier` — the *standardness* of `𝒦_W`
    is what makes `S` a `StandardSubspace`, the one-particle Reeh–Schlieder input), and a unitary group
    `V t = boostUnitary(−2π t)` (`hVboost`): GIVEN the KMS-uniqueness lemma (`hUniq`, BGL §2) and the
    strip property (`hStrip`, BGL §4), the modular flow IS the boost: `modUnitary S t = V t`.

    The boost-INVARIANCE that `oneParticleBW_of_kms` needs is here DISCHARGED from the proved
    `boostUnitary_mapsTo_wedgeSubspace` (via `hcarrier` + `hVboost`) — so the wedge instance rests only on
    the labelled AQFT facts, with the invariance derived.  This is `modUnitary 𝒦_W = boostUnitary(−2π·)`,
    the one-particle BW identification ⇒ the `hFlux` input of `qiqt_bekenstein_gives_gr`. -/
theorem oneParticleBW_wedge (m : ℝ)
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (V : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) {D : Set _}
    (hcarrier : (S.toClosedSubmodule : Set (Lp ℂ 2 (volume : Measure ℝ)))
        = closure (Submodule.span ℝ (wedgeGenSet m) : Set (Lp ℂ 2 (volume : Measure ℝ))))
    (hVboost : ∀ t x, V t x = boostUnitary (-(2 * Real.pi * t)) x)
    (hUniq : (∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set _) (S.toClosedSubmodule : Set _)) →
             StripKMS V D → ∀ t, modUnitary S t = V t)
    (hStrip : StripKMS V D) :
    ∀ t, modUnitary S t = V t := by
  refine oneParticleBW_of_kms S V hUniq ?_ hStrip
  intro t x hx
  rw [hVboost t x, hcarrier] at *
  exact boostUnitary_mapsTo_wedgeSubspace m (-(2 * Real.pi * t)) hx

/-! ### The field-level BW: the second-quantized modular flow IS Γ of the boost -/

/-- **★ The field-level Bisognano–Wichmann (functorial lift).**  Once the one-particle BW
    `modUnitary S t = V t` holds at the isometry level (`hbw`), the second-quantized modular flow
    `Γ(Δ^{it}) = secondQuantModFlow S t` equals `Γ(V t) = secondQuantPre (V t)` — the field-level
    modular automorphism IS `Γ` of the boost.  This carries the BW identification from the one-particle
    space to the Fock/field algebra, the first step of the stress-flux bridge (the field modular
    Hamiltonian = the field boost generator). -/
theorem secondQuantModFlow_eq_of_bw {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {S : StandardSubspace H} (W : ℝ → (H →ₗᵢ[ℂ] H))
    (hbw : ∀ t, QIQTH.Fock.modUnitaryₗᵢ S t = W t) :
    ∀ t, QIQTH.Fock.secondQuantModFlow S t = QIQTH.Fock.secondQuantPre (W t) := fun t => by
  rw [QIQTH.Fock.secondQuantModFlow, hbw t]

/-- **★★ The field-level Bisognano–Wichmann (geometric action).**  Given the one-particle BW at the
    vector level (`hbw : modUnitary S t u = boostUnitary(−2π t) u`), the modular automorphism
    `σ_t = Γ(Δ^{it})` acts on the Weyl operators by the **geometric Lorentz boost**:
    `σ_t(W(u) x) = W(boostUnitary(−2π t) u)(σ_t x)`.  i.e. the modular flow of the wedge IS the boost,
    implemented on the field algebra — the genuine content of Bisognano–Wichmann.  From the project's
    Tomita covariance `secondQuantModFlowH_weylH` (σ_t(W(u))=W(Δ^{it}u)) + the BW identification. -/
theorem secondQuantModFlowH_acts_as_boost
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
        QIQTH.StandardSubspaceModular.modUnitary S t u = boostUnitary (-(2 * Real.pi * t)) u)
    (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (x : QIQTH.Fock.Fock (Lp ℂ 2 (volume : Measure ℝ))) :
    QIQTH.Fock.secondQuantModFlowH S t (QIQTH.Fock.weylH u x)
      = QIQTH.Fock.weylH (boostUnitary (-(2 * Real.pi * t)) u)
          (QIQTH.Fock.secondQuantModFlowH S t x) := by
  rw [QIQTH.Fock.secondQuantModFlowH_weylH, hbw t u]

/-- **★ Modular energy = boost energy (derivative level), via BW.**  Given the one-particle BW
    `modUnitary S t u = boostUnitary(−2π t) u`, the modular-energy correlation `t ↦ ⟪ξ, Δ^{it} ξ⟫`
    coincides with the boost-energy correlation `t ↦ ⟪ξ, boostUnitary(−2π t) ξ⟫` as functions of `t`, so
    their derivatives at `0` agree.  The modular energy `kd = d/dt⟪ξ,Δ^{it}ξ⟫|₀` (the object feeding
    `hFlux`) therefore equals the boost energy derivative — reducing `hFlux` (modular energy = stress
    flux) to the standard **boost-charge = stress-flux** identity `δ⟨boost⟩ = ∫λ T_kk`, the one remaining
    labelled geometric fact.  No unbounded generator needed: the equality is a direct congruence from BW. -/
theorem hasDerivAt_modularEnergy_of_boost
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
        QIQTH.StandardSubspaceModular.modUnitary S t u = boostUnitary (-(2 * Real.pi * t)) u)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ)
    (h : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ)) c 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ)) c 0 := by
  have heq : (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ))
      = (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ)) := by
    funext t; rw [hbw t ξ]
  rw [heq]; exact h

/-- **★ One-particle `hFlux`: the modular energy IS `(2π/ℏ)·(stress flux)`** — `hFlux` derived from the BW
    plus the labelled boost-charge identity.  `hBoostCharge` is the single remaining labelled input on
    this path: the **boost-charge = stress-flux** identity `δ⟨boost⟩ = (2π/ℏ)·T_kk` (the conserved
    Killing charge of the boost equals the stress-tensor flux — standard field theory, needs the field
    stress tensor which the project has not built, so labelled).  Composed with the *proved*
    `hasDerivAt_modularEnergy_of_boost` (modular energy = boost energy, via BW), it gives the modular
    energy derivative `= (2π/ℏ)·T_kk` — exactly the `hFlux` of `qiqt_bekenstein_gives_gr` at the
    one-particle (Hilbert) level.  So `hFlux`'s modular content is DERIVED; only the Killing-charge
    identity (and the one-particle↔component `Krep` bridge) remain labelled. -/
theorem modularEnergy_eq_stressFlux
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
        QIQTH.StandardSubspaceModular.modUnitary S t u = boostUnitary (-(2 * Real.pi * t)) u)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (hbar Tkk : ℝ)
    (hBoostCharge : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ))
        (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ))
        (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0 :=
  hasDerivAt_modularEnergy_of_boost S hbw ξ _ hBoostCharge

/-- **★★★ The one-particle `hFlux`, fully assembled from the labelled inputs.**  From exactly the
    labelled, citable physics facts — `hcarrier`/standardness (`𝒦_W` is a standard subspace, Reeh–
    Schlieder), `hUniq` (KMS-uniqueness, BGL §2), `hStrip` (the wedge strip/KMS property, BGL §4), and
    `hBoostCharge` (boost-charge = stress-flux) — the modular-energy derivative equals `(2π/ℏ)·T_kk`,
    i.e. the `hFlux` of `qiqt_bekenstein_gives_gr` at the one-particle level.  EVERYTHING geometric and
    modular is derived inside: the boost-invariance of `𝒦_W`, the BW identification
    `modUnitary 𝒦_W = boostUnitary` (via `oneParticleBW_wedge`), and modular-energy = boost-energy.  So
    `hFlux`'s deep content is derived; only the standard labelled facts above remain.  No Lean axioms. -/
theorem oneParticle_hFlux (m : ℝ)
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (V : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) {D : Set _}
    (hcarrier : (S.toClosedSubmodule : Set (Lp ℂ 2 (volume : Measure ℝ)))
        = closure (Submodule.span ℝ (wedgeGenSet m) : Set (Lp ℂ 2 (volume : Measure ℝ))))
    (hVboost : ∀ t x, V t x = boostUnitary (-(2 * Real.pi * t)) x)
    (hUniq : (∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set _) (S.toClosedSubmodule : Set _)) →
             StripKMS V D → ∀ t, QIQTH.StandardSubspaceModular.modUnitary S t = V t)
    (hStrip : StripKMS V D)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (hbar Tkk : ℝ)
    (hBoostCharge : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ))
        (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0) :
    HasDerivAt (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ))
        (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0 := by
  have hone := oneParticleBW_wedge m S V hcarrier hVboost hUniq hStrip
  have hbw : ∀ (t : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)),
      QIQTH.StandardSubspaceModular.modUnitary S t u = boostUnitary (-(2 * Real.pi * t)) u := by
    intro t u
    rw [show QIQTH.StandardSubspaceModular.modUnitary S t = V t from hone t]
    exact hVboost t u
  exact modularEnergy_eq_stressFlux S hbw ξ hbar Tkk hBoostCharge

/-! ### The one-particle ↔ component bridge — landing `hFlux` at the chain's real component level -/

/-- **★★★ The component-level `hFlux`, derived from the wedge-KMS property + the standard localization.**
    This is the bridge from the one-particle (Hilbert) `hFlux` to the *real, component-level* `hFlux`
    `kd = (2π/ℏ)·T_kk` that `qiqt_bekenstein_gives_gr` actually consumes per null generator.

    The chain's modular-energy derivative `kd : ℝ` is, physically, the imaginary-derivative coefficient of
    the localized correlation `t ↦ ⟪ξ, Δ^{it} ξ⟫` (for a unitary group the derivative is `i·(real energy)`).
    `hbridge` is exactly that labelled localization identity — "the chain's null-generator modular energy IS
    the one-particle modular energy of the wedge state `ξ = ξ_{x,v}`."  Given it together with the
    wedge-KMS inputs and the boost-charge identity, `oneParticle_hFlux` pins the same correlation's
    derivative to `i·(2π/ℏ)·T_kk`; uniqueness of the derivative (`HasDerivAt.unique`) then forces
    `i·kd = i·(2π/ℏ)·T_kk`, and cancelling `i` + real-cast injectivity gives the component identity
    `kd = (2π/ℏ)·T_kk`.

    So the entire modular surface of `hFlux` — the BW identification, modular-energy = boost-energy, and
    the descent to the real component coefficient — is **derived**, resting only on the labelled wedge-KMS
    property (`hUniq`,`hStrip`,standardness), the boost-charge = stress-flux identity (`hBoostCharge`), and
    the localization identity (`hbridge`).  All three belong to the single "wedge KMS property + its
    standard localization" input.  No Lean axioms. -/
theorem component_hFlux_of_wedgeKMS (m : ℝ)
    (S : StandardSubspace (Lp ℂ 2 (volume : Measure ℝ)))
    (V : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))) {D : Set _}
    (hcarrier : (S.toClosedSubmodule : Set (Lp ℂ 2 (volume : Measure ℝ)))
        = closure (Submodule.span ℝ (wedgeGenSet m) : Set (Lp ℂ 2 (volume : Measure ℝ))))
    (hVboost : ∀ t x, V t x = boostUnitary (-(2 * Real.pi * t)) x)
    (hUniq : (∀ t, Set.MapsTo (V t) (S.toClosedSubmodule : Set _) (S.toClosedSubmodule : Set _)) →
             StripKMS V D → ∀ t, QIQTH.StandardSubspaceModular.modUnitary S t = V t)
    (hStrip : StripKMS V D)
    (ξ : Lp ℂ 2 (volume : Measure ℝ)) (hbar kd Tkk : ℝ)
    (hBoostCharge : HasDerivAt (fun t : ℝ => inner ℂ ξ (boostUnitary (-(2 * Real.pi * t)) ξ))
        (Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ)) 0)
    (hbridge : HasDerivAt (fun t : ℝ => inner ℂ ξ (QIQTH.StandardSubspaceModular.modUnitary S t ξ))
        (Complex.I * ((kd : ℝ) : ℂ)) 0) :
    kd = 2 * Real.pi / hbar * Tkk := by
  have hHil := oneParticle_hFlux m S V hcarrier hVboost hUniq hStrip ξ hbar Tkk hBoostCharge
  have huniq : Complex.I * ((kd : ℝ) : ℂ) = Complex.I * ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ) :=
    hbridge.unique hHil
  have hcast : ((kd : ℝ) : ℂ) = ((2 * Real.pi / hbar * Tkk : ℝ) : ℂ) :=
    mul_left_cancel₀ Complex.I_ne_zero huniq
  exact_mod_cast hcast

end QIQTH.Fock.OneParticleBW
