import QIQTH.StandardSubspaceModularFlow
import QIQTH.Fock.Localization
import QIQTH.Fock.OneParticle

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

end QIQTH.Fock.OneParticleBW
