import QIQTH.StandardSubspaceModularFlow
import QIQTH.Fock.Localization
import QIQTH.Fock.OneParticle
import QIQTH.Fock.SecondQuantModularFlow

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

end QIQTH.Fock.OneParticleBW
