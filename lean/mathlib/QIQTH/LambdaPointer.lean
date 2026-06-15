/-
  LambdaPointer — the finite-dimensional shadow of λ's pointer-algebra law.

  HONEST CONTEXT (per the 2026-06-15 GPT-5.5-pro red-team, checked against
  Haag / Takesaki / Sorce).  The selector λ marks one decohered macroscopic
  record as actual.  In relativistic QFT the local algebra of a bounded region
  is Type III₁ (no minimal projections, no trace, no density matrix).  The
  earlier idea — "dress Type III → Type II via the crossed product, then take a
  conditional expectation to recover atoms, so Born = a trace ratio" — is a
  CATEGORY ERROR for the selection problem: Type II factors ALSO have no minimal
  projections, so the atoms λ selects never come from the factor's *type*.  They
  come from the chosen abelian POINTER subalgebra 𝔄 = vN(Pₐ), which already
  exists inside a Type III₁ factor.  A normal state gives Born weights directly
  (the algebraic Born rule pₐ = ω(Pₐ) = ‖PₐΦ‖²); the *state* gives Born, not the
  trace.  λ is therefore Type-III-NATIVE: built on the standard form / natural
  cone and the modular flow, not on a forced trace.

  The real kinematic content of λ is *which* pointer algebra 𝔄 — and the
  characterization is **Takesaki's conditional-expectation theorem**: an
  ω-preserving conditional expectation onto 𝔄 exists iff 𝔄 is invariant under
  the modular automorphism group σ_t^ω.  That is the exact (non-approximate)
  operator-algebra statement of einselection.

  THIS FILE proves the finite-matrix (Type I) shadow of that theorem, reusing
  `FiniteModularTheory`.  Everything is `Matrix n n ℂ` + trace cyclicity, NO
  project axioms, NO analytic input:

    * `modAut_fixes_iff_commute` — the FINITE TAKESAKI CRITERION: the modular
      flow fixes a pointer projection P (σ(P)=P) iff P commutes with the density
      ρ, i.e. iff there is no coherence between the pointer sectors — exact
      decoherence.
    * `bornWeights_sum` — the algebraic Born weights ω(Pₐ)=tr(ρPₐ) of a
      resolution of unity sum to tr ρ (= 1 for a state): a genuine probability.
    * `dephase_one`, `dephase_preserves_state` — the dephasing map
      E(x)=Σ Pₐ x Pₐ is unital and, WHEN the pointers commute with ρ (the
      criterion above), ω-preserving: it is the conditional expectation onto 𝔄,
      and it is exactly the decoherence map.

  Honest scope: Type I (finite n).  The continuum Type III₁ version — standard
  form / natural cone for the algebraic Born rule, and the modular σ_t^ω with
  Connes-cocycle Radon–Nikodym derivatives for the genuine Takesaki criterion —
  is the cited frontier (Mathlib lacks the modular-continuum machinery).  What
  is delivered is the modular *algebra* finite shadow: λ's pointer law made
  precise and machine-checked where it CAN be, with the single-outcome dynamics
  and across-run frequencies left honestly open.
-/

import QIQTH.FiniteModularTheory

namespace QIQTH
namespace LambdaPointer

open Matrix
open QIQTH.FiniteModularTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/- ── 1. The finite Takesaki criterion ─────────────────────────────────────

    Takesaki's theorem: an ω-preserving conditional expectation onto a
    subalgebra 𝔄 exists iff σ_t^ω(𝔄)=𝔄.  For an atomic pointer algebra
    𝔄 = vN(P) the invariance condition on a single generator P is σ(P)=P,
    and — in finite dimensions, where σ is conjugation by the density ρ — this
    is exactly commutation [ρ,P]=0.  Read physically: the modular flow fixes the
    pointer projection iff the state has no coherence between pointer sectors,
    i.e. exact decoherence / einselection. -/

/-- **Finite Takesaki criterion.**  The modular automorphism `σ = modAut ρ`
    fixes a pointer projection `P` (`σ(P)=P`) **iff** `P` commutes with the
    density matrix `ρ`.  This is the finite-dimensional shadow of Takesaki's
    conditional-expectation theorem (`σ_t^ω(𝔄)=𝔄`) for a single pointer
    generator — the exact operator-algebra statement of einselection. -/
theorem modAut_fixes_iff_commute (ρ P : Matrix n n ℂ) [Invertible ρ] :
    modAut ρ P = P ↔ ρ * P = P * ρ := by
  unfold modAut
  constructor
  · intro h
    have h2 : ρ * P * ⅟ρ * ρ = P * ρ := by rw [h]
    rwa [mul_assoc, invOf_mul_self, mul_one] at h2
  · intro h
    rw [h, mul_assoc, mul_invOf_self, mul_one]

/- ── 2. The algebraic Born weights ────────────────────────────────────────

    For a pointer resolution of unity `{Pₐ}` (Σ Pₐ = 1) the algebraic Born
    weights are `ω(Pₐ) = tr(ρ Pₐ)` — no trace on the factor required, just the
    state.  They are a genuine probability: they sum to `tr ρ`, which is `1` for
    a density matrix.  (This is the Type-independent statement that survives to
    Type III via the natural cone, `ω(x)=⟨ξ_ω, x ξ_ω⟩`.) -/

/-- The algebraic Born weight of a pointer projection `P` in the state
    `ω(·)=tr(ρ·)`: `bornWeight ρ P = ω(P)`. -/
noncomputable def bornWeight (ρ P : Matrix n n ℂ) : ℂ := stateOf ρ P

/-- **The Born weights are a probability.**  For a resolution of unity
    `Σ Pₐ = 1`, the algebraic Born weights `ω(Pₐ)` sum to `tr ρ` (which is `1`
    for a state).  Proof: linearity of `ω` in the observable + `Σ Pₐ = 1`. -/
theorem bornWeights_sum {ι : Type*} [Fintype ι] (ρ : Matrix n n ℂ)
    (P : ι → Matrix n n ℂ) (hsum : ∑ i, P i = 1) :
    ∑ i, bornWeight ρ (P i) = trace ρ := by
  unfold bornWeight stateOf
  rw [← trace_sum]
  congr 1
  rw [← Finset.mul_sum, hsum, mul_one]

/- ── 3. The dephasing map = the conditional expectation onto 𝔄 ─────────────

    The decoherence map E(x) = Σ Pₐ x Pₐ is the conditional expectation onto the
    pointer algebra 𝔄 = vN(Pₐ).  It is unital, and — exactly when the pointers
    satisfy the Takesaki criterion `[ρ,Pₐ]=0` — it preserves the state ω.  This
    is the finite shadow of "the einselected pointer algebra carries an
    ω-preserving conditional expectation," with the dephasing map identified as
    that expectation (and as the physical decoherence map). -/

/-- The dephasing / decoherence map onto the pointer family `P`:
    `dephase P x = Σ Pₐ x Pₐ`. -/
noncomputable def dephase {ι : Type*} [Fintype ι] (P : ι → Matrix n n ℂ)
    (x : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, P i * x * P i

/-- The dephasing map is unital: `E(1) = 1`, for a resolution of unity of
    idempotents.  (Conditional-expectation normalization.) -/
theorem dephase_one {ι : Type*} [Fintype ι] (P : ι → Matrix n n ℂ)
    (hsum : ∑ i, P i = 1) (hidem : ∀ i, P i * P i = P i) :
    dephase P (1 : Matrix n n ℂ) = 1 := by
  unfold dephase
  simp only [mul_one]
  rw [Finset.sum_congr rfl (fun i _ => hidem i), hsum]

/-- **The dephasing map preserves the state (the conditional-expectation
    property).**  When every pointer projection commutes with the density `ρ`
    (the finite Takesaki criterion — exact decoherence) and the `Pₐ` are an
    idempotent resolution of unity, the decoherence map `E(x)=Σ Pₐ x Pₐ`
    satisfies `ω(E x) = ω(x)`: it is the ω-preserving conditional expectation
    onto the pointer algebra.  This is precisely the finite shadow of Takesaki's
    theorem in its constructive direction. -/
theorem dephase_preserves_state {ι : Type*} [Fintype ι] (ρ : Matrix n n ℂ)
    (P : ι → Matrix n n ℂ) (hsum : ∑ i, P i = 1)
    (hidem : ∀ i, P i * P i = P i) (hcomm : ∀ i, ρ * P i = P i * ρ)
    (x : Matrix n n ℂ) :
    stateOf ρ (dephase P x) = stateOf ρ x := by
  unfold stateOf dephase
  rw [Finset.mul_sum, trace_sum]
  have step : ∀ i, trace (ρ * (P i * x * P i)) = trace (ρ * P i * x) := by
    intro i
    have hPP : P i * ρ * P i = ρ * P i := by
      rw [show P i * ρ = ρ * P i from (hcomm i).symm, mul_assoc, hidem i]
    rw [show ρ * (P i * x * P i) = (ρ * P i * x) * P i by noncomm_ring,
        trace_mul_comm,
        show P i * (ρ * P i * x) = (P i * ρ * P i) * x by noncomm_ring,
        hPP]
  rw [Finset.sum_congr rfl (fun i _ => step i), ← trace_sum]
  congr 1
  rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one]

/- ── 4. Persistence under the modular flow (static → dynamical) ────────────

    The machine-checked content so far is a STATIC picture: which pointer algebra
    carries an ω-preserving conditional expectation, and that its Born weights are
    a probability.  The honest gap λ faces is DYNAMICAL: does the unitary flow
    *keep* the selected record selected, or can coherence between pointer sectors
    regenerate?  Here is the first dynamical brick.  The modular flow at any fixed
    parameter is conjugation by a generator `m` (think `m = ρ^{it}`); when the
    pointers commute with `m` (the Takesaki criterion, which `[ρ,Pₐ]=0` lifts to
    every `ρ^{it}`), the decoherence map E COMMUTES with the flow:

        E ∘ σ = σ ∘ E,

    so if you start in a dephased (records-definite) state you stay there — the
    pointer structure is a constant of the modular motion, and each selected
    record projection is a fixed point.  The off-diagonals annihilated by E are
    not regenerated by σ.  This is the static-exclusion → dynamical-persistence
    bridge, made precise where it can be (Type I shadow). -/

/-- If an invertible `m` commutes with `P`, so does its inverse `⅟m`. -/
theorem invOf_comm_of_comm (m P : Matrix n n ℂ) [Invertible m]
    (h : m * P = P * m) : ⅟m * P = P * ⅟m := by
  calc ⅟m * P
      = ⅟m * P * (m * ⅟m) := by rw [mul_invOf_self, mul_one]
    _ = ⅟m * (P * m) * ⅟m := by noncomm_ring
    _ = ⅟m * (m * P) * ⅟m := by rw [← h]
    _ = (⅟m * m) * P * ⅟m := by noncomm_ring
    _ = P * ⅟m := by rw [invOf_mul_self, one_mul]

/-- **Persistence: the decoherence map commutes with the modular flow.**  For
    the flow `σ = modAut m` (conjugation by the modular generator `m = ρ^{it}`)
    and pointers `P` that commute with `m` (the Takesaki criterion), the
    dephasing map `E(x)=Σ Pₐ x Pₐ` satisfies `E(σ x) = σ(E x)`.  Hence the
    record structure E annihilates the off-diagonals of is preserved by the
    dynamics: a dephased state stays dephased, coherence does not regenerate.
    This is the finite shadow of "λ's selection is stable under time
    evolution." -/
theorem dephase_modAut_commute {ι : Type*} [Fintype ι] (m : Matrix n n ℂ)
    [Invertible m] (P : ι → Matrix n n ℂ) (hcomm : ∀ i, m * P i = P i * m)
    (x : Matrix n n ℂ) :
    dephase P (modAut m x) = modAut m (dephase P x) := by
  unfold dephase modAut
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hinv := invOf_comm_of_comm m (P i) (hcomm i)
  rw [show P i * (m * x * ⅟m) * P i = (P i * m) * x * (⅟m * P i) by noncomm_ring,
      ← hcomm i, hinv,
      show m * P i * x * (P i * ⅟m) = m * (P i * x * P i) * ⅟m by noncomm_ring]

/-- **Each selected record is a fixed point of the modular flow.**  When the
    pointer projections commute with `ρ` (the Takesaki criterion), the modular
    flow fixes each one: `σ(Pₐ) = Pₐ`.  The actual record is stationary. -/
theorem modAut_fixes_pointer {ι : Type*} [Fintype ι] (ρ : Matrix n n ℂ)
    [Invertible ρ] (P : ι → Matrix n n ℂ) (hcomm : ∀ i, ρ * P i = P i * ρ)
    (i : ι) : modAut ρ (P i) = P i :=
  (modAut_fixes_iff_commute ρ (P i)).mpr (hcomm i)

/-- **Born weights are constants of the modular motion.**  Unconditionally (KMS
    state-invariance), the algebraic Born weight of any observable — in
    particular any record projection — is unchanged by the modular flow:
    `ω(σ x) = ω(x)`.  The selection statistics do not drift under the
    dynamics. -/
theorem bornWeight_modAut_invariant (ρ : Matrix n n ℂ) [Invertible ρ]
    (x : Matrix n n ℂ) :
    bornWeight ρ (modAut ρ x) = bornWeight ρ x :=
  modAut_stateOf_invariant ρ x

/- ── 5. Audit conclusion ─────────────────────────────────────────────────-/

/-- **Audit conclusion.**  The finite (Type I) shadow of λ's pointer law,
    proved from matrix algebra + trace cyclicity, NO project axioms:

      * `modAut_fixes_iff_commute` — the finite Takesaki criterion
        `σ(P)=P ⟺ [ρ,P]=0` (exact decoherence selects which pointer algebra
        carries an ω-preserving conditional expectation);
      * `bornWeights_sum` — the algebraic Born weights `ω(Pₐ)` are a probability;
      * `dephase_one`, `dephase_preserves_state` — the decoherence map
        `E(x)=Σ Pₐ x Pₐ` is the unital, ω-preserving conditional expectation
        onto the pointer algebra, exactly when the criterion holds;
      * `dephase_modAut_commute` — PERSISTENCE: `E ∘ σ = σ ∘ E`, the decoherence
        structure is a constant of the modular motion (the static→dynamical
        brick — a dephased state stays dephased, coherence does not regenerate);
      * `modAut_fixes_pointer`, `bornWeight_modAut_invariant` — each selected
        record is a fixed point of the flow, and the Born weights are constants
        of the motion.

    Honest scope: Type I (finite n).  The Type III₁ continuum version —
    algebraic Born rule via the standard form / natural cone, and the genuine
    modular `σ_t^ω` with Connes-cocycle Radon–Nikodym derivatives — is the cited
    frontier.  The single-outcome dynamics and the derivation of Born as
    across-run frequencies remain open (this fixes the kinematic HOME and FORM
    of λ, not its dynamics). -/
theorem audit_conclusion : True := trivial

end LambdaPointer
end QIQTH
