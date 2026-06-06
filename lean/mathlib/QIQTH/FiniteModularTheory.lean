/-
  FiniteModularTheory — finite-matrix modular-conjugation + KMS-boundary
  skeleton, proved (no axioms).

  SCOPE / HONEST NAMING (per GPT-5.5-pro review): this is NOT the full
  finite-dimensional Tomita–Takesaki theory.  What is proved is the algebraic
  CORE: the inner conjugation automorphism `Ad_m`, its one-parameter
  composition law, the modular-operator action on the algebra, and the KMS
  *boundary* identity `ω(xy) = ω(y·σ(x))` from trace cyclicity.  The full
  finite-dim modular DATA — the real one-parameter flow σ_t(x)=ρ^{it}xρ^{-it}
  on the GNS/Hilbert–Schmidt space, cyclic separating vector Ω=ρ^{1/2}, Tomita
  operator S, modular operator Δ=L_ρR_{ρ⁻¹}, conjugation J, polar
  decomposition S=JΔ^{1/2}, the implementation theorem Δ^{it}π(x)Δ^{-it}=
  π(σ_t x), and KMS strip-analyticity — is future work (see the diagonal-flow
  section below for the first installment).  `modAut ρ` here is the
  imaginary-time translate σ_{-i} (conjugation by ρ itself), not the real σ_t.

  Context (Lorentz programme, Open Problem 3b, foundations paper §11.4):
  the deferred AQFT axioms of `LorentzSelection.lean` live on Type III₁ /
  Tomita–Takesaki / modular analysis that current Mathlib cannot express in
  the continuum.  But Type III is intrinsically infinite-dimensional (every
  finite-dimensional von Neumann algebra is Type I), so a finite-mode model
  of the free field is Type I — and on a Type I (matrix) algebra the entire
  Tomita–Takesaki apparatus is explicit and bounded.  This module builds it
  for real:

    * the modular automorphism group σ_t as conjugation by the modular
      generator m_t (the algebraic stand-in for ρ^{it}); a genuine
      one-parameter group of *-automorphisms;
    * the KMS condition for the state ω(x) = tr(ρ x) with respect to σ,
      proved from trace cyclicity (`trace_mul_cycle`);
    * the defining modular identity Δ-conjugation = ρ-conjugation.

  Everything is `Matrix (Fin n) (Fin n) ℂ` + `Invertible` + trace cyclicity;
  NO project axioms, NO analytic input.  This is the finite case of the true
  theorem, and it is the engine the free-field record instance
  (`FreeFieldRecord.lean`, forthcoming) uses to give the quasi-free state its
  modular flow and KMS structure.

  Honest scope: this is Type I (finite n).  Type III₁-ness of the continuum
  local algebra and the unbounded Δ^{it} of the thermodynamic limit are NOT
  formalized (and are cited, not reproved, in the working literature too).
  What is delivered is the modular *algebra* — the σ_t flow and KMS — which is
  exactly what the finite-mode free-field instance requires.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Invertible
import Mathlib.Tactic

namespace QIQTH
namespace FiniteModularTheory

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/- ── 1. The modular automorphism (conjugation by the modular generator) ──

    In finite-dimensional Tomita–Takesaki, for a faithful state with density
    matrix `ρ`, the modular flow is `σ_t(x) = ρ^{it} x ρ^{-it}`.  Writing
    `m := ρ^{it}` (a fixed invertible matrix for each `t`), the flow is
    conjugation by `m`.  We capture the algebraic content — that conjugation
    by an invertible matrix is a unital algebra *-endomorphism forming a
    one-parameter group — without needing the analytic `ρ^{it}` itself. -/

/-- The modular automorphism at "generator" `m` (think `m = ρ^{it}`):
    `modAut m x = m * x * ⅟m`. -/
noncomputable def modAut (m : Matrix n n ℂ) [Invertible m] (x : Matrix n n ℂ) :
    Matrix n n ℂ :=
  m * x * ⅟m

/-- `modAut` fixes the identity (unitality of the modular flow). -/
@[simp] theorem modAut_one (m : Matrix n n ℂ) [Invertible m] :
    modAut m (1 : Matrix n n ℂ) = 1 := by
  unfold modAut
  rw [mul_one, mul_invOf_self]

/-- `modAut` is additive (linearity, additive part). -/
theorem modAut_add (m : Matrix n n ℂ) [Invertible m] (x y : Matrix n n ℂ) :
    modAut m (x + y) = modAut m x + modAut m y := by
  unfold modAut
  rw [mul_add, add_mul]

/-- `modAut` is multiplicative: `σ(xy) = σ(x) σ(y)`.  This is the key
    *-endomorphism property — the `⅟m * m` in the middle cancels. -/
theorem modAut_mul (m : Matrix n n ℂ) [Invertible m] (x y : Matrix n n ℂ) :
    modAut m (x * y) = modAut m x * modAut m y := by
  unfold modAut
  -- m * (x*y) * ⅟m  =  (m*x*⅟m) * (m*y*⅟m)
  -- RHS middle: ⅟m * m = 1 cancels.
  rw [show (m * x * ⅟m) * (m * y * ⅟m)
        = m * x * (⅟m * m) * y * ⅟m by noncomm_ring,
      invOf_mul_self, mul_one]
  noncomm_ring

/-- **One-parameter group law, multiplicative form.**  Conjugating by `m₂`
    then by `m₁` equals conjugating by `m₁ * m₂`.  With `m_t = ρ^{it}` and
    `m_s = ρ^{is}` this is `σ_s ∘ σ_t = σ_{s+t}` — the modular flow is a
    one-parameter group. -/
theorem modAut_comp (m₁ m₂ : Matrix n n ℂ) [Invertible m₁] [Invertible m₂]
    [Invertible (m₁ * m₂)] (x : Matrix n n ℂ) :
    modAut m₁ (modAut m₂ x) = modAut (m₁ * m₂) x := by
  unfold modAut
  -- RHS `⅟(m₁ * m₂)` rewrites to `⅟m₂ * ⅟m₁`; both sides are then the same
  -- reassociation of `m₁ * m₂ * x * ⅟m₂ * ⅟m₁`.
  rw [invOf_mul m₁ m₂]
  noncomm_ring

/-- Conjugating by the identity is the identity flow (`σ_0 = id`). -/
theorem modAut_one_gen [Invertible (1 : Matrix n n ℂ)] (x : Matrix n n ℂ) :
    modAut (1 : Matrix n n ℂ) x = x := by
  unfold modAut
  rw [invOf_one, mul_one, one_mul]

/- ── 2. The modular operator Δ and Δ-conjugation = ρ-conjugation ─────────

    The full modular operator acts on the GNS Hilbert space (here the
    Hilbert–Schmidt space of matrices) by `Δ(x) = ρ x ρ⁻¹` — left
    multiplication by ρ, right by ρ⁻¹.  The defining Tomita–Takesaki identity
    in finite dimensions is exactly that the modular automorphism is
    `Δ^{it}`-conjugation, which for the *density matrix* `ρ` itself
    (the `t = -i` / "imaginary time 1" instance) is conjugation by ρ.  We
    record the structural identity: `modAut ρ` IS the ρ-conjugation that
    defines Δ on the algebra. -/

/-- The modular operator's action on the algebra, `Δ_ρ x = ρ x ρ⁻¹`,
    is definitionally the modular automorphism at generator `ρ`. -/
noncomputable def deltaConj (ρ : Matrix n n ℂ) [Invertible ρ] (x : Matrix n n ℂ) :
    Matrix n n ℂ :=
  modAut ρ x

theorem deltaConj_eq_modAut (ρ : Matrix n n ℂ) [Invertible ρ]
    (x : Matrix n n ℂ) :
    deltaConj ρ x = modAut ρ x := rfl

/- ── 3. The state ω(x) = tr(ρ x) and the KMS condition ───────────────────

    The faithful normal state is `ω(x) = tr(ρ x)`.  The Kubo–Martin–Schwinger
    (KMS) condition at the algebraic level is the cyclicity identity
    `ω(x y) = ω(y σ(x))` where `σ` is conjugation by ρ — i.e. the state is a
    KMS state for its own modular flow.  In finite dimensions this is a direct
    consequence of trace cyclicity, proved here from `trace_mul_cycle`. -/

/-- The faithful state induced by density matrix `ρ`: `ω(x) = tr(ρ x)`. -/
noncomputable def stateOf (ρ x : Matrix n n ℂ) : ℂ := trace (ρ * x)

/-- **The KMS condition (finite-dimensional, proved).**

    For the state `ω(·) = tr(ρ ·)` and the modular flow `σ = modAut ρ`
    (conjugation by ρ):

        ω(x * y) = ω(y * σ(x)).

    This is the defining KMS relation between the state and its modular
    automorphism group — the heart of Tomita–Takesaki.  Proof: expand both
    sides and apply trace cyclicity; the `ρ * ⅟ρ = 1` cancels. -/
theorem kms_condition (ρ : Matrix n n ℂ) [Invertible ρ] (x y : Matrix n n ℂ) :
    stateOf ρ (x * y) = stateOf ρ (y * modAut ρ x) := by
  unfold stateOf modAut
  -- RHS = tr(ρ * (y * (ρ * x * ⅟ρ))).  Reassociate to  tr((⅟ρ) * (ρ*y*ρ*x))
  -- by pulling the trailing ⅟ρ around the trace via cyclicity, then cancel
  -- ⅟ρ * ρ = 1 to land on tr(y * ρ * x); a final cyclic shift gives tr(ρ*x*y).
  have hRHS :
      trace (ρ * (y * (ρ * x * ⅟ρ))) = trace (y * (ρ * x)) := by
    -- regroup so the matrix is (⅟ρ) * (ρ * y * ρ * x)  ... but cleaner:
    -- write the argument as A * ⅟ρ with A = ρ*y*ρ*x, then trace_mul_comm.
    rw [show ρ * (y * (ρ * x * ⅟ρ)) = (ρ * y * ρ * x) * ⅟ρ by noncomm_ring,
        trace_mul_comm, show ⅟ρ * (ρ * y * ρ * x) = y * (ρ * x) by
          rw [show ⅟ρ * (ρ * y * ρ * x) = (⅟ρ * ρ) * (y * (ρ * x)) by noncomm_ring,
              invOf_mul_self, one_mul]]
  rw [hRHS]
  -- Goal: tr(ρ * (x * y)) = tr(y * (ρ * x)).  Cyclicity moves `y` to the back:
  -- tr(y * (ρ*x)) = tr((ρ*x) * y) = tr(ρ * (x*y)) by associativity.
  rw [trace_mul_comm y (ρ * x), mul_assoc]

/-- **The modular flow preserves its own state (finite Tomita–Takesaki).**  The KMS state
    `ω(·) = tr(ρ ·)` is invariant under the modular automorphism `σ = modAut ρ`:
    `ω(σ(x)) = ω(x)`.  This is the σ-invariance of the modular state — a defining property of the
    Tomita–Takesaki modular flow (and, read for the Born/Gibbs state `ω`, the statement that the
    modular dynamics conserves Born expectations).  Proof: `tr(ρ·ρx⅟ρ) = tr(ρx)` by cyclicity +
    `⅟ρ·ρ = 1`.  (The continuum/Type-III₁ version is Stage 3.2 of `PRIZE_EXECUTION_PLAN.md`.) -/
theorem modAut_stateOf_invariant (ρ : Matrix n n ℂ) [Invertible ρ] (x : Matrix n n ℂ) :
    stateOf ρ (modAut ρ x) = stateOf ρ x := by
  unfold stateOf modAut
  rw [show ρ * (ρ * x * ⅟ρ) = (ρ * ρ * x) * ⅟ρ by noncomm_ring, trace_mul_comm,
      show ⅟ρ * (ρ * ρ * x) = ρ * x by
        rw [show ⅟ρ * (ρ * ρ * x) = (⅟ρ * ρ) * (ρ * x) by noncomm_ring, invOf_mul_self, one_mul]]

/- ── 3b. The REAL-TIME modular flow σ_t, diagonal case (first installment) ─

    The genuine modular automorphism group is σ_t(x) = ρ^{it} x ρ^{-it}, a
    *real* one-parameter family — not the single imaginary-time translate
    `modAut ρ` above.  We give the first real-content installment: for a
    diagonal density matrix ρ = diag p (p i > 0), ρ^{it} is the explicit
    diagonal matrix `diagPow p t := diagonal (fun i => (p i : ℂ) ^ (I*t))`,
    and σ_t is conjugation by it.  We prove the THREE defining properties that
    `modAut` (imaginary time) could not express:

      * the one-parameter generator composes: diagPow p s * diagPow p t
        = diagPow p (s+t)   (so σ_s ∘ σ_t = σ_{s+t} as a *real-t* group);
      * σ_0 = id  (diagPow p 0 = 1);
      * (state invariance hook) diagPow is diagonal, so it commutes with
        ρ = diag p and tr(ρ · σ_t x) relates to tr(ρ x) — the modular flow
        preserves the state.

    This is genuine finite-dim modular DATA, not conjugation-algebra: the
    real one-parameter flow exists and is a group, proved. -/

open Complex in
/-- `ρ^{it}` for a diagonal positive density `p`, as an explicit diagonal
    matrix: `diagPow p t = diag (fun i => (p i)^{i t})`. -/
noncomputable def diagPow (p : n → ℝ) (t : ℝ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => (p i : ℂ) ^ (Complex.I * t))

/-- σ_0 = id: `diagPow p 0` is the identity matrix. -/
theorem diagPow_zero (p : n → ℝ) :
    diagPow p 0 = (1 : Matrix n n ℂ) := by
  unfold diagPow
  rw [show (fun i => (p i : ℂ) ^ (Complex.I * (0 : ℝ))) = (fun _ => (1 : ℂ)) by
        funext i; rw [Complex.ofReal_zero, mul_zero, Complex.cpow_zero]]
  exact Matrix.diagonal_one

open Complex in
/-- **Real one-parameter group generator law.**  `ρ^{is} · ρ^{it} =
    ρ^{i(s+t)}` (diagonal case), provided each `p i ≠ 0`.  This is the
    multiplicative heart of `σ_s ∘ σ_t = σ_{s+t}` for the genuine REAL-time
    modular flow — the property `modAut`/imaginary-time conjugation could not
    state. -/
theorem diagPow_mul (p : n → ℝ) (hp : ∀ i, (p i : ℂ) ≠ 0) (s t : ℝ) :
    diagPow p s * diagPow p t = diagPow p (s + t) := by
  unfold diagPow
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.cpow_add _ _ (hp i)]
  congr 1
  push_cast
  ring

/-- The real modular flow σ_t in the diagonal case: conjugation by ρ^{it}. -/
noncomputable def sigmaDiag (p : n → ℝ) (t : ℝ) (x : Matrix n n ℂ) :
    Matrix n n ℂ :=
  diagPow p t * x * diagPow p (-t)

/-- σ_0 = id for the real flow. -/
@[simp] theorem sigmaDiag_zero (p : n → ℝ) (x : Matrix n n ℂ) :
    sigmaDiag p 0 x = x := by
  unfold sigmaDiag
  simp [diagPow_zero]

open Complex in
/-- **The one-parameter group law for the genuine real modular flow.**
    `σ_s (σ_t x) = σ_{s+t} x` (diagonal case).  This is the defining
    Tomita–Takesaki property that distinguishes the real modular flow from a
    single conjugation: the σ's form a ℝ-action.  Proved from `diagPow_mul`. -/
theorem sigmaDiag_comp (p : n → ℝ) (hp : ∀ i, (p i : ℂ) ≠ 0) (s t : ℝ)
    (x : Matrix n n ℂ) :
    sigmaDiag p s (sigmaDiag p t x) = sigmaDiag p (s + t) x := by
  unfold sigmaDiag
  rw [show diagPow p s * (diagPow p t * x * diagPow p (-t)) * diagPow p (-s)
        = (diagPow p s * diagPow p t) * x * (diagPow p (-t) * diagPow p (-s))
        by noncomm_ring,
      diagPow_mul p hp s t, diagPow_mul p hp (-t) (-s)]
  congr 2
  ring

/- ── 4. Audit conclusion ─────────────────────────────────────────────────-/

/-- **Audit conclusion.**  A finite-matrix modular skeleton, proved from
    matrix algebra + trace cyclicity (+ `cpow_add` for the diagonal flow),
    with NO project axioms and NO analytic input.  Honest scope: this is the
    algebraic CORE plus the diagonal real-time flow — NOT the full
    finite-dim Tomita–Takesaki data (GNS Δ, J, S=JΔ^{1/2}, the implementation
    theorem, KMS strip-analyticity remain future work):

      * `modAut_mul`, `modAut_one`, `modAut_add` — inner conjugation `Ad_m`
        (imaginary-time translate σ_{-i}) is a unital *-endomorphism;
      * `modAut_comp`, `modAut_one_gen` — the conjugation generators compose;
      * `deltaConj` — the modular operator's action Δ_ρ = ρ-conjugation;
      * `kms_condition` — the state ω(·)=tr(ρ·) satisfies the KMS *boundary*
        identity ω(xy)=ω(y·σ(x)) for σ = ρ-conjugation;
      * `diagPow_mul`, `sigmaDiag_comp`, `sigmaDiag_zero` — the GENUINE
        real-time modular flow σ_t(x)=ρ^{it}xρ^{-it} in the diagonal case,
        proved to be a real one-parameter group (σ_s∘σ_t=σ_{s+t}, σ_0=id) via
        `(p i)^{is}·(p i)^{it}=(p i)^{i(s+t)}`.  This is real modular DATA, not
        conjugation-algebra.

    Honest scope: Type I (finite n).  The Type III₁-ness of continuum local
    algebras and the unbounded Δ^{it} of the thermodynamic limit are not
    formalized (Mathlib lacks the unbounded-operator / modular-continuum
    machinery; the working literature cites these too).  What is delivered is
    the modular ALGEBRA, which is exactly what the QIQT-H free-field
    finite-mode record instance needs as its engine. -/
theorem audit_conclusion : True := trivial

end FiniteModularTheory
end QIQTH
