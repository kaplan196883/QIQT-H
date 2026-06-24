/-
  GleasonSelector — the Gleason-route construction of the QIQT-H typicality
  measure μ over actuality selectors (Open Problem 1, foundations paper §11.4).

  GPT-5.5-pro "options for μ" consultation: of the six candidate routes for
  deriving μ (Gleason / envariance / decoherent-histories-postulate / Bohmian
  equilibrium / frequency-operator / decision-theory), the **Gleason / POVM /
  Mackey-Gleason route is the unique one** that can give an OBJECTIVE,
  Lorentz-equivariant μ meeting requirements (1)-(5), with operational
  no-signaling following structurally from ONE canonical μ rather than per-
  experiment tuning.  Recommended architecture: Gleason as the spine; the
  decoherence functional as the cylinder construction; a frequency theorem as
  the LLN corollary.

  This module formalizes the architecture in the finite-dimensional record
  model, in the project's standing discipline.  IMPORTANT — soundness fix
  (second GPT-5.5-pro review): an earlier version named an axiom asserting
  "normalized + additive + homogeneous + ray-certain ⇒ Born".  **That axiom
  was FALSE** (positivity-free; the `Fin 2` weight `E ↦ E₀₀+E₀₁` satisfies all
  its premises but isn't Born).  It has been RETIRED.  The module now contains
  NO project axiom; what it delivers:

    * `naive_gleason_premises_insufficient` — the explicit `Fin 2`
      counterexample, PROVED: the positivity-free premises do NOT force Born.
      (Soundness red-team that documents why positivity is indispensable.)
    * `proj_sandwich` — PROVED: `P_ψ · E · P_ψ = ⟨ψ|E|ψ⟩ • P_ψ` on the ray
      projector; the algebraic heart of "ray-certainty ⇒ Born".
    * `born_is_forced` — PROVED (no axiom): a linear, **ray-supported**
      (`w E = w (P_ψ E P_ψ)` — the genuine positivity/certainty content the
      counterexample violates), ray-certain weight IS the Born functional.
    * `history_measure_is_born` / `history_measure_total` — μ on a complete
      decoherent record family is the Born / decoherence-functional measure,
      normalized.
    * `no_signaling_marginal` — one bilinear correlation gives
      spacelike-marginal independence for ALL of Bob's settings (requirement
      2, honest form), depending on no project axiom.

  The key conceptual point GPT-5.5-pro flagged (and the proofs honour): the
  Born content is NOT in any single Boolean/record algebra — a single context
  admits any probability vector.  What forces Born is *positivity +
  non-contextuality across overlapping effect contexts* + state-certainty.  In
  this module the positivity/certainty content is the explicit `hsupp`
  hypothesis of `born_is_forced` (ray-support), making the dependency overt
  rather than hidden in a false axiom.

  Honest scope: finite-dimensional.  The full continuum Type II / Haagerup-L^p
  / history-net version (requirement 5 in full) and the Busch *extension*
  (effect-additivity ⇒ positive linear functional, which would discharge
  `hsupp` from first principles) stay future work / the named axiom
  `LorentzSelection.decoherence_functional_measure`.  And — per GPT — μ cannot
  be derived from unitarity + bare λ alone; ONE bridge principle (here:
  positivity + non-contextuality + state-certainty) is irreducible, exactly as
  quantum equilibrium is assumed in Bohmian mechanics.  What is established is
  the *uniqueness/canonicity* of μ given those structural hypotheses, not
  "probability from nothing".
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace QIQTH
namespace GleasonSelector

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/- ── 1. Effects and the Born functional ─────────────────────────────────

    An effect is a Hermitian matrix `E` with `0 ≤ E ≤ I` (a yes-component of
    a measurement / POVM).  The Born functional of a unit state vector `ψ` is
    `born ψ E = ⟨ψ | E | ψ⟩ = star ψ ⬝ᵥ (E *ᵥ ψ)`.  We work with the explicit
    quadratic form to stay inside finite linear algebra. -/

/-- The Born functional of state vector `ψ` on operator `E`:
    `⟨ψ| E |ψ⟩ = star ψ ⬝ᵥ (E *ᵥ ψ)`. -/
noncomputable def born (ψ : n → ℂ) (E : Matrix n n ℂ) : ℂ := star ψ ⬝ᵥ (E *ᵥ ψ)

/-- The Born functional is additive in the effect. -/
theorem born_add (ψ : n → ℂ) (E F : Matrix n n ℂ) :
    born ψ (E + F) = born ψ E + born ψ F := by
  unfold born
  rw [add_mulVec, dotProduct_add]

/-- The Born functional is ℝ-homogeneous (scalar pulls out). -/
theorem born_smul (ψ : n → ℂ) (c : ℂ) (E : Matrix n n ℂ) :
    born ψ (c • E) = c * born ψ E := by
  unfold born
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- On the identity, the Born functional of a *unit* vector is `1`
    (`⟨ψ|ψ⟩ = 1`).  (Normalization hypothesis supplied by the caller.) -/
theorem born_one (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    born ψ (1 : Matrix n n ℂ) = 1 := by
  unfold born
  rw [one_mulVec]; exact hψ

/- ── 2. RED TEAM: the naive premises do NOT force Born ────────────────────

    GPT-5.5-pro review (correct, and important): an earlier version of this
    module named an axiom asserting that a normalized, additive, homogeneous,
    ray-certain weight `w : Matrix n n ℂ → ℂ` must equal `born ψ`.  **That is
    FALSE** — without a *positivity* constraint (and with `w` ranging over all
    matrices rather than effects), ray-certainty does not pin the state.  We
    record the explicit counterexample as a theorem, so the module documents
    exactly why positivity is essential and cannot be dropped. -/

/-- **Counterexample weight on `Fin 2`.**  `wBad E = E 0 0 + E 0 1`.  It is
    linear and agrees with `born (1,0)` on `1` and on the ray projector — yet
    differs from `born` on the off-diagonal matrix unit.  Witnesses that the
    naive (positivity-free) Gleason premises are insufficient. -/
def wBad (E : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := E 0 0 + E 0 1

/-- The counterexample state `ψ = (1,0)` on `Fin 2`. -/
def ψ0 : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

theorem ψ0_unit : star ψ0 ⬝ᵥ ψ0 = 1 := by
  simp only [ψ0, dotProduct, Fin.sum_univ_two, Pi.star_apply]
  norm_num [Complex.ext_iff]

theorem wBad_add (E F : Matrix (Fin 2) (Fin 2) ℂ) :
    wBad (E + F) = wBad E + wBad F := by simp [wBad]; ring

theorem wBad_smul (c : ℂ) (E : Matrix (Fin 2) (Fin 2) ℂ) :
    wBad (c • E) = c * wBad E := by simp [wBad]; ring

theorem wBad_one : wBad 1 = 1 := by
  simp only [wBad, Matrix.one_apply]; norm_num

theorem wBad_ray : wBad (vecMulVec ψ0 (star ψ0)) = 1 := by
  simp only [wBad, vecMulVec_apply, ψ0, Pi.star_apply]
  norm_num [Complex.ext_iff]

/-- **The red-team theorem.**  `wBad` satisfies every naive Gleason premise
    (normalized, additive, homogeneous, ray-certain) yet is NOT the Born
    functional — it disagrees on the off-diagonal unit `E₀₁`.  Hence the
    naive premises do not force Born; *positivity is indispensable*.  (This is
    the soundness check that retired the earlier false axiom.) -/
theorem naive_gleason_premises_insufficient :
    ∃ (w : Matrix (Fin 2) (Fin 2) ℂ → ℂ),
      w 1 = 1 ∧ (∀ E F, w (E + F) = w E + w F) ∧
      (∀ (c : ℂ) E, w (c • E) = c * w E) ∧
      w (vecMulVec ψ0 (star ψ0)) = 1 ∧
      ∃ E, w E ≠ born ψ0 E := by
  refine ⟨wBad, wBad_one, wBad_add, wBad_smul, wBad_ray, ?_⟩
  -- The off-diagonal unit E₀₁: wBad gives 1, born gives 0.
  refine ⟨Matrix.single 0 1 1, ?_⟩
  have hw : wBad (Matrix.single 0 1 1) = 1 := by
    simp only [wBad, Matrix.single_apply]; norm_num
  have hb : born ψ0 (Matrix.single (0 : Fin 2) 1 1) = 0 := by
    simp only [born, ψ0, Matrix.single, dotProduct, mulVec, Fin.sum_univ_two,
               Pi.star_apply, Matrix.of_apply]
    norm_num
  rw [hw, hb]; norm_num

/- ── 3. The CORRECT core, PROVED: positive-linear + ray-certain ⇒ Born ───

    The honest, provable theorem (GPT-5.5-pro's recommended discharge):
    a *positive*, linear, ray-certain functional equals Born — no spectral
    theory, no trace duality.  Positivity is encoded as
    `hpos : ∀ A, w (Aᴴ * A) = born ψ (Aᴴ * A)` on the cone of squares; this is
    the genuine Gleason content that the false axiom omitted.  The PROVED step
    is the projector-sandwich collapse below; what remains a (much smaller,
    true) named axiom is only that an effect-additive valuation *extends* to
    such a positive linear functional (the Busch extension). -/

/-- **Rank-one sandwich identity (PROVED, no axioms, NO normalization).**
    For the rank-one operator `R = |ψ⟩⟨ψ| = vecMulVec ψ (star ψ)` of ANY vector
    `ψ`, `R E R = ⟨ψ|E|ψ⟩ • R`.  Normalization is NOT needed for this algebraic
    identity (it is only needed to make `R` idempotent); per the GPT-5.5-pro
    review we state the hψ-free version as the real lemma and give the
    projector specialization as a wrapper. -/
theorem rankOne_sandwich (ψ : n → ℂ) (E : Matrix n n ℂ) :
    (vecMulVec ψ (star ψ)) * E * (vecMulVec ψ (star ψ))
      = born ψ E • vecMulVec ψ (star ψ) := by
  ext i j
  -- RHS (i,j) = (Σ_{a,b} star ψ a · E a b · ψ b) · (ψ i · star ψ j).
  rw [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  -- LHS (i,j): expand the two matrix products.
  rw [Matrix.mul_apply]
  -- inner: ((vecMulVec ψ (star ψ)) * E) i k = ψ i · Σ_a star ψ a · E a k
  have hinner : ∀ k, ((vecMulVec ψ (star ψ)) * E) i k
      = ψ i * ∑ a, star ψ a * E a k := by
    intro k
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [vecMulVec_apply]; ring
  simp only [hinner, vecMulVec_apply]
  -- LHS = Σ_k (ψ i · Σ_a star ψ a · E a k) · (ψ k · star ψ j)
  --     = ψ i · star ψ j · Σ_k Σ_a star ψ a · E a k · ψ k.
  -- RHS = born · ψ i · star ψ j, with born = Σ_a star ψ a · Σ_b E a b · ψ b.
  rw [born]
  simp only [dotProduct, mulVec, Pi.star_apply]
  -- Pull the common ψ i · star ψ j factor out of the LHS sum.
  rw [show (∑ k, (ψ i * ∑ a, star (ψ a) * E a k) * (ψ k * star (ψ j)))
        = (ψ i * star (ψ j)) * ∑ k, (∑ a, star (ψ a) * E a k) * ψ k by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
  -- RHS: (Σ_a star ψ a · (Σ_b E a b · ψ b)) · (ψ i · star ψ j).
  rw [show (∑ a, star (ψ a) * ∑ b, E a b * ψ b) * (ψ i * star (ψ j))
        = (ψ i * star (ψ j)) * ∑ a, (∑ b, E a b * ψ b) * star (ψ a) by
        rw [Finset.sum_mul]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro a _; ring]
  congr 1
  -- Σ_k (Σ_a star ψ a E a k) ψ k  =  Σ_a (Σ_b E a b ψ b) star ψ a.
  -- Flatten both to Σ_a Σ_k (star ψ a · E a k · ψ k) and use sum_comm on LHS.
  rw [show (∑ k, (∑ a, star (ψ a) * E a k) * ψ k)
        = ∑ k, ∑ a, star (ψ a) * E a k * ψ k by
        apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]]
  rw [show (∑ a, (∑ b, E a b * ψ b) * star (ψ a))
        = ∑ a, ∑ b, star (ψ a) * E a b * ψ b by
        apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro b _; ring]
  rw [Finset.sum_comm]

/-- **Projector-sandwich (wrapper).**  For a *unit* vector `ψ`, the ray
    projector `P = |ψ⟩⟨ψ|` satisfies `P E P = ⟨ψ|E|ψ⟩ • P`.  Specialization of
    `rankOne_sandwich`; `hψ` is the normalization that makes `P` idempotent,
    kept for callers that need the projector reading (the identity itself does
    not use it). -/
theorem proj_sandwich (ψ : n → ℂ) (_hψ : star ψ ⬝ᵥ ψ = 1)
    (E : Matrix n n ℂ) :
    (vecMulVec ψ (star ψ)) * E * (vecMulVec ψ (star ψ))
      = born ψ E • vecMulVec ψ (star ψ) :=
  rankOne_sandwich ψ E

/- Note on the Busch / positive-extension content.  The genuine input the
   earlier (FALSE) axiom skipped is: an effect-valuation that is normalized,
   additive on coexistent effects, and *positive* extends to a complex linear
   functional that is *ray-supported* (`hsupp` below: `w E = w (P E P)`, i.e.
   only the state's ray carries weight — the certainty content the `Fin 2`
   counterexample violates).  We isolate this as the explicit hypothesis
   `hsupp` of `born_is_forced` rather than a free-standing axiom, so it is a
   discharatable premise (a future Busch-extension development would supply
   it), and `born_is_forced` itself is then a THEOREM with no project axiom. -/

/- ── 3b. DISCHARGING ray-support FROM POSITIVITY (the real Gleason bridge) ─

    GPT-5.5-pro second review: `hsupp` (ray-support) is, in the rank-one case,
    extensionally as strong as the conclusion; the genuine Gleason/Busch step
    is to *derive* ray-support from POSITIVITY.  This section does exactly that,
    via the Cauchy–Schwarz/null-space argument, turning the support premise into
    a theorem.  `w` positive means the sesquilinear form ⟨A,B⟩ := w(Aᴴ B) is
    positive-semidefinite; a null vector of a PSD form lies in its radical
    (⟨A,A⟩=0 ⇒ ⟨A,X⟩=0), so with Q = I − P and w(Q)=0 the off-ray terms vanish
    and w(E)=w(PEP). -/

/-- A complex number is **nonneg** iff it is a nonnegative real.  (ℂ has no
    native order; this is the predicate used for positivity of `w` on squares.) -/
def NonnegC (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

/-- A nonneg-real complex number is fixed by conjugation. -/
theorem NonnegC.star_eq {z : ℂ} (hz : NonnegC z) : star z = z := by
  obtain ⟨r, _, rfl⟩ := hz
  exact Complex.conj_ofReal r

/-- A nonneg-real complex number has zero imaginary part. -/
theorem NonnegC.im_zero {z : ℂ} (hz : NonnegC z) : z.im = 0 := by
  obtain ⟨r, _, rfl⟩ := hz; simp

/-- **Real-quadratic null lemma.**  If `0 ≤ d t² + 2 a t` for all real `t`
    (with `0 ≤ d`), then `a = 0`.  Proof: evaluate at `t = -a/(d+1)`. -/
theorem quadratic_nonneg_forall_linear_zero {d a : ℝ} (hd : 0 ≤ d)
    (h : ∀ t : ℝ, 0 ≤ d * t ^ 2 + 2 * a * t) : a = 0 := by
  -- Evaluate at t = s and t = -s for small s>0: 0 ≤ d s² ± 2 a s.
  -- Subtracting bounds 4|a|s ≤ ... forces a = 0 as s→0; cleanest: nlinarith
  -- with a chosen evaluation point.  Use t = -a (gives 0 ≤ d a² − 2 a²),
  -- and t = a is not needed; instead use the two-point trick directly.
  by_contra ha
  -- WLOG handle the sign of a via |a|; use t = -a / (d+1) > 0-direction.
  have hd1 : (0:ℝ) < d + 1 := by linarith
  have ht := h (-a / (d + 1))
  have e : d * (-a / (d + 1)) ^ 2 + 2 * a * (-a / (d + 1))
      = (a^2 * (d - 2*(d+1))) / (d+1)^2 := by
    field_simp; ring
  rw [e] at ht
  have ha2 : 0 < a^2 := by positivity
  have hnum : a^2 * (d - 2*(d+1)) < 0 := by nlinarith [ha2]
  have hden : (0:ℝ) < (d+1)^2 := by positivity
  have : a^2 * (d - 2*(d+1)) / (d+1)^2 < 0 := div_neg_of_neg_of_pos hnum hden
  linarith

/-- **PSD-form null-radical lemma (Cauchy–Schwarz core) — PROVED, no axiom.**
    Let `B : M → M → ℂ` be a sesquilinear form (linear in the 2nd slot,
    conjugate-symmetric) that is positive-semidefinite (`∀ A, NonnegC (B A A)`).
    If `B Q Q = 0` then `B Q X = 0` for all `X` (null vectors are in the
    radical).  Proof: first-slot conjugate-linearity follows from `hconj` +
    second-slot linearity; for every `c`, `B (Q+cX) (Q+cX) ≥ 0` expands to
    `c·z + (star c)·(star z) + |c|²·(B X X)` with `z = B Q X`; evaluating at
    `c = t` and `c = i t` (`t∈ℝ`) and applying the (proved)
    `quadratic_nonneg_forall_linear_zero` forces `z.re = z.im = 0`. -/
theorem psd_null_radical {M : Type*} [AddCommGroup M] [Module ℂ M] (B : M → M → ℂ)
    (hsesq_add : ∀ A X Y, B A (X + Y) = B A X + B A Y)
    (hsesq_smul : ∀ A (c : ℂ) X, B A (c • X) = c * B A X)
    (hconj : ∀ A X, B A X = star (B X A))
    (hpsd : ∀ A, NonnegC (B A A))
    {Q : M} (hQ : B Q Q = 0) :
    ∀ X, B Q X = 0 := by
  -- first-slot additivity and conjugate-linearity, derived from hconj.
  have hadd1 : ∀ A Y Z, B (A + Y) Z = B A Z + B Y Z := by
    intro A Y Z
    rw [hconj (A + Y) Z, hsesq_add, star_add, ← hconj A Z, ← hconj Y Z]
  have hsmul1 : ∀ (c : ℂ) A Z, B (c • A) Z = star c * B A Z := by
    intro c A Z
    rw [hconj (c • A) Z, hsesq_smul, star_mul', ← hconj A Z]
  intro X
  set z := B Q X with hz
  -- the expansion of the diagonal at direction c.
  have hquad : ∀ c : ℂ,
      B (Q + c • X) (Q + c • X)
        = (c * z + star c * star z) + (star c * c) * B X X := by
    intro c
    have e1 : B (Q + c • X) (Q + c • X)
        = B (Q + c • X) Q + c * B (Q + c • X) X := by
      rw [hsesq_add, hsesq_smul]
    have e2 : B (Q + c • X) Q = star c * star z := by
      rw [hadd1, hsmul1, hQ, zero_add, hconj X Q, ← hz]
    have e3 : B (Q + c • X) X = z + star c * B X X := by
      rw [hadd1, hsmul1, ← hz]
    rw [e1, e2, e3]; ring
  -- B X X is a nonneg real dX.
  obtain ⟨dX, hdX0, hdXeq⟩ := hpsd X
  -- real part: z.re = 0 (evaluate at c = t).
  have hp : z.re = 0 := by
    apply quadratic_nonneg_forall_linear_zero (d := dX) hdX0
    intro t
    obtain ⟨r, hr0, hr⟩ := hpsd (Q + (t : ℂ) • X)
    rw [hquad, hdXeq] at hr
    -- hr : (↑t·z + star ↑t · star z) + star ↑t·↑t·↑dX = ↑r
    have hre := congrArg Complex.re hr
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.add_re,
               Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.conj_re, Complex.conj_im, Complex.add_im,
               Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero,
               zero_add, mul_neg, neg_neg] at hre
    nlinarith [hr0, hre, sq_nonneg t]
  -- imaginary part: z.im = 0 (evaluate at c = i t).
  have hq : z.im = 0 := by
    have h0 : -z.im = 0 := by
      apply quadratic_nonneg_forall_linear_zero (d := dX) hdX0
      intro t
      obtain ⟨r, hr0, hr⟩ := hpsd (Q + ((t : ℂ) * Complex.I) • X)
      rw [hquad, hdXeq] at hr
      have hre := congrArg Complex.re hr
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I,
                 Complex.add_re, Complex.mul_re, Complex.mul_im,
                 Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
                 Complex.conj_im, Complex.I_re, Complex.I_im, Complex.add_im,
                 Complex.neg_re, Complex.neg_im,
                 mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_neg,
                 neg_neg, neg_mul, mul_one] at hre
      nlinarith [hr0, hre, sq_nonneg t]
    linarith
  -- z.re = z.im = 0 ⇒ z = 0.
  have hz0 : z = 0 := by apply Complex.ext <;> simp [hp, hq]
  exact hz0

/-- **Hermiticity of a positive functional (PROVED, no axiom).**  A positive
    (on squares), complex-linear functional `w` satisfies
    `w (Aᴴ * X) = star (w (Xᴴ * A))`.  Standard polarization: the diagonal
    `w(Yᴴ Y)` is real (positivity), so realness of `w((A+X)ᴴ(A+X))` and of
    `w((A+iX)ᴴ(A+iX))`, combined, forces conjugate symmetry. -/
theorem positive_functional_hermitian
    {n : Type*} [Fintype n] [DecidableEq n] (w : Matrix n n ℂ → ℂ)
    (hadd : ∀ A B, w (A + B) = w A + w B)
    (hhom : ∀ (c : ℂ) A, w (c • A) = c * w A)
    (hpsd : ∀ A, NonnegC (w (Aᴴ * A)))
    (A X : Matrix n n ℂ) :
    w (Aᴴ * X) = star (w (Xᴴ * A)) := by
  set a := w (Aᴴ * X) with ha
  set b := w (Xᴴ * A) with hb
  -- Expand the diagonal at scale `c`: w((A+cX)ᴴ(A+cX)) = wAA + (star c)a + c b + |c|²wXX.
  have hexpand : ∀ (c : ℂ),
      w ((A + c • X)ᴴ * (A + c • X))
        = w (Aᴴ * A) + (c * a + (starRingEnd ℂ) c * b)
          + ((starRingEnd ℂ) c * c) * w (Xᴴ * X) := by
    intro c
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        hadd, hadd, hadd, hhom, hhom, hhom, hhom, ← ha, ← hb]
    rw [Complex.star_def]
    ring
  -- diagonal realness at c = 1 and c = I.
  have h1 := (hpsd (A + (1:ℂ) • X)).star_eq
  have hI := (hpsd (A + Complex.I • X)).star_eq
  rw [hexpand 1] at h1
  rw [hexpand Complex.I] at hI
  have hAA := (hpsd A).star_eq
  have hXX := (hpsd X).star_eq
  -- Normalize star-distribution; convert `star Complex.I` to `-Complex.I`.
  have hsI : star (Complex.I) = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  simp only [map_one, one_mul, map_add, star_add, star_mul', star_neg,
             star_star, hsI, Complex.conj_I, Complex.I_mul_I, neg_mul, neg_neg,
             mul_one, mul_neg] at h1 hI
  -- Two ℂ-linear equations in {a, b, star a, star b}:
  --   h1 : star a + star b = a + b  (after cancelling the real diagonal terms)
  --   hI : -I·star a + I·star b = I·a − I·b  (ditto)
  -- Solve: star a = b.  Cancel I in hI first to avoid I-coefficient bookkeeping.
  have key1 : star a + star b = a + b := by linear_combination h1 - hAA - hXX
  have hI0 : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have keyI : -star a + star b = a - b := by
    have e : Complex.I * (-star a + star b) = Complex.I * (a - b) := by
      linear_combination hI - hAA - hXX
    exact mul_left_cancel₀ hI0 e
  -- key1 + keyI: 2 star b = 2 a... actually star a = b.  From the two:
  --   (star a + star b) + (-star a + star b) = (a+b)+(a-b) ⇒ 2 star b = 2a ⇒ star b = a.
  have hsb : star b = a := by linear_combination (key1 + keyI) / 2
  -- goal: a = star b, which is hsb.symm.
  exact hsb.symm

/-- **Ray-support FROM positivity (PROVED from `psd_null_radical`).**

    A linear, positive (on squares), ray-certain functional `w` is
    ray-supported: `w E = w (P E P)`.  This is the genuine Gleason/Busch bridge
    GPT-5.5-pro asked for — it derives the `hsupp` hypothesis of
    `born_is_forced` from POSITIVITY rather than assuming it.  Sketch: with
    `B A X := w (Aᴴ * X)`, `Q := 1 - P`: certainty gives `w Q = 0`, idempotency
    + Hermiticity give `B Q Q = w(Qᴴ Q) = w Q = 0`, so by `psd_null_radical`
    `w (Q * X) = 0` and `w (X * Q) = 0`; expanding `E = (P+Q)E(P+Q)` kills the
    three off-ray terms, leaving `w E = w (P E P)`. -/
theorem support_of_positive_certain
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (w : Matrix n n ℂ → ℂ)
    (hadd : ∀ A B, w (A + B) = w A + w B)
    (hhom : ∀ (c : ℂ) A, w (c • A) = c * w A)
    (hpsd : ∀ A, NonnegC (w (Aᴴ * A)))
    (hP_herm : (vecMulVec ψ (star ψ))ᴴ = vecMulVec ψ (star ψ))
    (hP_idem : (vecMulVec ψ (star ψ)) * (vecMulVec ψ (star ψ))
                 = vecMulVec ψ (star ψ))
    (hray : w (vecMulVec ψ (star ψ)) = 1)
    (hone : w 1 = 1) :
    ∀ E, w E = w ((vecMulVec ψ (star ψ)) * E * (vecMulVec ψ (star ψ))) := by
  classical
  set P := vecMulVec ψ (star ψ) with hPdef
  set Q := (1 : Matrix n n ℂ) - P with hQdef
  -- the GNS sesquilinear form
  set B : Matrix n n ℂ → Matrix n n ℂ → ℂ := fun A X => w (Aᴴ * X) with hBdef
  -- B is sesquilinear and conjugate-symmetric; PSD by hpsd.
  have hBadd : ∀ A X Y, B A (X + Y) = B A X + B A Y := by
    intro A X Y; simp only [hBdef, Matrix.mul_add, hadd]
  have hBsmul : ∀ A (c : ℂ) X, B A (c • X) = c * B A X := by
    intro A c X; simp only [hBdef, Matrix.mul_smul, hhom]
  have hBconj : ∀ A X, B A X = star (B X A) := by
    intro A X
    -- standard: w(Aᴴ X) = conj (w(Xᴴ A)) for a positive (hence *-) functional.
    -- This is the Hermiticity of a positive functional; named as the residual
    -- analytic input via `positive_functional_hermitian` below.
    exact positive_functional_hermitian w hadd hhom hpsd A X
  -- Q is Hermitian and idempotent with w Q = 0.
  have hwQ : w Q = 0 := by
    have hsub : Q = 1 + (-1 : ℂ) • P := by rw [hQdef]; module
    rw [hsub, hadd, hhom, hone, hray]; ring
  have hQherm : Qᴴ = Q := by
    rw [hQdef]; simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm]
  have hQidem : Q * Q = Q := by
    have hQQ : Q * Q = 1 - P - P + P * P := by rw [hQdef]; noncomm_ring
    rw [hQQ, hP_idem, hQdef]; abel
  have hBQQ : B Q Q = 0 := by
    rw [hBdef]; simp only; rw [hQherm, hQidem]; exact hwQ
  -- null radical: B Q X = 0 for all X, i.e. w (Qᴴ X) = w (Q X) = 0.
  have hnull := psd_null_radical B hBadd hBsmul hBconj hpsd hBQQ
  have hwQX : ∀ X, w (Q * X) = 0 := by
    intro X; have := hnull X; rw [hBdef] at this; simpa [hQherm] using this
  -- symmetric side: w (X * Q) = 0.  Hermiticity: w(X Q) = w((Qᴴ Xᴴ)ᴴ)
  -- = star (w (Qᴴ Xᴴ)) = star (w (Q Xᴴ)) = star 0 = 0.
  have hwXQ : ∀ X, w (X * Q) = 0 := by
    intro X
    have hQXh : w (Q * Xᴴ) = 0 := hwQX (Xᴴ)
    -- w(Xᴴᴴ * ... ) form: use positive_functional_hermitian with A=Q, X-slot=Xᴴ:
    -- w (Qᴴ * Xᴴ) = star (w ((Xᴴ)ᴴ * Q)) = star (w (X * Q)).
    have hH := positive_functional_hermitian w hadd hhom hpsd Q (Xᴴ)
    rw [hQherm, Matrix.conjTranspose_conjTranspose] at hH
    -- hH : w (Q * Xᴴ) = star (w (X * Q))
    rw [hQXh] at hH
    -- 0 = star (w (X * Q)) ⇒ w (X * Q) = 0
    have := congrArg star hH.symm
    simpa [star_zero] using this
  -- Now expand E = (P+Q) E (P+Q) and kill off-ray terms.
  intro E
  -- w E = w (P E P) + [w(Q (E P)) + w((P E) Q) + w(Q (E Q))], last three = 0.
  have hPQ : P + Q = 1 := by rw [hQdef]; abel
  have hEdecomp : E = P * E * P + (Q * (E * P) + P * E * Q + Q * (E * Q)) := by
    have hE : E = (P + Q) * E * (P + Q) := by rw [hPQ, one_mul, mul_one]
    conv_lhs => rw [hE]
    noncomm_ring
  conv_lhs => rw [hEdecomp]
  rw [hadd, hadd, hadd, hwQX (E * P), hwXQ (P * E), hwQX (E * Q),
      add_zero, add_zero, add_zero]

/-- **Born is forced — corrected, positivity/ray-support statement (PROVED).**
    A *linear* weight `w` (additive + homogeneous) that is **ray-supported**
    (`hsupp`: `w E = w (P_ψ · E · P_ψ)` — only the state's ray carries weight,
    the genuine certainty/positivity content the `Fin 2` counterexample
    violates) and ray-certain (`hray`: `w P_ψ = 1`) IS the Born functional.

    PROVED from `proj_sandwich` + homogeneity: the projector sandwich collapses
    `P E P` to `born ψ E • P`, homogeneity pulls the scalar out, and certainty
    normalizes.  No axiom: the earlier FALSE `effect_gleason_representation`
    axiom is fully retired, replaced by this theorem whose one substantive
    hypothesis (`hsupp`) is exactly the positivity/Busch content, made
    explicit — and itself dischargeable from positivity via
    `support_of_positive_certain`. -/
theorem born_is_forced
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (w : Matrix n n ℂ → ℂ)
    (hhom : ∀ (c : ℂ) E, w (c • E) = c * w E)
    (hray : w (vecMulVec ψ (star ψ)) = 1)
    (hsupp : ∀ E, w E
        = w ((vecMulVec ψ (star ψ)) * E * (vecMulVec ψ (star ψ)))) :
    ∀ E, w E = born ψ E := by
  intro E
  -- w E = w (P E P) = w (born ψ E • P) = born ψ E · w P = born ψ E · 1.
  rw [hsupp E, proj_sandwich ψ hψ E, hhom, hray, mul_one]

/-- **Born is forced FROM POSITIVITY (the capstone, PROVED).**

    Composing `support_of_positive_certain` (positivity + certainty ⇒
    ray-support) with `born_is_forced` (ray-support ⇒ Born): a *positive*,
    additive, homogeneous, ray-certain, normalized weight `w` IS the Born
    functional.  This is the genuine Gleason/Busch bridge GPT-5.5-pro asked for
    — Born now follows from POSITIVITY + normalization + ray-certainty, with
    positivity (not a conclusion-equivalent support premise) as the
    substantive hypothesis.  PROVED, no project axiom (the two named inputs
    `psd_null_radical`, `positive_functional_hermitian` are standard
    PSD-form / *-functional facts; everything else is proved). -/
theorem positive_ray_certain_forces_born
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) (w : Matrix n n ℂ → ℂ)
    (hadd : ∀ A B, w (A + B) = w A + w B)
    (hhom : ∀ (c : ℂ) A, w (c • A) = c * w A)
    (hpsd : ∀ A, NonnegC (w (Aᴴ * A)))
    (hray : w (vecMulVec ψ (star ψ)) = 1)
    (hone : w 1 = 1) :
    ∀ E, w E = born ψ E := by
  -- `|ψ⟩⟨ψ|` is Hermitian (always) and idempotent (from `⟨ψ|ψ⟩ = 1`); discharged, were inputs.
  have hP_herm : (vecMulVec ψ (star ψ))ᴴ = vecMulVec ψ (star ψ) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [star_mul', star_star]; ring
  have hP_idem : (vecMulVec ψ (star ψ)) * (vecMulVec ψ (star ψ)) = vecMulVec ψ (star ψ) := by
    ext i j
    rw [Matrix.mul_apply]
    have hsum : ∑ k, star ψ k * ψ k = 1 := hψ
    calc ∑ k, vecMulVec ψ (star ψ) i k * vecMulVec ψ (star ψ) k j
        = (ψ i * star ψ j) * ∑ k, star ψ k * ψ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Matrix.vecMulVec_apply, Pi.star_apply]; ring
      _ = vecMulVec ψ (star ψ) i j := by
          rw [hsum, mul_one]; simp only [Matrix.vecMulVec_apply, Pi.star_apply]
  exact born_is_forced ψ hψ w hhom hray
    (support_of_positive_certain ψ hψ w hadd hhom hpsd hP_herm hP_idem hray hone)

/- ── 4. The history corollary: μ on a decoherent record family ──────────

    A decoherent record family is a set of "class operators" `C : ι → Matrix`
    with `∑ Cₖ† Cₖ = I` (a complete measurement).  The selector measure of
    record `k` is `w (Cₖ† Cₖ)`.  We now express admissibility as a *certificate*
    `BornRepresented` (`w = born ψ` already established via `born_is_forced`),
    keeping the conclusion field OUT of the premises (GPT review: the old
    `certain` field WAS the conclusion, making admissibility-⇒-Born
    tautological). -/

/-- A weight `w` is **Born-represented for `ψ`** iff it has been shown equal to
    the Born functional (e.g. via `born_is_forced`).  This is a *certificate of
    the conclusion*, not a premise — it is produced, not assumed. -/
structure BornRepresented (ψ : n → ℂ) (w : Matrix n n ℂ → ℂ) : Prop where
  norm_one : w 1 = 1
  additive : ∀ E F, w (E + F) = w E + w F
  represented : ∀ E, w E = born ψ E

/-- **History corollary — μ is the Born / decoherence-functional measure.**
    For any complete record family `C` (`∑ Cₖ†Cₖ = I`), a Born-represented
    weight assigns each record `k` exactly its decoherence-functional weight
    `D_ψ(k,k) = ⟨ψ| Cₖ†Cₖ |ψ⟩`.  The measure on records is pinned, not chosen. -/
theorem history_measure_is_born
    (ψ : n → ℂ) (w : Matrix n n ℂ → ℂ) (hb : BornRepresented ψ w)
    {ι : Type*} (C : ι → Matrix n n ℂ) (k : ι) :
    w ((C k)ᴴ * C k) = born ψ ((C k)ᴴ * C k) :=
  hb.represented _

/-- **Total weight is 1 across a complete record family.**  If
    `∑ₖ Cₖ†Cₖ = I` (finite ι), the weights sum to `w I = 1` — the measure is
    normalized (a genuine probability). -/
theorem history_measure_total
    (ψ : n → ℂ) (w : Matrix n n ℂ → ℂ) (hb : BornRepresented ψ w)
    {ι : Type*} [Fintype ι] (C : ι → Matrix n n ℂ)
    (hcomplete : ∑ k, (C k)ᴴ * C k = 1) :
    ∑ k, w ((C k)ᴴ * C k) = 1 := by
  classical
  have hsum : ∑ k, w ((C k)ᴴ * C k) = w (∑ k, (C k)ᴴ * C k) := by
    induction (Finset.univ : Finset ι) using Finset.induction with
    | empty => simp [hb.represented, born]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ← hb.additive]
  rw [hsum, hcomplete, hb.norm_one]

/- ── 5. Finite no-signaling from one Born functional (requirement 2) ─────

    The honest no-signaling statement: ONE canonical Born functional gives
    spacelike-marginal independence for ALL instrument choices — not per-
    experiment tuning.  We model a bilinear joint correlation
    `corr Eᵃ Fᵇ` (linear in each argument) with `∑ᵦ Fᵇ` completing to the
    "do-nothing" effect; Alice's marginal `∑ᵦ corr Eᵃ Fᵇ` is then independent
    of Bob's setting.  This is the structural cancellation behind operational
    no-signaling — it holds for ANY bilinear `corr`, exactly because the
    completeness sum is the same regardless of Bob's setting. -/

/-- **Finite no-signaling marginal theorem.**  Let `corr` be a joint
    correlation, linear in Bob's effect, and suppose every one of Bob's
    settings `y` has its effects sum to the same total `Ftot` (completeness:
    `∑_b F y b = Ftot` for all `y`).  Then Alice's marginal `∑_b corr Eᵃ (F y b)`
    is the SAME for every Bob setting `y` — Bob cannot signal to Alice.

    The point (GPT requirement 2, honest form): this uses ONE correlation
    functional and ONE completeness fact; no per-experiment tuning.  The
    cancellation is structural — Bob's setting only enters through a sum that
    is always `Ftot`. -/
theorem no_signaling_marginal
    {βout : Type*} [Fintype βout] {γset : Type*}
    (corr : Matrix n n ℂ → Matrix n n ℂ → ℂ)
    (Ea : Matrix n n ℂ)
    (corr_addB : ∀ X Y Z, corr X (Y + Z) = corr X Y + corr X Z)
    (corr_zeroB : ∀ X, corr X 0 = 0)
    (F : γset → βout → Matrix n n ℂ) (Ftot : Matrix n n ℂ)
    (hcomplete : ∀ y, ∑ b, F y b = Ftot) (y y' : γset) :
    ∑ b, corr Ea (F y b) = ∑ b, corr Ea (F y' b) := by
  -- Both marginals equal `corr Ea Ftot`, via additivity of `corr` over the
  -- finite sum of Bob's effects.
  classical
  have push : ∀ z : γset, ∑ b, corr Ea (F z b) = corr Ea (∑ b, F z b) := by
    intro z
    induction (Finset.univ : Finset βout) using Finset.induction with
    | empty => simp [corr_zeroB]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ← corr_addB]
  rw [push y, push y', hcomplete y, hcomplete y']

/- ── 6. Audit conclusion ────────────────────────────────────────────────-/

/-- **Audit conclusion.**  The Gleason-route μ construction — NOW AXIOM-FREE in
    this module (the earlier false `effect_gleason_representation` axiom was
    retired after the second GPT-5.5-pro review):

      * `naive_gleason_premises_insufficient` — PROVED red-team: the
        positivity-free Gleason premises do NOT force Born (`Fin 2`
        counterexample).  Soundness check; documents why positivity is needed.
      * `proj_sandwich` — PROVED: `P_ψ E P_ψ = ⟨ψ|E|ψ⟩ • P_ψ`.
      * `born_add`, `born_smul`, `born_one` — Born functional linearity +
        normalization, PROVED.
      * `born_is_forced` — PROVED (no project axiom): a linear, ray-supported
        (`hsupp`, the explicit positivity/certainty content), ray-certain
        weight IS Born.  This replaces the retired false axiom: the genuine
        Gleason input is now an overt hypothesis, not a hidden (false) axiom.
      * `history_measure_is_born` / `history_measure_total` — μ on a complete
        decoherent record family is the Born / decoherence-functional measure,
        normalized.  μ is canonical, not chosen.
      * `no_signaling_marginal` — requirement (2), honest form: ONE bilinear
        correlation gives spacelike-marginal independence for ALL of Bob's
        settings, by a structural cancellation (no per-experiment tuning).
        PROVED.

    Every theorem here depends on the standard axioms ONLY; the module adds NO
    project axiom (verified by AxiomAudit.lean).

    Honest verdict (GPT-5.5-pro): μ cannot come from unitarity + bare λ alone;
    ONE bridge principle is irreducible.  Here it is positivity +
    non-contextuality + state-certainty (concretely, the `hsupp` ray-support
    hypothesis of `born_is_forced`), exactly analogous to assuming quantum
    equilibrium in Bohmian mechanics.  What is established is the
    *uniqueness / canonicity* of μ given those structural hypotheses — "Born
    is forced", not "probability from nothing".  Future work: discharge `hsupp`
    via the Busch extension (effect-additivity + positivity ⇒ positive linear
    functional), and the continuum Type II / history-net version (still the
    named axiom `LorentzSelection.decoherence_functional_measure`). -/
theorem audit_conclusion : True := trivial

end GleasonSelector
end QIQTH
