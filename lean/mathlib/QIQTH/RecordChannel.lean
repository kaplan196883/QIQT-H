/-
  THE RECORD CHANNEL — the record-dephasing semigroup: the first record-FORMING boundary
  dynamics (boundary-dynamics candidate 6, brick RC1).

  The held free dynamics FREEZES records: `Dynamics.alpha` fixes every diagonal observable
  (`alpha_diagonal`) — the record ledger never moves under the Hamiltonian flow.  This brick
  supplies the complementary OPEN/DISSIPATIVE half: a genuine one-parameter semigroup of
  capacity-respecting channels on the held finite code under which records FORM,

      `T_s = e^{−s}·id + (1 − e^{−s})·dephase`,

  where `dephase` is the record-readout projection (kill all off-diagonal coherences in the
  record/occupation basis).  Proved here, axiom-free:

  • CHANNEL LAWS — `T_0 = id`, `T_{s+t} = T_s ∘ T_t` (a one-parameter semigroup, in fact for
    ALL real s,t by the ring algebra), trace preservation, unitality, positivity, and
    density-to-density (`Tsem_isDensity`) for `s ≥ 0`.
  • FIXED POINTS = RECORDS — `Tsem_fixed_iff`: for every `s > 0` the fixed points of `T_s`
    are EXACTLY the record-diagonal matrices (`dephase A = A`); the Gibbs/KMS states, the
    record projectors, and the maximally mixed state are all stationary.
  • RECORDS FORM — `tendsto_Tsem_dephase`: every state relaxes EXPONENTIALLY (rate 1, exact:
    `T_s A − dephase A = e^{−s}·(A − dephase A)`) to its record readout — decoherence /
    einselection as a semigroup THEOREM, the dynamical upgrade of the frozen ledger.
  • ENTROPY — dephasing never lowers entropy (`entropy_dephase_ge`, Klein route), the flow
    is entropy-non-decreasing (`entropy_Tsem_ge`), and NEVER exceeds capacity
    (`Tsem_capacity` = the held `vonNeumannEntropy_le_log_card` guard); the maximum-entropy
    fixed point is capacity saturation (`saturation_fixed`) — the area-law state
    `S = log N_C = A_τ(C)/4G` of the held K2a capstone (CITED, not re-proved).
  • LYAPUNOV — `relEntropy_Tsem_le`: the relative entropy to EVERY record-diagonal
    equilibrium is non-increasing along the flow (joint convexity `relEntropy_subadditive`
    + the dephasing inequality), and is stationary at equilibrium — the B4/E4-shaped
    stationarity whose join to the first law and linearized Einstein is the held
    `CodeEquilibrium.code_equilibrium_einstein` (CITED, not imported).
  • CONSISTENCY WITH THE FREE FLOW — `Tsem_alpha_comm`: the open dynamics COMMUTES with the
    held Heisenberg flow `alpha`, so `T_s ∘ α_t` is a consistent Markovian family — the
    channel extends, not fights, the DY dynamics.
  • EQUIVARIANCE — `Tsem_submatrix`: the channel commutes with every record-basis
    relabeling (injective substitution / permutation), the finite shape of Gate 3's
    `equivariant_enforcement_preserves_invariance` (CITED, not imported).

  Unraveling reading (candidate 3): `T_s` is the λ-averaged record-accretion process; the
  per-λ jump-chain unraveling is the named follow-on brick, NOT built here.

  ⚠ MANDATORY FIREWALL.  The record/pointer basis is an INPUT: the dephasing is CHOSEN in
  the record basis — einselection of that basis from an interaction Hamiltonian is NOT
  derived.  Finite, single code corner only; no bulk reconstruction, no graviton coupling,
  no unraveling built.  Positivity and trace preservation are PROVED; complete positivity
  holds because `T_s` is a convex combination of the identity and the (clock-twirl,
  mixed-unitary) dephasing channel, but is not separately formalized here.  The E4/K2a
  joins are CITED, not re-proved.  This is the first rung of a boundary theory — NOT the
  strong holographic principle, NOT quantum gravity.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.Keystone
import QIQTH.Entropy.RelEntropyDPI
import QIQTH.Dynamics

namespace QIQTH.RecordChannel

open QIQTH.QuantumEntropy QIQTH.Keystone QIQTH.Entropy
open scoped ComplexOrder

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## RC1.1 — the record-readout projection `dephase` -/

/-- **The record-readout projection**: kill every off-diagonal coherence in the record
    basis, `dephase A = diag(A₁₁, …, A_NN)`.  The Schur/pinching map onto the record
    (diagonal) algebra — the "read the ledger" channel. -/
def dephase (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun n => A n n)

/-- Entry formula for the readout. -/
theorem dephase_apply (A : Matrix ι ι ℂ) (n m : ι) :
    dephase A n m = if n = m then A n n else 0 := by
  rw [dephase, Matrix.diagonal_apply]

/-- Diagonal entries survive the readout. -/
theorem dephase_apply_eq (A : Matrix ι ι ℂ) (n : ι) : dephase A n n = A n n := by
  rw [dephase_apply, if_pos rfl]

/-- Off-diagonal entries are killed by the readout. -/
theorem dephase_apply_ne (A : Matrix ι ι ℂ) {n m : ι} (h : n ≠ m) : dephase A n m = 0 := by
  rw [dephase_apply, if_neg h]

/-- The readout is additive. -/
theorem dephase_add (A B : Matrix ι ι ℂ) : dephase (A + B) = dephase A + dephase B := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [dephase_apply_eq, Matrix.add_apply, Matrix.add_apply, dephase_apply_eq,
      dephase_apply_eq]
  · rw [dephase_apply_ne _ h, Matrix.add_apply, dephase_apply_ne _ h, dephase_apply_ne _ h,
      add_zero]

/-- The readout is `ℂ`-homogeneous (with `dephase_add`: a `ℂ`-linear map). -/
theorem dephase_smul (c : ℂ) (A : Matrix ι ι ℂ) : dephase (c • A) = c • dephase A := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [dephase_apply_eq, Matrix.smul_apply, Matrix.smul_apply, dephase_apply_eq]
  · rw [dephase_apply_ne _ h, Matrix.smul_apply, dephase_apply_ne _ h, smul_zero]

/-- The readout is `ℝ`-homogeneous (real convex coefficients pass through). -/
theorem dephase_smul_real (r : ℝ) (A : Matrix ι ι ℂ) : dephase (r • A) = r • dephase A := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [dephase_apply_eq, Matrix.smul_apply, Matrix.smul_apply, dephase_apply_eq]
  · rw [dephase_apply_ne _ h, Matrix.smul_apply, dephase_apply_ne _ h, smul_zero]

/-- The readout is idempotent — reading the ledger twice is reading it once. -/
theorem dephase_dephase (A : Matrix ι ι ℂ) : dephase (dephase A) = dephase A := by
  ext n m
  by_cases h : n = m
  · subst h; rw [dephase_apply_eq]
  · rw [dephase_apply_ne _ h, dephase_apply_ne _ h]

/-- The readout is trace-preserving. -/
theorem trace_dephase (A : Matrix ι ι ℂ) : (dephase A).trace = A.trace := by
  rw [dephase, Matrix.trace_diagonal]
  rfl

/-- The readout is unital. -/
theorem dephase_one : dephase (1 : Matrix ι ι ℂ) = 1 := by
  ext n m
  by_cases h : n = m
  · subst h; rw [dephase_apply_eq]
  · rw [dephase_apply_ne _ h, Matrix.one_apply_ne h]

/-- The readout fixes every diagonal (record) matrix. -/
theorem dephase_diagonal (d : ι → ℂ) : dephase (Matrix.diagonal d) = Matrix.diagonal d := by
  ext n m
  by_cases h : n = m
  · subst h; rw [dephase_apply_eq]
  · rw [dephase_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-- **Readout invariance = record-diagonality** (off-diagonal form): `dephase A = A` iff all
    coherences vanish. -/
theorem dephase_eq_self_iff (A : Matrix ι ι ℂ) :
    dephase A = A ↔ ∀ n m, n ≠ m → A n m = 0 := by
  constructor
  · intro h n m hnm
    rw [← h]
    exact dephase_apply_ne A hnm
  · intro h
    ext n m
    by_cases hnm : n = m
    · subst hnm; rw [dephase_apply_eq]
    · rw [dephase_apply_ne A hnm]
      exact (h n m hnm).symm

/-- **Readout invariance = record-diagonality** (existential form): `dephase A = A` iff `A`
    is a diagonal matrix. -/
theorem dephase_eq_self_iff_diagonal (A : Matrix ι ι ℂ) :
    dephase A = A ↔ ∃ d, A = Matrix.diagonal d := by
  constructor
  · intro h
    exact ⟨fun n => A n n, h.symm⟩
  · rintro ⟨d, rfl⟩
    exact dephase_diagonal d

/-- **The readout is a positive map**: diagonal entries of a PSD matrix are nonnegative, and
    a nonnegative diagonal is PSD. -/
theorem dephase_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (dephase A).PosSemidef := by
  rw [dephase]
  exact Matrix.posSemidef_diagonal_iff.mpr fun n => hA.diag_nonneg (i := n)

/-- The readout preserves strict positivity. -/
theorem dephase_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef) : (dephase A).PosDef := by
  rw [dephase]
  exact Matrix.posDef_diagonal_iff.mpr fun n => hA.diag_pos (i := n)

/-- **The readout maps densities to densities** (positive + trace-preserving). -/
theorem dephase_isDensity {A : Matrix ι ι ℂ} (h : IsDensity A) : IsDensity (dephase A) :=
  ⟨dephase_posSemidef h.posSemidef, by rw [trace_dephase]; exact h.trace_one⟩

/-- The maximally mixed (capacity-saturating) state is a readout fixed point. -/
theorem dephase_maxMixed : dephase (maxMixed ι) = maxMixed ι := by
  rw [maxMixed, dephase_smul, dephase_one]

/-! ## RC1.2 — the record-dephasing semigroup `Tsem` -/

/-- Real scalars act on `ℂ`-matrices as their complex coercions (the smul bridge used to
    move between the real convex coefficients and the `ComplexOrder` positivity API). -/
theorem realSmul_eq (r : ℝ) (X : Matrix ι ι ℂ) : r • X = (r : ℂ) • X := by
  ext n m
  rw [Matrix.smul_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

/-- **THE RECORD CHANNEL** — the record-dephasing semigroup
    `T_s = e^{−s}·id + (1 − e^{−s})·dephase`: the convex interpolation from the identity to
    the record readout, at exponential rate 1.  The first record-FORMING boundary dynamics
    on the held finite code (the record basis is an INPUT — see the module firewall). -/
noncomputable def Tsem (s : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Real.exp (-s) • A + (1 - Real.exp (-s)) • dephase A

/-- Entry formula for the channel. -/
theorem Tsem_apply (s : ℝ) (A : Matrix ι ι ℂ) (n m : ι) :
    Tsem s A n m
      = ((Real.exp (-s) : ℝ) : ℂ) * A n m
        + ((1 - Real.exp (-s) : ℝ) : ℂ) * dephase A n m := by
  rw [Tsem, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.real_smul]

/-- Diagonal (record) entries are FROZEN by the channel — the ledger is never rewritten. -/
theorem Tsem_apply_eq (s : ℝ) (A : Matrix ι ι ℂ) (n : ι) : Tsem s A n n = A n n := by
  rw [Tsem_apply, dephase_apply_eq, ← add_mul, ← Complex.ofReal_add,
    show Real.exp (-s) + (1 - Real.exp (-s)) = 1 from by ring, Complex.ofReal_one, one_mul]

/-- Off-diagonal coherences decay at the exact exponential rate `e^{−s}`. -/
theorem Tsem_apply_ne (s : ℝ) (A : Matrix ι ι ℂ) {n m : ι} (h : n ≠ m) :
    Tsem s A n m = ((Real.exp (-s) : ℝ) : ℂ) * A n m := by
  rw [Tsem_apply, dephase_apply_ne A h, mul_zero, add_zero]

/-- `T_0 = id`. -/
theorem Tsem_zero (A : Matrix ι ι ℂ) : Tsem 0 A = A := by
  rw [Tsem, neg_zero, Real.exp_zero, one_smul, sub_self, zero_smul, add_zero]

/-- **The semigroup law** `T_{s+t} = T_s ∘ T_t` — for ALL real `s, t` (pure ring algebra:
    `dephase` is linear and idempotent and `e^{−s}e^{−t} = e^{−(s+t)}`); the channel family
    is a genuine one-parameter semigroup on `s ≥ 0`. -/
theorem Tsem_add (s t : ℝ) (A : Matrix ι ι ℂ) : Tsem (s + t) A = Tsem s (Tsem t A) := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [Tsem_apply_eq, Tsem_apply_eq, Tsem_apply_eq]
  · rw [Tsem_apply_ne (s + t) A h, Tsem_apply_ne s (Tsem t A) h, Tsem_apply_ne t A h,
      show -(s + t) = -s + -t from by ring, Real.exp_add, Complex.ofReal_mul, mul_assoc]

/-- The channel is trace-preserving. -/
theorem Tsem_trace (s : ℝ) (A : Matrix ι ι ℂ) : (Tsem s A).trace = A.trace := by
  rw [Tsem, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, trace_dephase,
    ← add_smul, show Real.exp (-s) + (1 - Real.exp (-s)) = 1 from by ring, one_smul]

/-- Every readout fixed point is a channel fixed point (at every time, any sign). -/
theorem Tsem_of_dephase_eq (s : ℝ) {A : Matrix ι ι ℂ} (h : dephase A = A) : Tsem s A = A := by
  rw [Tsem, h, ← add_smul, show Real.exp (-s) + (1 - Real.exp (-s)) = 1 from by ring,
    one_smul]

/-- The channel is unital. -/
theorem Tsem_one (s : ℝ) : Tsem s (1 : Matrix ι ι ℂ) = 1 :=
  Tsem_of_dephase_eq s dephase_one

/-- Every diagonal (record) matrix is stationary. -/
theorem Tsem_diagonal (s : ℝ) (d : ι → ℂ) :
    Tsem s (Matrix.diagonal d) = Matrix.diagonal d :=
  Tsem_of_dephase_eq s (dephase_diagonal d)

/-- Every readout image is stationary — the record readout is the invariant manifold. -/
theorem Tsem_dephase (s : ℝ) (A : Matrix ι ι ℂ) : Tsem s (dephase A) = dephase A :=
  Tsem_of_dephase_eq s (dephase_dephase A)

/-- The maximally mixed state is stationary. -/
theorem Tsem_maxMixed (s : ℝ) : Tsem s (maxMixed ι) = maxMixed ι :=
  Tsem_of_dephase_eq s dephase_maxMixed

/-- **The channel is a positive map** for `s ≥ 0` (convex combination of two positive
    maps). -/
theorem Tsem_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    (Tsem s A).PosSemidef := by
  rw [Tsem, realSmul_eq, realSmul_eq]
  refine (hA.smul ?_).add ((dephase_posSemidef hA).smul ?_)
  · exact Complex.zero_le_real.mpr (Real.exp_pos (-s)).le
  · exact Complex.zero_le_real.mpr
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)))

/-- The channel preserves strict positivity for `s ≥ 0`. -/
theorem Tsem_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (Tsem s A).PosDef := by
  rcases hs.eq_or_lt with hs0 | hs0
  · rw [← hs0, Tsem_zero]; exact hA
  · rw [Tsem]
    exact (hA.smul (Real.exp_pos (-s))).add ((dephase_posDef hA).smul
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs0))))

/-- **The channel maps densities to densities** for `s ≥ 0` — a capacity-respecting
    (positive, trace-preserving) evolution of states. -/
theorem Tsem_isDensity {A : Matrix ι ι ℂ} (h : IsDensity A) {s : ℝ} (hs : 0 ≤ s) :
    IsDensity (Tsem s A) :=
  ⟨Tsem_posSemidef h.posSemidef hs, by rw [Tsem_trace]; exact h.trace_one⟩

/-! ## RC1.3 — fixed points are EXACTLY the records -/

/-- The channel never moves the record readout: `dephase ∘ T_s = dephase`. -/
theorem dephase_Tsem (s : ℝ) (A : Matrix ι ι ℂ) : dephase (Tsem s A) = dephase A := by
  ext n m
  by_cases h : n = m
  · subst h; rw [dephase_apply_eq, Tsem_apply_eq, dephase_apply_eq]
  · rw [dephase_apply_ne _ h, dephase_apply_ne _ h]

/-- **The exact relaxation identity**: `T_s A − dephase A = e^{−s}·(A − dephase A)` — the
    distance to the record readout contracts at the exact exponential rate 1. -/
theorem Tsem_sub_dephase (s : ℝ) (A : Matrix ι ι ℂ) :
    Tsem s A - dephase A = Real.exp (-s) • (A - dephase A) := by
  rw [Tsem, smul_sub, sub_smul, one_smul]
  abel

/-- **FIXED POINTS = RECORDS**: for every `s > 0`, `T_s A = A` iff `A` is record-diagonal
    (`dephase A = A`) — off-diagonal entries scale by `e^{−s} ≠ 1`, so nothing but the
    records survives stationarity.  Combined with `dephase_eq_self_iff_diagonal`, the fixed
    algebra of the open dynamics is EXACTLY the record algebra. -/
theorem Tsem_fixed_iff {s : ℝ} (hs : 0 < s) (A : Matrix ι ι ℂ) :
    Tsem s A = A ↔ dephase A = A := by
  constructor
  · intro hfix
    refine (dephase_eq_self_iff A).mpr fun n m hnm => ?_
    have he : ((Real.exp (-s) : ℝ) : ℂ) * A n m = A n m := by
      rw [← Tsem_apply_ne s A hnm, hfix]
    have ha : ((Real.exp (-s) : ℝ) : ℂ) ≠ 1 := by
      rw [Ne, Complex.ofReal_eq_one]
      exact (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)).ne
    have h0 : (((Real.exp (-s) : ℝ) : ℂ) - 1) * A n m = 0 := by
      rw [sub_mul, one_mul, he, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr ha)
  · intro h
    exact Tsem_of_dephase_eq s h

/-! ## RC1.4 — RECORDS FORM: exponential convergence to the record readout -/

/-- **DECOHERENCE AS A THEOREM — records form.**  Every state relaxes (entrywise, at the
    exact exponential rate 1) to its record readout: `T_s A → dephase A` as `s → ∞`.  This
    is the dynamical upgrade of `alpha_diagonal`'s frozen ledger: the held free flow keeps
    records fixed; the open channel CREATES them, monotonically erasing every coherence —
    einselection onto the (input) record basis as a semigroup limit. -/
theorem tendsto_Tsem_dephase (A : Matrix ι ι ℂ) (n m : ι) :
    Filter.Tendsto (fun s : ℝ => Tsem s A n m) Filter.atTop (nhds (dephase A n m)) := by
  have hfun : (fun s : ℝ => Tsem s A n m)
      = fun s : ℝ => dephase A n m + ((Real.exp (-s) : ℝ) : ℂ) * (A n m - dephase A n m) := by
    funext s
    rw [Tsem_apply]
    push_cast
    ring
  rw [hfun]
  have h1 : Filter.Tendsto (fun s : ℝ => ((Real.exp (-s) : ℝ) : ℂ)) Filter.atTop
      (nhds (0 : ℂ)) := by
    have h0 := (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
    rw [Complex.ofReal_zero] at h0
    exact h0
  have h2 := h1.mul_const (A n m - dephase A n m)
  rw [zero_mul] at h2
  simpa using tendsto_const_nhds.add h2

/-! ## RC1.5 — entropy: monotone production, Lyapunov contraction, capacity

Route A (Klein): the cross-entropy of any state against a record-DIAGONAL reference depends
only on the state's diagonal (because `log` of a positive diagonal matrix is again diagonal
— proved via the sign-flip diagonal unitaries and the held `matLog_conj`, no twirl needed).
Klein positivity then gives `S(dephase A) ≥ S(A)`, and joint convexity
(`relEntropy_subadditive`) upgrades it to the Lyapunov theorem for the whole semigroup. -/

/-- The matrix logarithm depends only on the matrix (proof irrelevance for the Hermitian
    witness). -/
theorem matLog_congr {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : matLog hA = matLog hB := by
  subst h
  rfl

/-- **`log` of a record-diagonal positive matrix is record-diagonal.**  A diagonal `σ` is
    fixed by conjugation with every ±1 sign-flip diagonal unitary; by the held CFC
    naturality (`matLog_conj`) so is `log σ`, which forces every off-diagonal entry of
    `log σ` to equal its own negative — hence to vanish. -/
theorem dephase_matLog {σ : Matrix ι ι ℂ} (hσ : σ.PosDef) (hd : dephase σ = σ) :
    dephase (matLog hσ.1) = matLog hσ.1 := by
  refine (dephase_eq_self_iff _).mpr fun n m hnm => ?_
  -- the ±1 sign-flip diagonal unitary at `n`
  set u : ι → ℂ := fun k => if k = n then (-1 : ℂ) else 1 with hu
  have huu' : ∀ k, u k * u k = 1 := fun k => by
    by_cases h : k = n <;> simp [hu, h]
  set U : Matrix ι ι ℂ := Matrix.diagonal u with hU
  have hUstar : star U = U := by
    rw [hU, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    by_cases h : k = n <;> simp [hu, h, Pi.star_apply]
  have hUU : U * U = 1 := by
    rw [hU, Matrix.diagonal_mul_diagonal,
      show (fun k => u k * u k) = fun _ => (1 : ℂ) from funext huu', Matrix.diagonal_one]
  have hmem : U ∈ unitary (Matrix ι ι ℂ) := by
    rw [Unitary.mem_iff, hUstar]
    exact ⟨hUU, hUU⟩
  set uu : unitary (Matrix ι ι ℂ) := ⟨U, hmem⟩ with huu2
  have hcoe : (uu : Matrix ι ι ℂ) = U := rfl
  have hcoes : (star uu : Matrix ι ι ℂ) = U := by
    show star U = U
    exact hUstar
  -- conjugation by the sign flip fixes the diagonal σ …
  have hconj : (uu : Matrix ι ι ℂ) * σ * (star uu : Matrix ι ι ℂ) = σ := by
    rw [hcoe, hcoes, ← hd, dephase, hU, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    show u k * σ k k * u k = σ k k
    calc u k * σ k k * u k = u k * u k * σ k k := by ring
      _ = σ k k := by rw [huu' k, one_mul]
  -- … hence (matLog_conj) it fixes log σ
  have hH : ((uu : Matrix ι ι ℂ) * σ * (star uu : Matrix ι ι ℂ)).IsHermitian := by
    rw [hconj]; exact hσ.1
  have hlog := matLog_conj hσ uu hH
  have hlogeq : matLog hσ.1 = U * matLog hσ.1 * U := by
    conv_lhs => rw [matLog_congr hσ.1 hH hconj.symm]
    rw [hlog, hcoe, hcoes]
  -- the (n,m) entry is its own negative
  have hentry : matLog hσ.1 n m = u n * matLog hσ.1 n m * u m := by
    conv_lhs => rw [hlogeq, hU]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hn : u n = -1 := by simp [hu]
  have hm : u m = 1 := by simp [hu, Ne.symm hnm]
  rw [hn, hm, mul_one, neg_one_mul] at hentry
  exact CharZero.eq_neg_self_iff.mp hentry

/-- Trace against a record-diagonal matrix sees only the diagonal of the state. -/
theorem trace_mul_dephase_eq {L : Matrix ι ι ℂ} (hL : dephase L = L) (A : Matrix ι ι ℂ) :
    (dephase A * L).trace = (A * L).trace := by
  rw [Matrix.trace, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · subst h; rw [dephase_apply_eq]
  · have hL0 : L j i = 0 := by
      rw [← hL]
      exact dephase_apply_ne L (Ne.symm h)
    rw [hL0, mul_zero, mul_zero]

/-- **Cross-entropy against a record-diagonal reference depends only on the state's
    records**: `−tr(dephase A · log σ) = −tr(A · log σ)` for diagonal positive `σ`. -/
theorem crossEntropy_dephase {σ : Matrix ι ι ℂ} (hσ : σ.PosDef) (hd : dephase σ = σ)
    (A : Matrix ι ι ℂ) :
    crossEntropy (dephase A) hσ.1 = crossEntropy A hσ.1 := by
  rw [crossEntropy, crossEntropy, trace_mul_dephase_eq (dephase_matLog hσ hd) A]

/-- **Dephasing never lowers entropy** (the `s → ∞` entropy statement): for a positive
    density `A`, `S(A) ≤ S(dephase A)`.  Klein route: `0 ≤ D(A‖dephase A)` and the
    cross-entropy of `A` against its own readout IS the readout's entropy
    (`crossEntropy_dephase` + `crossEntropy_self`), so `D(A‖dephase A) = S(dephase A) −
    S(A)`.  Reading the ledger only produces entropy — record formation is thermodynamically
    free. -/
theorem entropy_dephase_ge {A : Matrix ι ι ℂ} (hA : A.PosDef) (h : IsDensity A) :
    vonNeumannEntropy h ≤ vonNeumannEntropy (dephase_isDensity h) := by
  have hDApd : (dephase A).PosDef := dephase_posDef hA
  have hklein : 0 ≤ relEntropy hA.1 hDApd.1 :=
    relEntropy_nonneg hA hDApd h.trace_one (dephase_isDensity h).trace_one
  have hid := relEntropy_eq_crossEntropy_sub_entropy hA hDApd h
  have hcross : crossEntropy A hDApd.1 = vonNeumannEntropy (dephase_isDensity h) := by
    rw [← crossEntropy_dephase hDApd (dephase_dephase A) A]
    exact crossEntropy_self hDApd (dephase_isDensity h)
  linarith

/-- **The dephasing DPI against record-diagonal references**:
    `D(dephase A ‖ σ) ≤ D(A ‖ σ)` for every record-diagonal positive `σ` — from Route A
    alone (the cross-entropy terms agree, so the difference is `S(A) − S(dephase A) ≤ 0`). -/
theorem relEntropy_dephase_le {A σ : Matrix ι ι ℂ} (hA : A.PosDef) (h : IsDensity A)
    (hσ : σ.PosDef) (hd : dephase σ = σ) :
    relEntropy (dephase_posDef hA).1 hσ.1 ≤ relEntropy hA.1 hσ.1 := by
  rw [relEntropy_eq_crossEntropy_sub_entropy (dephase_posDef hA) hσ (dephase_isDensity h),
    relEntropy_eq_crossEntropy_sub_entropy hA hσ h, crossEntropy_dephase hσ hd A]
  have := entropy_dephase_ge hA h
  linarith

/-- **THE LYAPUNOV THEOREM — approach to record equilibrium.**  Along the record channel,
    the relative entropy to EVERY record-diagonal equilibrium `σ` is non-increasing:
    `D(T_s A ‖ σ) ≤ D(A ‖ σ)` for `s ≥ 0`.  Proof: `T_s A` is the convex combination
    `e^{−s}A + (1−e^{−s})·dephase A`, `σ = e^{−s}σ + (1−e^{−s})σ`, and joint convexity of
    the relative entropy (the held `relEntropy_subadditive`, Carlen §6.3) + scaling +
    the dephasing DPI contract it.  At a fixed point (`dephase A = A`) the Lyapunov
    functional is stationary — the B4/E4-shaped relative-entropy stationarity whose join to
    the entanglement first law and linearized Einstein is the held
    `CodeEquilibrium.code_equilibrium_einstein` (CITED, not imported). -/
theorem relEntropy_Tsem_le {A σ : Matrix ι ι ℂ} {s : ℝ} (hs : 0 ≤ s) (hA : A.PosDef)
    (h : IsDensity A) (hσ : σ.PosDef) (hd : dephase σ = σ) :
    relEntropy (Tsem_posDef hA hs).1 hσ.1 ≤ relEntropy hA.1 hσ.1 := by
  rcases hs.eq_or_lt with hs0 | hs0
  · exact le_of_eq (relEntropy_congr _ _ _ _ (by rw [← hs0, Tsem_zero]) rfl)
  · have hDA : (dephase A).PosDef := dephase_posDef hA
    have ha : (0 : ℝ) < Real.exp (-s) := Real.exp_pos (-s)
    have hb : (0 : ℝ) < 1 - Real.exp (-s) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs0))
    have h1 : (Real.exp (-s) • A).PosDef := hA.smul ha
    have h2 : ((1 - Real.exp (-s)) • dephase A).PosDef := hDA.smul hb
    have h3 : (Real.exp (-s) • σ).PosDef := hσ.smul ha
    have h4 : ((1 - Real.exp (-s)) • σ).PosDef := hσ.smul hb
    have hsplit : Real.exp (-s) • σ + (1 - Real.exp (-s)) • σ = σ := by
      rw [← add_smul, show Real.exp (-s) + (1 - Real.exp (-s)) = 1 from by ring, one_smul]
    calc relEntropy (Tsem_posDef hA hs).1 hσ.1
        = relEntropy (h1.add h2).1 (h3.add h4).1 :=
          relEntropy_congr _ _ _ _ (by rw [Tsem]) hsplit.symm
      _ ≤ relEntropy h1.1 h3.1 + relEntropy h2.1 h4.1 :=
          relEntropy_subadditive h1 h2 h3 h4
      _ = Real.exp (-s) * relEntropy hA.1 hσ.1
            + (1 - Real.exp (-s)) * relEntropy hDA.1 hσ.1 := by
          rw [relEntropy_smul hA hσ ha h1.1 h3.1, relEntropy_smul hDA hσ hb h2.1 h4.1]
      _ ≤ Real.exp (-s) * relEntropy hA.1 hσ.1
            + (1 - Real.exp (-s)) * relEntropy hA.1 hσ.1 := by
          have hdep := relEntropy_dephase_le hA h hσ hd
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hdep hb.le)
      _ = relEntropy hA.1 hσ.1 := by ring

/-- **Entropy production along the flow**: `S(A) ≤ S(T_s A)` for `s ≥ 0` — the record
    channel never destroys entropy (Lyapunov theorem at `σ = dephase A`, plus the
    cross-entropy identity `−tr(T_s A · log dephase A) = S(dephase A)` since the channel
    never moves the readout). -/
theorem entropy_Tsem_ge {A : Matrix ι ι ℂ} {s : ℝ} (hs : 0 ≤ s) (hA : A.PosDef)
    (h : IsDensity A) :
    vonNeumannEntropy h ≤ vonNeumannEntropy (Tsem_isDensity h hs) := by
  have hDApd : (dephase A).PosDef := dephase_posDef hA
  have hDAd : IsDensity (dephase A) := dephase_isDensity h
  have hTpd : (Tsem s A).PosDef := Tsem_posDef hA hs
  have hTd : IsDensity (Tsem s A) := Tsem_isDensity h hs
  have hlya : relEntropy hTpd.1 hDApd.1 ≤ relEntropy hA.1 hDApd.1 :=
    relEntropy_Tsem_le hs hA h hDApd (dephase_dephase A)
  have h1 : relEntropy hTpd.1 hDApd.1
      = vonNeumannEntropy hDAd - vonNeumannEntropy hTd := by
    rw [relEntropy_eq_crossEntropy_sub_entropy hTpd hDApd hTd]
    congr 1
    rw [← crossEntropy_dephase hDApd (dephase_dephase A) (Tsem s A), dephase_Tsem]
    exact crossEntropy_self hDApd hDAd
  have h2 : relEntropy hA.1 hDApd.1
      = vonNeumannEntropy hDAd - vonNeumannEntropy h := by
    rw [relEntropy_eq_crossEntropy_sub_entropy hA hDApd h]
    congr 1
    rw [← crossEntropy_dephase hDApd (dephase_dephase A) A]
    exact crossEntropy_self hDApd hDAd
  linarith

/-- **The dynamics never exceeds capacity**: `S(T_s A) ≤ log N` for every density and every
    `s ≥ 0` — the held Gibbs/Jensen guard `vonNeumannEntropy_le_log_card` applied to the
    evolved state.  The record channel is capacity-respecting at all times. -/
theorem Tsem_capacity {A : Matrix ι ι ℂ} (h : IsDensity A) {s : ℝ} (hs : 0 ≤ s) :
    vonNeumannEntropy (Tsem_isDensity h hs) ≤ Real.log (Fintype.card ι) :=
  vonNeumannEntropy_le_log_card _

/-- **The maximum-entropy fixed point is capacity saturation**: the maximally mixed state is
    a record equilibrium AND its entropy is `log N` — in the code instance,
    `log N_C = Σ_e log D_e = A_τ(C)/4G`, the area-law state of the held K2a capstone
    (`entropy_saturation_eq_area`, CITED, not re-proved here). -/
theorem saturation_fixed [Nonempty ι] :
    dephase (maxMixed ι) = maxMixed ι
      ∧ vonNeumannEntropy (maxMixed_isDensity (ι := ι)) = Real.log (Fintype.card ι) :=
  ⟨dephase_maxMixed, vonNeumannEntropy_maxMixed⟩

/-! ## RC1.6 — record-relabeling equivariance (the Gate-3-safe shape) -/

/-- **The readout commutes with every record-basis relabeling** (injective substitution —
    in particular every permutation of the records). -/
theorem dephase_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℂ)
    (e : κ → ι) (he : Function.Injective e) :
    dephase (A.submatrix e e) = (dephase A).submatrix e e := by
  ext n m
  rw [Matrix.submatrix_apply]
  by_cases h : n = m
  · subst h
    rw [dephase_apply_eq, dephase_apply_eq, Matrix.submatrix_apply]
  · rw [dephase_apply_ne _ h, dephase_apply_ne _ fun hc => h (he hc)]

/-- **Record-relabeling equivariance of the channel**: `T_s` commutes with every injective
    relabeling of the record basis — the finite shape of Gate 3's
    `equivariant_enforcement_preserves_invariance` (CITED, not imported): the enforcement
    dynamics carries no preferred record label. -/
theorem Tsem_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (s : ℝ) (A : Matrix ι ι ℂ)
    (e : κ → ι) (he : Function.Injective e) :
    Tsem s (A.submatrix e e) = (Tsem s A).submatrix e e := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [Tsem_apply_eq, Matrix.submatrix_apply, Matrix.submatrix_apply, Tsem_apply_eq]
  · rw [Tsem_apply_ne s _ h, Matrix.submatrix_apply, Matrix.submatrix_apply,
      Tsem_apply_ne s A fun hc => h (he hc)]

/-- The channel commutes with every record permutation (the `Equiv.Perm` instance of the
    equivariance). -/
theorem Tsem_perm (s : ℝ) (A : Matrix ι ι ℂ) (e : Equiv.Perm ι) :
    Tsem s (A.submatrix e e) = (Tsem s A).submatrix e e :=
  Tsem_submatrix s A e e.injective

/-! ## RC1.7 — the code instance: compatibility with the held free dynamics

Instantiation on the held diamond algebra `DiamondAlg L C` of THE EMBEDDING's record code:
the record channel commutes with the held Heisenberg flow `alpha` (the phase is `1` on the
diagonal), so `T_s ∘ α_t` is a consistent Markovian family — the open dynamics EXTENDS the
free dynamics.  The held Gibbs/KMS states and record projectors are stationary, and the
Lyapunov theorem applies verbatim to the Gibbs record equilibrium. -/

section Diamond

open QIQTH.Dynamics

variable {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E) (ω : E → ℝ)

/-- The free flow never moves the record readout: `dephase ∘ α_t = dephase` (the diagonal
    phase `e^{it(E(n)−E(n))} = 1`). -/
theorem dephase_alpha (t : ℝ) (A : DiamondAlg L C) :
    dephase (alpha L C ω t A) = dephase A := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [dephase_apply_eq, dephase_apply_eq, alpha_entry, sub_self]
    simp
  · rw [dephase_apply_ne _ h, dephase_apply_ne _ h]

/-- Readout images are stationary under the free flow (the held `alpha_diagonal`). -/
theorem alpha_dephase (t : ℝ) (A : DiamondAlg L C) :
    alpha L C ω t (dephase A) = dephase A := by
  rw [dephase]
  exact alpha_diagonal L C ω t _

/-- **The record channel COMMUTES with the held free dynamics**:
    `T_s ∘ α_t = α_t ∘ T_s` — the open (record-forming) and closed (record-freezing) halves
    are compatible, giving a consistent Markovian family `T_s ∘ α_t` on the code. -/
theorem Tsem_alpha_comm (s t : ℝ) (A : DiamondAlg L C) :
    Tsem s (alpha L C ω t A) = alpha L C ω t (Tsem s A) := by
  ext n m
  by_cases h : n = m
  · subst h
    rw [Tsem_apply_eq, alpha_entry, alpha_entry, Tsem_apply_eq]
  · rw [Tsem_apply_ne s _ h, alpha_entry, alpha_entry, Tsem_apply_ne s A h]
    ring

/-- **The Gibbs/KMS state is a fixed point of the record channel** (it is record-diagonal)
    — the thermal record equilibrium of the code is stationary under record formation. -/
theorem Tsem_gibbs (s β : ℝ) : Tsem s (gibbsDensity L C ω β) = gibbsDensity L C ω β :=
  Tsem_of_dephase_eq s (by rw [gibbsDensity]; exact dephase_diagonal _)

/-- The keystone record projectors are fixed points of the record channel. -/
theorem Tsem_recordProj (s : ℝ) (R : Finset (Micro L C)) :
    Tsem s (recordProj L C R) = recordProj L C R :=
  Tsem_of_dephase_eq s (by rw [recordProj]; exact dephase_diagonal _)

/-- The Gibbs density is positive definite (explicit positive diagonal weights). -/
theorem gibbsDensity_posDef (β : ℝ) : (gibbsDensity L C ω β).PosDef := by
  rw [gibbsDensity]
  exact Matrix.posDef_diagonal_iff.mpr fun n =>
    Complex.zero_lt_real.mpr (gibbsWeight_pos L C ω β n)

/-- **RC1 CAPSTONE — Lyapunov contraction onto the thermal record equilibrium**: on the held
    code, the relative entropy of every positive density to the Gibbs/KMS state is
    non-increasing along the record channel, `D(T_s A ‖ ρ_β) ≤ D(A ‖ ρ_β)` — approach to the
    code's thermal equilibrium as a theorem (the E4 equilibrium join is CITED, not
    re-proved). -/
theorem relEntropy_Tsem_gibbs_le (β : ℝ) {s : ℝ} (hs : 0 ≤ s) {A : DiamondAlg L C}
    (hA : A.PosDef) (h : IsDensity A) :
    relEntropy (Tsem_posDef hA hs).1 (gibbsDensity_posDef L C ω β).1
      ≤ relEntropy hA.1 (gibbsDensity_posDef L C ω β).1 :=
  relEntropy_Tsem_le hs hA h (gibbsDensity_posDef L C ω β)
    (by rw [gibbsDensity]; exact dephase_diagonal _)

end Diamond

end QIQTH.RecordChannel
