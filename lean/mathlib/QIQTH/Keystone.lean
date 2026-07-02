/-
  K0 (KEYSTONE_PLAN.md) — the finite trace-entropy lemmas for THE COUNT.

  The entropy substrate the count capstones stand on (unnormalized counting trace — the binding
  correction: τ(1) = N, never normalized):
  • `maxMixed` — the maximally mixed density `N⁻¹·1` with `maxMixed_isDensity`;
  • `maxMixed_eigenvalues` — every spectral eigenvalue is `N⁻¹` (scalar matrices via the
    eigenvector-basis relation);
  • **`vonNeumannEntropy_maxMixed`** — `S(maxMixed) = log N`: the maximal-entropy state's entropy IS the
    log of the (unnormalized-trace) dimension — the entropy half of the count;
  • **`vonNeumannEntropy_le_log_card`** — the Gibbs/Jensen guard `S(ρ) ≤ log N` for EVERY density
    (riding the held classical `shannon_le_log_card` on the eigenvalue vector): the count equality is
    claimed only where it holds — at maximal mixing. (The strict-concavity uniqueness refinement is the
    standard textbook addendum, not needed by K2.)
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.QuantumRelativeEntropy
import QIQTH.RecordContract
import QIQTH.MonomialTrace
import QIQTH.Entropy.TraceConvexity

namespace QIQTH.Keystone

open QIQTH.QuantumEntropy
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximally mixed density `N⁻¹·1` (w.r.t. the UNNORMALIZED counting trace). -/
noncomputable def maxMixed (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ • 1

theorem maxMixed_isDensity [Nonempty ι] : IsDensity (maxMixed ι) where
  posSemidef := by
    rw [maxMixed, show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) from by
      push_cast
      rfl]
    have h1 : (Matrix.PosSemidef (1 : Matrix ι ι ℂ)) := Matrix.PosSemidef.one
    have hc : (0 : ℂ) ≤ (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.zero_le_real]
      positivity
    exact h1.smul hc
  trace_one := by
    rw [maxMixed, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    have hc : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- Every eigenvalue of the maximally mixed density is `N⁻¹` (a scalar matrix has constant
    spectrum — via the eigenvector-basis relation). -/
theorem maxMixed_eigenvalues [Nonempty ι] (j : ι) :
    (maxMixed_isDensity (ι := ι)).eigenvalues j = ((Fintype.card ι : ℝ))⁻¹ := by
  have hH := (maxMixed_isDensity (ι := ι)).posSemidef.1
  have h := hH.mulVec_eigenvectorBasis j
  have hlhs : (maxMixed ι).mulVec (hH.eigenvectorBasis j).ofLp
      = ((Fintype.card ι : ℂ))⁻¹ • (hH.eigenvectorBasis j).ofLp := by
    simp only [maxMixed, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hlhs] at h
  have hreal : hH.eigenvalues j • (hH.eigenvectorBasis j).ofLp
      = ((hH.eigenvalues j : ℝ) : ℂ) • (hH.eigenvectorBasis j).ofLp := by
    funext i
    simp [Complex.real_smul]
  rw [hreal] at h
  have hvne : hH.eigenvectorBasis j ≠ 0 := hH.eigenvectorBasis.orthonormal.ne_zero j
  have hv : (hH.eigenvectorBasis j).ofLp ≠ 0 := by
    intro h0
    apply hvne
    ext i
    exact congrFun h0 i
  have hsub : (((Fintype.card ι : ℂ))⁻¹ - ((hH.eigenvalues j : ℝ) : ℂ))
      • (hH.eigenvectorBasis j).ofLp = 0 := by
    rw [sub_smul, h]
    simp
  rcases smul_eq_zero.mp hsub with hc | hzero
  · have hceq : ((Fintype.card ι : ℂ))⁻¹ = ((hH.eigenvalues j : ℝ) : ℂ) :=
      sub_eq_zero.mp hc
    have hcast : ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = ((hH.eigenvalues j : ℝ) : ℂ) := by
      rw [← hceq]
      push_cast
      rfl
    exact (Complex.ofReal_inj.mp hcast).symm
  · exact absurd hzero hv

/-- **K0 CAPSTONE (entropy value) — `S(maxMixed) = log N`:** the maximally mixed state's entropy is
    the log of the unnormalized-trace dimension — the entropy half of the count. -/
theorem vonNeumannEntropy_maxMixed [Nonempty ι] :
    vonNeumannEntropy (maxMixed_isDensity (ι := ι)) = Real.log (Fintype.card ι) := by
  rw [vonNeumannEntropy,
    Finset.sum_congr rfl fun j _ => by rw [maxMixed_eigenvalues],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [Real.negMulLog_def, Real.log_inv]
  field_simp

/-- **K0 CAPSTONE (the guard) — the Gibbs/Jensen bound `S(ρ) ≤ log N` for EVERY density** (riding the
    held classical bound on the eigenvalue vector): the count equality is claimed only at maximal
    mixing. -/
theorem vonNeumannEntropy_le_log_card {ρ : Matrix ι ι ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ Real.log (Fintype.card ι) := by
  have hb := QIQTH.RecordContract.shannon_le_log_card h.eigenvalues
    h.eigenvalues_nonneg h.sum_eigenvalues
  rwa [QIQTH.RecordContract.shannon_eq_sum_negMulLog] at hb

/-! ## K2a — the standalone finite count

The screen's diamond algebra with the UNNORMALIZED counting trace; the weight is TRACE-DEFINED
(`wEntτ e = log D_e` where `D_e` is the trace of the link projection — per the binding correction, an
EXTERNAL weight matching `log D_e` is the old calibration and is stated only as the honest iff). -/

/-- Link dimensions (positive). -/
structure LinkDims (E : Type*) where
  /-- the dimension of each link fiber -/
  D : E → ℕ
  /-- positivity -/
  hD : ∀ e, 0 < D e

variable {E : Type*} [DecidableEq E]

/-- The screen microstates over a cut: one `Fin (D e)` record fiber per link. -/
abbrev Micro (L : LinkDims E) (C : Finset E) : Type _ := (e : C) → Fin (L.D e.val)

instance microNonempty (L : LinkDims E) (C : Finset E) : Nonempty (Micro L C) :=
  ⟨fun e => ⟨0, L.hD e.val⟩⟩

/-- The microstate count `N_C = Π_{e∈C} D_e`. -/
noncomputable def NC (L : LinkDims E) (C : Finset E) : ℕ := ∏ e ∈ C, L.D e

theorem card_micro (L : LinkDims E) (C : Finset E) :
    Fintype.card (Micro L C) = NC L C := by
  rw [NC, Fintype.card_pi, ← Finset.prod_coe_sort C (fun e => L.D e)]
  exact Finset.prod_congr rfl fun e _ => Fintype.card_fin _

theorem NC_pos (L : LinkDims E) (C : Finset E) : 0 < NC L C :=
  Finset.prod_pos fun e _ => L.hD e

/-- The diamond algebra of the cut: the full matrix algebra on the microstates. -/
abbrev DiamondAlg (L : LinkDims E) (C : Finset E) : Type _ :=
  Matrix (Micro L C) (Micro L C) ℂ

/-- **The UNNORMALIZED counting trace** (`τ(1) = N_C` — the binding correction; a normalized trace
    kills the count). -/
noncomputable def tauCount (L : LinkDims E) (C : Finset E) (x : DiamondAlg L C) : ℂ :=
  Matrix.trace x

/-- The record projection onto a set of microstates. -/
noncomputable def recordProj (L : LinkDims E) (C : Finset E) (R : Finset (Micro L C)) :
    DiamondAlg L C :=
  Matrix.diagonal fun m => if m ∈ R then 1 else 0

/-- `τ(P_R) = |R|` — the trace COUNTS the records. -/
theorem tau_recordProj (L : LinkDims E) (C : Finset E) (R : Finset (Micro L C)) :
    tauCount L C (recordProj L C R) = (R.card : ℂ) := by
  rw [tauCount, recordProj, Matrix.trace_diagonal]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `τ(1) = N_C` — the top projection counts everything. -/
theorem tau_top (L : LinkDims E) (C : Finset E) :
    tauCount L C (1 : DiamondAlg L C) = (NC L C : ℂ) := by
  rw [tauCount, Matrix.trace_one, card_micro]

/-- **The TRACE-DEFINED link weight** `wEntτ e := log D_e` (`D_e` is the τ-dimension of the link
    fiber — the weight comes FROM the trace, never from an external geometric assignment). -/
noncomputable def wEntTau (L : LinkDims E) (e : E) : ℝ := Real.log (L.D e)

/-- The trace-defined cut weight. -/
noncomputable def cutTau (L : LinkDims E) (C : Finset E) : ℝ := ∑ e ∈ C, wEntTau L e

/-- The trace-induced screen area (G enters ONLY as the normalization — never derived). -/
noncomputable def inducedScreenAreaTau (L : LinkDims E) (G : ℝ) (C : Finset E) : ℝ :=
  (4 * G) * cutTau L C

theorem log_NC_eq_cutTau (L : LinkDims E) (C : Finset E) :
    Real.log (NC L C) = cutTau L C := by
  rw [NC, cutTau]
  push_cast
  rw [Real.log_prod]
  · rfl
  · intro e _
    exact_mod_cast (L.hD e).ne'

/-- **K2a CAPSTONE — THE COUNT (standalone finite form):** the maximal entropy of the diamond algebra
    w.r.t. the unnormalized counting trace equals the trace-induced screen area over `4G` —
    `S(maxMixed) = log N_C = Σ_e log D_e = A_τ(C)/4G`, with `G` entering only through the
    normalization. Combined with K0's guard, the equality holds exactly at maximal mixing. -/
theorem K2a_count_capstone (L : LinkDims E) (C : Finset E) {G : ℝ} (hG : G ≠ 0) :
    vonNeumannEntropy (maxMixed_isDensity (ι := Micro L C))
      = inducedScreenAreaTau L G C / (4 * G) := by
  rw [vonNeumannEntropy_maxMixed, card_micro, log_NC_eq_cutTau, inducedScreenAreaTau]
  field_simp

/-- **The honest external-weight statement (the binding correction):** the trace-defined cut matches
    an EXTERNAL weight assignment iff the external weights sum to the log-dimensions — i.e., pointwise
    matching IS the old calibration hypothesis. It is stated, not deleted. -/
theorem count_matches_external_weights_iff (L : LinkDims E) (C : Finset E) (wExt : E → ℝ) :
    cutTau L C = ∑ e ∈ C, wExt e ↔ ∑ e ∈ C, Real.log (L.D e) = ∑ e ∈ C, wExt e :=
  Iff.rfl

/-! ## K2b — THE COUNT IN THE HELD CORE: the counting trace is the VALUE of the constructed τ₀

The held W3a monomial trace `τ₀(π(a)λ_t f(L)) = ω(a)·Iexp(f.modMul t)`, evaluated at `t = 0`, the
uniform matter state `Tr/N_C`, and a clock test of `Iexp`-mass `N_C`, IS the unnormalized counting
trace — the count is the restriction of the constructed crossed-product trace, not a new postulate.
(The `1_{(−∞, log N]}` indicator idealization has noncompact support; the held `ExpTest` structure
requires compact support, so the mass-`N_C` clock is realized as the flat window `N·e^{−x}·1_{[0,1]}` —
identical `Iexp` mass, honest substitution.) -/

open QIQTH.TypeIITrace QIQTH.Spectral.Multiplication

/-- **The flat clock window of mass `N`**: `f(x) = N·e^{−x}` on `[0,1]` — a genuine `ExpTest` whose
    log-clock weight is EXACTLY `N` (`e^x · N e^{−x} = N` on the window). -/
noncomputable def flatClock (N : ℝ) : ExpTest where
  f := fun x => if x ∈ Set.Icc (0 : ℝ) 1 then ((N * Real.exp (-x) : ℝ) : ℂ) else 0
  meas := by
    refine Measurable.ite measurableSet_Icc ?_ measurable_const
    exact Complex.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp measurable_neg))
  bound := |N|
  hbound := fun x => by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos hx, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1)
      have h2 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
      nlinarith [abs_nonneg N]
    · rw [if_neg hx]
      simp
  rad := 1
  hsupp := fun x hx => by
    rw [if_neg]
    intro hmem
    exact hx ⟨by linarith [hmem.1], hmem.2⟩

/-- The flat window's log-clock weight is exactly its mass. -/
theorem Iexp_flatClock (N : ℝ) : Iexp (flatClock N) = (N : ℂ) := by
  rw [Iexp]
  rw [show (fun x => (Real.exp x : ℂ) * (flatClock N).f x)
      = Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (N : ℂ)) from ?_]
  · rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc]
    simp [Real.volume_Icc]
  · funext x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [if_pos hx, show (flatClock N).f x = ((N * Real.exp (-x) : ℝ) : ℂ) from if_pos hx]
      push_cast
      rw [show Complex.exp (x : ℂ) * ((N : ℂ) * Complex.exp (-(x : ℂ)))
          = (N : ℂ) * (Complex.exp (x : ℂ) * Complex.exp (-(x : ℂ))) from by ring,
        ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    · rw [if_neg hx, show (flatClock N).f x = 0 from if_neg hx, mul_zero]

/-- The uniform matter state `Tr/N_C` on the diamond algebra. -/
noncomputable def uniformState (L : LinkDims E) (C : Finset E) (x : DiamondAlg L C) : ℂ :=
  Matrix.trace x / (NC L C : ℂ)

/-- **K2b — THE COUNTING TRACE IS THE VALUE OF THE CONSTRUCTED τ₀:** the held monomial trace at the
    uniform matter state, `t = 0`, and the mass-`N_C` clock window equals the unnormalized counting
    trace — `τ₀(π(x)·q_{N_C}(L)) = Tr x`. The count is a RESTRICTION of the crossed-product trace,
    not a new postulate. -/
theorem tauMonomial_uniform_eq_tauCount (L : LinkDims E) (C : Finset E) (x : DiamondAlg L C) :
    tauMonomial (uniformState L C) x 0 (flatClock (NC L C)) = tauCount L C x := by
  rw [tauMonomial]
  have hmod : Iexp ((flatClock (NC L C)).modMul 0) = Iexp (flatClock (NC L C)) := by
    rw [Iexp, Iexp]
    congr 1
    funext y
    rw [show ((flatClock (NC L C)).modMul 0).f y
        = modSymbol 0 y * (flatClock (NC L C)).f y from rfl]
    rw [show modSymbol 0 y = 1 from by simp [modSymbol]]
    rw [one_mul]
  rw [hmod, Iexp_flatClock, uniformState, tauCount]
  have hN : (NC L C : ℂ) ≠ 0 := by
    exact_mod_cast (NC_pos L C).ne'
  field_simp
  norm_cast

/-- The record count through τ₀: `τ₀(π(P_R)·q_{N_C}(L)) = |R|`. -/
theorem tau0_recordProj_eq_card (L : LinkDims E) (C : Finset E) (R : Finset (Micro L C)) :
    tauMonomial (uniformState L C) (recordProj L C R) 0 (flatClock (NC L C)) = (R.card : ℂ) := by
  rw [tauMonomial_uniform_eq_tauCount, tau_recordProj]

/-- The τ₀-dimension of the full diamond is `N_C`. -/
theorem tau0_top_eq_NC (L : LinkDims E) (C : Finset E) :
    tauMonomial (uniformState L C) (1 : DiamondAlg L C) 0 (flatClock (NC L C))
      = (NC L C : ℂ) := by
  rw [tauMonomial_uniform_eq_tauCount, tau_top]

/-- **THE CALIBRATION IS A THEOREM (trace-defined):** the link weight IS the log of the link fiber's
    τ₀-dimension — `wEntTau e = log dim_{τ₀}(single-link diamond)`. Nothing is calibrated; the weight
    comes from the trace. -/
theorem wEntTau_eq_log_tau0Dim (L : LinkDims E) (e : E) :
    wEntTau L e
      = Real.log ((tauMonomial (uniformState L {e}) (1 : DiamondAlg L {e}) 0
          (flatClock (NC L {e}))).re) := by
  rw [tau0_top_eq_NC, wEntTau]
  norm_num [NC, Finset.prod_singleton]

/-- **K2b CAPSTONE — THE COUNT IN THE HELD CORE:** the maximal entropy of the diamond record corner
    equals the log of its τ₀-dimension, equals the trace-induced screen area over `4G` —
    `S = log dim_{τ₀}(𝒟_C) = A_τ(C)/4G`, in the finite record corner of the constructed crossed-product
    core, with the calibration trace-defined and `G` entering only as the normalization. -/
theorem K2b_tau0_capstone (L : LinkDims E) (C : Finset E) {G : ℝ} (hG : G ≠ 0) :
    vonNeumannEntropy (maxMixed_isDensity (ι := Micro L C))
      = Real.log ((tauMonomial (uniformState L C) (1 : DiamondAlg L C) 0
          (flatClock (NC L C))).re)
    ∧ vonNeumannEntropy (maxMixed_isDensity (ι := Micro L C))
      = inducedScreenAreaTau L G C / (4 * G) := by
  constructor
  · rw [tau0_top_eq_NC, vonNeumannEntropy_maxMixed, card_micro]
    norm_num
  · exact K2a_count_capstone L C hG

/-! ## K5 — the covariance checks

Per the binding correction: trace-PRESERVING (code/Lorentz) unitaries leave the count INVARIANT;
the dual action SCALES it — `S(θ_s·) = S(·) − s` (covariance with transported area, never naive
invariance). -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary conjugation preserves densities. -/
theorem isDensity_conj {ρ : Matrix ι ι ℂ} (h : IsDensity ρ) {V : Matrix ι ι ℂ}
    (hVr : V * star V = 1) : IsDensity (star V * ρ * V) where
  posSemidef := by
    have := h.posSemidef.conjTranspose_mul_mul_same (B := V)
    simpa [Matrix.star_eq_conjTranspose] using this
  trace_one := by
    rw [Matrix.trace_mul_cycle, hVr, Matrix.one_mul, h.trace_one]

/-- **Trace-preserving unitaries preserve the count's entropy** (Gate-3's finite instantiation —
    riding the held general-`f` eigenvalue conjugation invariance). -/
theorem vonNeumannEntropy_unitary_conj {ρ : Matrix ι ι ℂ} (h : IsDensity ρ)
    {V : Matrix ι ι ℂ} (hVl : star V * V = 1) (hVr : V * star V = 1)
    (h' : IsDensity (star V * ρ * V)) :
    vonNeumannEntropy h' = vonNeumannEntropy h := by
  rw [vonNeumannEntropy, vonNeumannEntropy]
  exact QIQTH.Entropy.eigenvalues_sum_conj_invariant h.posSemidef.1 hVl hVr h'.posSemidef.1
    Real.negMulLog

/-- **Code unitaries preserve the counting trace.** -/
theorem tauCount_conj {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E)
    (x V : DiamondAlg L C) (hVr : V * star V = 1) :
    tauCount L C (star V * x * V) = tauCount L C x := by
  rw [tauCount, tauCount, Matrix.trace_mul_cycle, hVr, Matrix.one_mul]

/-- **The dual action SCALES the τ₀-count exactly** (`t = 0` of the held W3a dual-scaling law):
    `τ₀(θ_s-shifted corner) = e^{−s}·N_C`. -/
theorem tau0_dual_scaled {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E) (s : ℝ) :
    tauMonomial (uniformState L C) (1 : DiamondAlg L C) 0
        ((flatClock (NC L C)).dualShift s)
      = (Real.exp (-s) : ℂ) * (NC L C : ℂ) := by
  have h := tauMonomial_dual (uniformState L C) (1 : DiamondAlg L C) s 0 (flatClock (NC L C))
  rw [show ((0 : ℝ) * s) = (0 : ℝ) from by ring] at h
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at h
  rw [h, tau0_top_eq_NC]

/-- **K5 CAPSTONE — the count transforms covariantly under the dual action:**
    `S(θ_s·) = S(·) − s` at the count level (`S = log dim_τ₀` for the maximal corner) — the honest
    dual-covariance law with TRANSPORTED area, per the binding correction (never naive invariance). -/
theorem K5_dual_covariant_count {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E)
    (s : ℝ) :
    Real.log ((tauMonomial (uniformState L C) (1 : DiamondAlg L C) 0
        ((flatClock (NC L C)).dualShift s)).re)
      = Real.log ((tauMonomial (uniformState L C) (1 : DiamondAlg L C) 0
          (flatClock (NC L C))).re) - s := by
  rw [tau0_dual_scaled, tau0_top_eq_NC]
  have hre : ((Real.exp (-s) : ℂ) * (NC L C : ℂ)).re = Real.exp (-s) * (NC L C : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  have hN : (0 : ℝ) < (NC L C : ℝ) := by
    exact_mod_cast NC_pos L C
  rw [show ((NC L C : ℂ)).re = (NC L C : ℝ) from by
      rw [← Complex.ofReal_natCast, Complex.ofReal_re],
    Real.log_mul (Real.exp_ne_zero _) hN.ne', Real.log_exp]
  ring

/-! ## K3 — finite closure hygiene

The counting trace is bounded on the finite corner (norm-closure extension trivial in finite dimension);
and the K3 audit STRENGTHENED the carried `DualWeightTraceExtension` interface: its previous shape (no
embedding multiplicativity) was satisfiable by an abelian collapse witness for ANY algebra — a vacuous
interface, now fixed in `TraceCapacityFromCore` (the vN extension itself remains Wall 3, carried). -/

/-- The counting trace is bounded on the finite corner (by the diagonal norm sum — finite). -/
theorem tauCount_norm_le_sum_diag {E : Type*} [DecidableEq E] (L : LinkDims E) (C : Finset E)
    (x : DiamondAlg L C) : ‖tauCount L C x‖ ≤ ∑ m, ‖x m m‖ := by
  rw [tauCount, Matrix.trace]
  exact norm_sum_le _ _

end QIQTH.Keystone
