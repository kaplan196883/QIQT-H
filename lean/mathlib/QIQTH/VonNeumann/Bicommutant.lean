/-
  THE CLOSURE C7 (THE_CLOSURE_PLAN.md) — THE CENTERPIECE: the von Neumann double-commutant
  theorem, in SOT-density form.

  For a unital ⋆-subalgebra A of the bounded operators on a complex Hilbert space (unitality and
  ⋆-closure ride in `StarSubalgebra` — both are load-bearing, see the C1/C3 counterexamples), the
  double centralizer A″ equals the set of operators approximable from A in norm on every finite
  tuple of vectors:

      T ∈ A″  ↔  ∀ n (ξ : Fin n → H), ∀ ε > 0, ∃ a ∈ A, ∀ i, ‖T (ξ i) − a (ξ i)‖ < ε.

  The right-hand side (`SOTApprox`) is membership in the strong-operator-topology closure of A,
  stated concretely (binding verdict: the predicate is primary; no topology type copy). The
  QUANTIFIER ORDER is load-bearing: ONE approximant `a`, uniform over the whole tuple — a per-i
  witness would be vacuous. The CONVERSE needs tuples of length 2 (`![x, S x]`): approximability
  at single vectors alone does NOT put T in A″, because the commutation estimate against S ∈ A′
  requires the approximant to be good at `S x` simultaneously with `x`.

  Forward = C6 (amplified density); converse = the `![x, S x]` estimate
  `‖(TS − ST)x‖ ≤ ‖(T−a)(Sx)‖ + ‖S‖·‖(a−T)x‖`. Nothing here mentions the weak operator
  topology — no theorem in this file claims a WOT closure (C10, separately named, if it ships).
-/
import Mathlib
import QIQTH.VonNeumann.GeneratedBy
import QIQTH.VonNeumann.DensityN

namespace QIQTH.VonNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Strong-operator approximability** — membership in the SOT closure of `A`, concretely: one
    element of `A` approximates `T` in norm on every finite tuple of vectors. The single `a`
    uniform over the tuple is load-bearing. -/
def SOTApprox (A : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) : Prop :=
  ∀ (n : ℕ) (ξ : Fin n → H), ∀ ε > 0, ∃ a ∈ A, ∀ i, ‖T (ξ i) - a (ξ i)‖ < ε

theorem SOTApprox.mono {A B : Set (H →L[ℂ] H)} (hAB : A ⊆ B) {T : H →L[ℂ] H}
    (hT : SOTApprox A T) : SOTApprox B T := fun n ξ ε hε =>
  let ⟨a, ha, h⟩ := hT n ξ ε hε
  ⟨a, hAB ha, h⟩

theorem sotApprox_self {A : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} (hT : T ∈ A) :
    SOTApprox A T := fun _ ξ ε hε =>
  ⟨T, hT, fun i => by simpa using hε⟩

/-- **THE VON NEUMANN DOUBLE-COMMUTANT THEOREM (iff form)**: membership in the double
    centralizer is exactly strong-operator approximability from the algebra. -/
theorem mem_centralizer_centralizer_iff_sotApprox (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))
      ↔ SOTApprox (A : Set (H →L[ℂ] H)) T := by
  constructor
  · intro hT n ξ ε hε
    exact bicommutant_sotApprox hT n ξ hε
  · intro hT S hS
    refine ContinuousLinearMap.ext fun x => ?_
    have key : ∀ ε > (0 : ℝ), ‖S (T x) - T (S x)‖ < ε := by
      intro ε hε
      set δ : ℝ := ε / (‖S‖ + 1) with hδdef
      have hSpos : (0 : ℝ) < ‖S‖ + 1 := by positivity
      have hδ : 0 < δ := div_pos hε hSpos
      obtain ⟨a, ha, hclose⟩ := hT 2 ![x, S x] δ hδ
      have h0 : ‖T x - a x‖ < δ := by simpa using hclose 0
      have h1 : ‖T (S x) - a (S x)‖ < δ := by simpa using hclose 1
      have hcommSa : S (a x) = a (S x) := by
        have := hS a ha
        have happ := congrArg (fun (F : H →L[ℂ] H) => F x) this
        simpa only [ContinuousLinearMap.mul_apply] using happ.symm
      have hsplit : S (T x) - T (S x)
          = S (T x - a x) + (a (S x) - T (S x)) := by
        rw [map_sub, hcommSa]
        abel
      calc ‖S (T x) - T (S x)‖
          = ‖S (T x - a x) + (a (S x) - T (S x))‖ := by rw [hsplit]
        _ ≤ ‖S (T x - a x)‖ + ‖a (S x) - T (S x)‖ := norm_add_le _ _
        _ ≤ ‖S‖ * ‖T x - a x‖ + ‖a (S x) - T (S x)‖ := by
            have := S.le_opNorm (T x - a x)
            gcongr
        _ < ‖S‖ * δ + δ := by
            rw [norm_sub_rev] at h1
            have hS0 : (0 : ℝ) ≤ ‖S‖ := norm_nonneg S
            nlinarith
        _ ≤ ε := by
            rw [hδdef]
            rw [show ‖S‖ * (ε / (‖S‖ + 1)) + ε / (‖S‖ + 1)
                = (‖S‖ + 1) * (ε / (‖S‖ + 1)) from by ring]
            rw [mul_div_cancel₀ _ hSpos.ne']
    have hzero : ‖S (T x) - T (S x)‖ ≤ 0 := by
      by_contra h
      push_neg at h
      exact absurd (key _ h) (lt_irrefl _)
    have := norm_le_zero_iff.mp hzero
    have hdiff : S (T x) = T (S x) := by
      have := sub_eq_zero.mp this
      exact this
    show S (T x) = T (S x)
    exact hdiff

/-- The set form: `A″` IS the SOT closure of `A`, concretely. -/
theorem centralizer_centralizer_eq_setOf_sotApprox (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))
      = {T | SOTApprox (A : Set (H →L[ℂ] H)) T} :=
  Set.ext fun T => mem_centralizer_centralizer_iff_sotApprox A T

/-- **The von Neumann double-commutant theorem** (headline alias of the set form). -/
theorem vonNeumann_double_commutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))
      = {T | SOTApprox (A : Set (H →L[ℂ] H)) T} :=
  centralizer_centralizer_eq_setOf_sotApprox A

/-- **Idempotence**: approximability from the bicommutant is no stronger than approximability
    from the algebra (a "closure" behaves like a closure). -/
theorem sotApprox_bicommutant_iff (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    SOTApprox (Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) T
      ↔ SOTApprox (A : Set (H →L[ℂ] H)) T := by
  constructor
  · intro hT n ξ ε hε
    obtain ⟨b, hb, hbclose⟩ := hT n ξ (ε / 2) (by positivity)
    obtain ⟨a, ha, haclose⟩ :=
      (mem_centralizer_centralizer_iff_sotApprox A b).mp hb n ξ (ε / 2) (by positivity)
    refine ⟨a, ha, fun i => ?_⟩
    calc ‖T (ξ i) - a (ξ i)‖
        ≤ ‖T (ξ i) - b (ξ i)‖ + ‖b (ξ i) - a (ξ i)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hbclose i) (haclose i)
      _ = ε := add_halves ε
  · intro hT
    exact hT.mono Set.subset_centralizer_centralizer

/-- **The generated von Neumann algebra IS the SOT closure of the generated ⋆-algebra**:
    C2's naming layer meets the density theorem. -/
theorem generatedBy_carrier_eq (S : Set (H →L[ℂ] H)) :
    (generatedBy S : Set (H →L[ℂ] H))
      = {T | SOTApprox ((StarAlgebra.adjoin ℂ S : StarSubalgebra ℂ (H →L[ℂ] H))
          : Set (H →L[ℂ] H)) T} := by
  rw [generatedBy_coe, ← centralizer_adjoin,
    centralizer_centralizer_eq_setOf_sotApprox]

end QIQTH.VonNeumann
