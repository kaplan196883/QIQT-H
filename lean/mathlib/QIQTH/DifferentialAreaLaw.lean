import QIQTH.RecordContract
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The differential area law `δS = η δA`, DERIVED (not assumed) from a saturated capacity bound

`jacobson_einstein_from_area_law` (the QIQT-H ⇒ GR chain) currently takes the differential area law
`δS = η δA` as a bare hypothesis (`hAreaLaw`).  This file removes that assumption: it *derives* the
first-variation relation `δS = η δA` from inputs QIQT-H genuinely supplies, plus the entanglement first
law — **without ever assuming the equality `S = ηA`**.

The mechanism (GPT-5-pro's architecture, honest by construction):

* QIQT-H proves the capacity **BOUND** `S ≤ η·A` (this is `RecordContract.shannon_le_log_card`, the
  Gibbs/Jensen bound `H(R) ≤ log|R|`, with the holographic capacity `log|R| = η·A`).  This is a
  *theorem*, not an assumption.
* At the equilibrium / maximally-mixed reference the bound is **saturated**: `S 0 = η·A 0`
  (`RecordContract.shannon_uniform_eq_log_card`).
* `deriv_eq_of_le_of_eq`: a bound saturated at a point forces the *first variations* to agree —
  `δS = δ(ηA)` — even though `S ≠ ηA` away from the reference.  (Pure calculus: `0` is a local max of
  `S − ηA`, so the derivative of `S − ηA` vanishes there.)
* The entanglement first law `δS = δ⟨K⟩` (`IsLocalMin (KE − S) 0`, i.e. relative entropy ≥ 0 with
  equality at the reference) then gives `δ⟨K⟩ = η δA` as well.

CRUCIALLY (anti-circularity): no hypothesis below is `S = ηA` or `δS = η δA`.  The inputs are the
*inequality* `S ≤ ηA` (QIQT-H's bound), saturation *only at the point* `S 0 = ηA 0`, and the first law.
Together they ENTAIL `δS = η δA` — they do not presuppose it.
-/

namespace QIQTH.DifferentialAreaLaw

open Filter Topology

/-- **First-order saturation ⇒ equal first variations.**  If `f ≤ g` on a neighbourhood of `0` and
    `f 0 = g 0`, then `0` is a local maximum of `f − g`, so the derivatives agree: `f' = g'`.  This is
    the engine that converts a *bound* saturated at the reference into an *equality of first variations*,
    without assuming `f = g`. -/
theorem deriv_eq_of_le_of_eq {f g : ℝ → ℝ} {f' g' : ℝ}
    (hf : HasDerivAt f f' 0) (hg : HasDerivAt g g' 0)
    (hle : ∀ᶠ t in 𝓝 0, f t ≤ g t) (h0 : f 0 = g 0) :
    f' = g' := by
  have hmax : IsLocalMax (fun t => f t - g t) 0 := by
    filter_upwards [hle] with t ht
    show f t - g t ≤ f 0 - g 0
    have : f 0 - g 0 = 0 := by rw [h0, sub_self]
    linarith
  have hsub : HasDerivAt (fun t => f t - g t) (f' - g') 0 := hf.sub hg
  have hz : f' - g' = 0 := hmax.hasDerivAt_eq_zero hsub
  linarith

/-- **★ THE DIFFERENTIAL AREA LAW, DERIVED.**  Along a one-parameter deformation `t`, with `S` the
    horizon entropy, `KE` the modular energy `⟨K⟩`, `A` the area, and a constant `η`:

    HYPOTHESES (note: NONE asserts `S = ηA` or `δS = ηδA`):
    * `hbound` — the capacity **bound** `S ≤ η·A` near `0` (QIQT-H's `shannon_le_log_card`);
    * `hsat`   — **saturation at the reference** `S 0 = η·A 0` (equilibrium, `shannon_uniform_eq_log_card`);
    * `hfl`    — the **entanglement first law** datum: `KE − S` has a local minimum at `0` (relative
      entropy `≥ 0`, `= 0` at the reference);
    * differentiability of `S, KE, A` at `0`.

    CONCLUSION: `δS = η δA` **and** `δ⟨K⟩ = η δA` — the differential area law, derived. -/
theorem differential_area_law {S KE A : ℝ → ℝ} {s' k' a' η : ℝ}
    (hS : HasDerivAt S s' 0) (hK : HasDerivAt KE k' 0) (hA : HasDerivAt A a' 0)
    (hbound : ∀ᶠ t in 𝓝 0, S t ≤ η * A t) (hsat : S 0 = η * A 0)
    (hfl : IsLocalMin (fun t => KE t - S t) 0) :
    s' = η * a' ∧ k' = η * a' := by
  have hSarea : HasDerivAt (fun t => η * A t) (η * a') 0 := hA.const_mul η
  have h1 : s' = η * a' := deriv_eq_of_le_of_eq hS hSarea hbound hsat
  have hsub : HasDerivAt (fun t => KE t - S t) (k' - s') 0 := hK.sub hS
  have hz : k' - s' = 0 := hfl.hasDerivAt_eq_zero hsub
  exact ⟨h1, by linarith⟩

/-- **The differential area law from RELATIVE-ENTROPY POSITIVITY** — grounding the first-law datum `hfl`
    in QIQT-H's own theorem.  The entanglement first law's premise (`IsLocalMin (KE − S) 0`) is not an
    extra assumption: it is exactly *relative-entropy non-negativity with equality at the reference*,
    `D = KE − S ≥ 0` and `D 0 = 0` — which QIQT-H proves as `QuantumEntropy.relEntropy_nonneg` (Klein's
    inequality) and `relEntropy_self`.  So the inputs reduce to: the capacity bound `S ≤ η·A` (QIQT's
    `shannon_le_log_card`), saturation at the reference, relative-entropy positivity (Klein), and
    differentiability — and these DERIVE `δS = η δA` and `δ⟨K⟩ = η δA`. -/
theorem differential_area_law_of_relEntropy {S KE A : ℝ → ℝ} {s' k' a' η : ℝ}
    (hS : HasDerivAt S s' 0) (hK : HasDerivAt KE k' 0) (hA : HasDerivAt A a' 0)
    (hbound : ∀ᶠ t in 𝓝 0, S t ≤ η * A t) (hsat : S 0 = η * A 0)
    (hDnn : ∀ t, 0 ≤ KE t - S t) (hD0 : KE 0 - S 0 = 0) :
    s' = η * a' ∧ k' = η * a' := by
  have hfl : IsLocalMin (fun t => KE t - S t) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    show KE 0 - S 0 ≤ KE t - S t
    rw [hD0]; exact hDnn t
  exact differential_area_law hS hK hA hbound hsat hfl

end QIQTH.DifferentialAreaLaw
