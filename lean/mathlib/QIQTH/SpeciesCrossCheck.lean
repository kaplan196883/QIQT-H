/-
  A3 — the mixed-species Sakharov consistency chain over ONE shared species datum (Track A capstone).

  ★ WHAT THIS IS (honest scope). A **consistency chain over one shared cited datum — NOT an
  independent cross-check**. A single `SpeciesContent` datum `S` (the mixed field content: scalars,
  Weyl fermions, gauge vectors, with their per-species coefficients) feeds BOTH bookkeepings:

    • the one-loop entanglement entropy across an area `A` at cutoff `Λ`,
        `S_ent(S, A, Λ) = A · (Σᵢ nᵢ cᵢ)/(48π) · Λ²`   (`speciesEntropy`), and
    • the induced inverse Newton constant,
        `1/G_ind(S, Λ) = (Σᵢ nᵢ cᵢ)/(12π) · Λ²`        (`InducedG.inducedInvG`),

  and the theorems below check that the ENTIRE species sum `Σᵢ nᵢ cᵢ` cancels between them:
  the ratio is the Sakharov `1/4` (`species_sakharov_ratio`), equivalently `S_ent = A/4G_ind`
  (`speciesEntropy_eq_capacity`) — for ANY mixed field content, not just the single-scalar case of
  `SakharovRatio.sakharov_ratio`.

  ⚠ The `c_i` are **cited one-loop Seeley–DeWitt heat-kernel coefficients** (Susskind–Uglum /
  Solodukhin normalization: entropy density `1/48π`, induced `1/G` density `1/12π` per unit
  coefficient), **hand-entered** as data on `SpeciesContent`. There is NO claim that either side is
  independently computed, and NO claim that `G` is derived numerically — the chain certifies that the
  one shared cited datum is wired coherently through both bookkeepings.
-/
import QIQTH.HolographicBridge

namespace QIQTH.InducedG

open Real

/-- **The one-loop entanglement entropy of a mixed field content** across an area `A` at UV cutoff
    `Λ`: `S_ent = A · (n_s c_s + n_f c_f + n_v c_v)/(48π) · Λ²` — the raw species sum in the CITED
    Susskind–Uglum/Solodukhin `1/48π` entropy-density normalization (the same shared species datum
    that feeds `inducedInvG` in its `1/12π` normalization). The `c_i` are hand-entered cited
    heat-kernel data, NOT derived. -/
noncomputable def speciesEntropy (S : SpeciesContent) (A Λ : ℝ) : ℝ :=
  A * ((S.nScalar * S.cScalar + S.nWeyl * S.cWeyl + S.nVector * S.cVector) / (48 * π)) * Λ ^ 2

/-- `speciesEntropy` in terms of the shared effective species number: `S_ent = A · N_eff · Λ²/4` —
    the `1/48π = (1/12π)/4` bookkeeping made explicit (this factor-4 relation IS the Sakharov ratio
    in disguise). -/
theorem speciesEntropy_eq_effSpeciesN_form (S : SpeciesContent) (A Λ : ℝ) :
    speciesEntropy S A Λ = A * effSpeciesN S * Λ ^ 2 / 4 := by
  have hπ := Real.pi_ne_zero
  unfold speciesEntropy effSpeciesN
  field_simp
  ring

/-- **THE MIXED-CONTENT `1/4`.** For ANY field content `S` with nonvanishing species sum, arbitrary
    nonzero area `A` and cutoff `Λ`: the ratio of the one-loop entanglement entropy to `A/G_ind`
    (with both computed from the SAME species datum) is `1/4` — the ENTIRE species sum
    `n_s c_s + n_f c_f + n_v c_v`, the cutoff `Λ`, the area `A`, and `π` ALL cancel. This is
    `SakharovRatio.sakharov_ratio` upgraded from one scalar to a mixed field content: the `1/4` is
    fixed by the two geometric normalizations `48π` and `12π` alone. Consistency chain over one
    shared cited datum — NOT an independent cross-check. -/
theorem species_sakharov_ratio (S : SpeciesContent)
    (hS : S.nScalar * S.cScalar + S.nWeyl * S.cWeyl + S.nVector * S.cVector ≠ 0)
    (A Λ : ℝ) (hA : A ≠ 0) (hΛ : Λ ≠ 0) :
    speciesEntropy S A Λ / (A * inducedInvG S Λ) = 1 / 4 := by
  have hπ := Real.pi_ne_zero
  unfold speciesEntropy inducedInvG effSpeciesN
  field_simp
  ring

/-- **CAPSTONE — the mixed-content entropy IS the capacity.** For any field content `S` with
    nonvanishing species sum and any cutoff `Λ ≠ 0`, the one-loop entanglement entropy equals the
    Bekenstein–Hawking capacity computed with the induced Newton constant of the SAME species datum:
    `S_ent(S, A, Λ) = A / (4 · G_ind(N_eff(S), Λ))`. One shared species datum feeds both sides; the
    equality is a theorem (the species sum cancels). No numerical `G`, no independently computed
    side — the coherence of the shared cited datum through both bookkeepings is what is certified. -/
theorem speciesEntropy_eq_capacity (S : SpeciesContent)
    (hS : S.nScalar * S.cScalar + S.nWeyl * S.cWeyl + S.nVector * S.cVector ≠ 0)
    (A Λ : ℝ) (hΛ : Λ ≠ 0) :
    speciesEntropy S A Λ = A / (4 * inducedG (effSpeciesN S) Λ) := by
  have hπ := Real.pi_ne_zero
  unfold speciesEntropy inducedG effSpeciesN
  field_simp
  ring

/-- **Corollary through the holographic bridge**: the BTZ boundary-CFT Cardy microstate entropy,
    evaluated with the induced `G` of the species datum `S`, equals the mixed-content one-loop
    entanglement entropy of that SAME datum across the horizon `A = 2π r₊`. Chains
    `HolographicBridge.btz_cardy_eq_qiqth_capacity` through the species accounting — still the one
    shared cited datum, now threaded through the Cardy bookkeeping as well. -/
theorem btz_cardy_eq_species_entropy (S : SpeciesContent) (rp rm Λs ℓ : ℝ)
    (hN : 0 < effSpeciesN S) (hΛ : 0 < Λs) (hℓ : 0 < ℓ) (hrp : 0 ≤ rp)
    (hlo : -rp ≤ rm) (hhi : rm ≤ rp) :
    AdSCFT.cardyEntropy
        (AdSCFT.bhCentralCharge ℓ (inducedG (effSpeciesN S) Λs))
        (AdSCFT.bhCentralCharge ℓ (inducedG (effSpeciesN S) Λs))
        (AdSCFT.btzL0 rp rm (inducedG (effSpeciesN S) Λs) ℓ)
        (AdSCFT.btzL0bar rp rm (inducedG (effSpeciesN S) Λs) ℓ)
      = speciesEntropy S (2 * π * rp) Λs := by
  rw [QIQTH.HolographicBridge.btz_cardy_eq_qiqth_capacity rp rm (effSpeciesN S) Λs ℓ
    hN hΛ hℓ hrp hlo hhi]
  have hπ := Real.pi_ne_zero
  unfold speciesEntropy effSpeciesN
  field_simp
  ring

/-! ## Track A checkpoint

HAVE: "We have the regulator rigidity theorem — any positive, species-additive, monotone family
covariant under rescalings is forced to the Sakharov/Dvali form 1/G = N_eff·Λ^κ, with κ = 2 fixed by
a single dimensional calibration and an explicit witness that weakened covariance breaks the
conclusion — together with the first derived (not cited) heat-kernel coefficient in the repository
(the 1D Gaussian a₀ = 1/√(4πt), from Mathlib's Gaussian integral) and the mixed-field-content
Sakharov consistency chain: one shared species datum feeds both the entanglement entropy and the
induced 1/G, and their ratio being 1/4 — and the entropy equalling A/4G — are theorems with the
entire species sum cancelling."

HAVE NOT: "We do not have the numerical value of G, and we have not derived the per-species
coefficients: the c_i remain cited one-loop Seeley–DeWitt heat-kernel data, hand-entered; no lattice
area-law scaling, no one-loop integral, and no independent microstate count is formalized — the
consistency chain certifies that one shared cited datum is wired coherently through both
bookkeepings, not that either side is independently computed."
-/

end QIQTH.InducedG
