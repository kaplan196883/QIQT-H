/-
  MixedEnvelopeAssembly — J4-913: the FIRST full CONSTRUCTION of a `MixedDirectionsFieldHessianEnvelope`
  term, reducing ALL FIVE fields of the fourth `hCConv` hypothesis to a single FLAT named-carry list at
  a CONSISTENT choice of `(BL, BF, C)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.  This brick
  is pure WIRING: it composes the four banked per-field reductions
    • `BFGaussianEnvelopeClosed.witnessFieldHessian_hFd_of_peak_dominator` (J4-868 — `hFd` at the sup),
    • `HkintReducedToHbint.hkint_reduces_to_hbint_concrete`             (J4-875 — `hkint` ⟸ `hbint`),
    • `HZMassCappedWindowClosed.hzmass_capped_window_closed`            (J4-886 — `hzmass` at `C = M·t`),
  into an ACTUAL `MixedDirectionsFieldHessianEnvelope` STRUCTURE, demonstrating that the per-field `BL`/`BF`
  choices RECONCILE at the single consistent pair
    `BL s z := CB s · gaussDdim (2·s) z`   (the width-`2s` Levi envelope shape, J4-883 §A),
    `BF s z := ⨆ x', ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x'‖`   (the concrete sup, J4-868),
    `C      := M·t`   (the capped-window constant, J4-886).
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS ANSWERS (the composition question).

  Prior bricks REDUCED each field of `MixedDirectionsFieldHessianEnvelope` to named carries in ISOLATION,
  but NO term of the structure had ever been built — leaving open whether the five reductions use a
  MUTUALLY CONSISTENT `(BL, BF, C)`.  They do.  `mixedEnvelope_of_named_carries` exhibits the actual
  structure from the flat carry list
    {hMnn, hepspos, hCBnn, hPpknn, hPCbound}      — elementary window/constant facts,
    {hLevi}                                        — the width-`2s` Levi envelope (J4-883 §A, ⟸ hEmeas),
    {hcpt, hpeak}                                  — the gate-geometry inputs of `hFd` (J4-868),
    {hbint}                                        — the product-dominator integrability (⟸ b<r₀, J4-907),
    {hmeas}                                        — the `kPrime` z-measurability (J4-841),
    {hBFpeak}                                      — the z-uniform field-Hessian peak (J4-868),
  deriving `hFd`, `hkint`, `hzmass` internally and threading `hLevi`, `hbint` through.

  ## HONEST RESIDUAL (unchanged).  The FLAT carry list above is exactly the union of the still-standing
  named walls of the fourth hypothesis: `hEmeas` (feeds `hLevi`), `b < r₀` (feeds `hbint`), the gate
  compactness / peak-dominator geometry (feeds `hFd`/`hBFpeak`), and the `kPrime` measurability family.
  This brick CLOSES NONE of them — it proves they SUFFICE, jointly, to build the structure.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedDirectionsFieldHessianEnvelope
import QIQTH.BFGaussianEnvelopeClosed
import QIQTH.HZMassCappedWindowClosed
import QIQTH.HkintReducedToHbint
import QIQTH.AlphaLevi
import QIQTH.OffSVanishing

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.LaplaceBeltrami QIQTH.LeviSeries QIQTH.FderivBulkConcrete QIQTH.ResidueBound
open QIQTH.MixedDirFieldHessianEnvelope
open QIQTH.BFGaussianEnvelopeClosed QIQTH.HZMassCappedWindowClosed QIQTH.HkintReducedToHbint
open scoped Topology Interval BigOperators

namespace QIQTH.MixedEnvelopeAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the empty-gate Levi vanishing (for non-vacuity).
    ############################################################################### -/

/-- **§0 — `leviSeries_emptyGate_eq_zero`.**  At the DEGENERATE empty gate `S := fun _ => ∅` the gated
    van-Vleck witness is identically `0` (`p ∈ ∅` is always false), so the heat operator maps it to the
    zero residual (`deriv 0 = 0`, `laplaceBeltrami 0 = 0`), and the signed Levi series of the zero
    residual vanishes term-by-term (`iterE_zero_eq_zero`).  Used ONLY to inhabit the assembly's carry
    list at the empty gate.  NOT `a₁ = R/6`. -/
theorem leviSeries_emptyGate_eq_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (s : ℝ) (z : Point n) :
    leviSeries (heatOp g gi
        (vanVleckGatedWitness g gi hC hK (fun _ => (∅ : Set (Point n))) a b)) s z 0 = 0 := by
  -- (1) the empty-gate witness is the zero kernel.
  have hw : vanVleckGatedWitness g gi hC hK (fun _ => (∅ : Set (Point n))) a b
      = (fun _ _ _ => (0 : ℝ)) := by
    funext τ p q
    simp only [vanVleckGatedWitness, gatedKernel]
    by_cases hq : q ∈ K <;> simp [hq]
  rw [hw]
  -- (2) the heat operator sends the zero kernel to the zero residual.
  have hE : heatOp g gi (fun _ _ _ => (0 : ℝ)) = (fun _ _ _ => (0 : ℝ)) := by
    funext τ x y
    simp only [heatOp]
    have hlap : laplaceBeltrami g gi (fun _ : Point n => (0 : ℝ)) x = 0 := by
      simp only [laplaceBeltrami, QIQTH.OffSVanishing.pd_zero_fun]
      simp
    rw [hlap]
    simp
  rw [hE]
  -- (3) the signed Levi series of the zero residual vanishes.
  have hterm : ∀ k : ℕ,
      (-1 : ℝ) ^ (k + 1) * iterE (fun _ _ _ => (0 : ℝ)) (k + 1) s z 0 = 0 := by
    intro k; rw [QIQTH.AlphaLevi.iterE_zero_eq_zero]; ring
  simp only [leviSeries, hterm, tsum_zero]

/-! ###############################################################################
    ### §1 — THE ASSEMBLY: the five reductions compose at consistent `(BL, BF, C)`.
    ############################################################################### -/

/-- **★★★ §1 — `mixedEnvelope_of_named_carries`.**  THE FIRST full construction of a
    `MixedDirectionsFieldHessianEnvelope` term.  At the consistent choice
      `BL s z := CB s · gaussDdim (2·s) z`,
      `BF s z := ⨆ x', ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x'‖`,
      `C      := M · t`,
    the FLAT named-carry list assembles the structure:
      • `hLevi`   — the width-`2s` Levi envelope (threaded; J4-883 §A supplies it, ⟸ hEmeas);
      • `hFd`     — DERIVED from `{hcpt, hpeak}` via `witnessFieldHessian_hFd_of_peak_dominator`;
      • `hkint`   — DERIVED from `{hbint, hmeas, hLevi, hFd}` via `hkint_reduces_to_hbint_concrete`;
      • `hbint`   — threaded (J4-907 supplies it, ⟸ `b < r₀`);
      • `hzmass`  — DERIVED from `{hMnn, hepspos, hbint, hBFpeak, hBLnn, hBLgauss, hPpknn, hPCbound}`
                    via `hzmass_capped_window_closed`, at `C = M·t`.
    The elementary `hBLnn`/`hBLgauss` are built internally from `hCBnn` (`gaussDdim ≥ 0`, `le_refl`).
    Proves the five reductions RECONCILE; closes none of the named carries.  NOT `a₁ = R/6`. -/
theorem mixedEnvelope_of_named_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (M : ℝ) (CB Ppk : ℝ → ℝ)
    (hMnn : 0 ≤ M) (hepspos : 0 < t - epsSeq m)
    (hCBnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 ≤ CB s)
    (hPpknn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → 0 ≤ Ppk s)
    (hPCbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → Ppk s * CB s ≤ M)
    (hLevi : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CB s * gaussDdim (2 * s) z)
    (hcpt : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, IsCompact (closure (S z)))
    (hpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∃ Poly : Point n → ℝ, Continuous Poly ∧
          ∀ x ∈ closure (S z),
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
              ≤ gaussDdim (t - s) (0 : Point n) * Poly x)
    (hbint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        Integrable (fun z => (CB s * gaussDdim (2 * s) z)
          * (⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖))
          volume)
    (hmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ x : Point n,
          AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z) volume)
    (hBFpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z : Point n,
          (⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)
            ≤ Ppk s) :
    MixedDirectionsFieldHessianEnvelope g gi hC hK S a b i t m (M * t)
      (fun s z => CB s * gaussDdim (2 * s) z)
      (fun s z => ⨆ x' : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖) := by
  -- hFd from the J4-868 peak-dominator reduction (BF := the concrete sup).
  have hFd := witnessFieldHessian_hFd_of_peak_dominator g gi hC hK S a b i t m hcpt hpeak
  -- the elementary `BL := CB·gaussDdim(2s)` nonnegativity / self-domination.
  have hBLnn : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, 0 ≤ CB s * gaussDdim (2 * s) z := by
    filter_upwards [hCBnn] with s hs hmem z
    exact mul_nonneg (hs hmem) (gaussDdim_nonneg _ _)
  have hBLgauss : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ z : Point n, CB s * gaussDdim (2 * s) z ≤ CB s * gaussDdim (2 * s) z :=
    ae_of_all _ (fun s _ z => le_refl _)
  -- hkint downstream of hbint (J4-875).
  have hkint := hkint_reduces_to_hbint_concrete g gi hC hK S a b i t m
    (fun s z => CB s * gaussDdim (2 * s) z)
    (fun s z => ⨆ x' : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)
    hbint hmeas hLevi hFd
  -- hzmass on the capped window at `C = M·t` (J4-886).
  have hzmass := hzmass_capped_window_closed (n := n) t m M
    (fun s z => CB s * gaussDdim (2 * s) z)
    (fun s z => ⨆ x' : Point n,
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)
    Ppk CB hMnn hepspos hbint hBFpeak hBLnn hBLgauss hPpknn hPCbound
  exact
    { hLevi := hLevi
      hFd := hFd
      hkint := hkint
      hbint := hbint
      hzmass := hzmass }

/-! ###############################################################################
    ### §2 — NON-VACUITY: the carry list is jointly inhabited (empty gate).
    ############################################################################### -/

/-- **§2 — NON-VACUITY.**  The assembly's flat carry list is JOINTLY INHABITED at the DEGENERATE empty
    gate `S := fun _ => ∅` with `CB := 0`, `Ppk := 0`, `M := 0`: the field-derivative kernel and the Levi
    series both vanish identically (`witnessFieldHessian_fderiv_eqZero_of_notMem_closure`,
    `leviSeries_emptyGate_eq_zero`), so every carry holds with zeros, and
    `mixedEnvelope_of_named_carries` FIRES — producing a genuine `MixedDirectionsFieldHessianEnvelope`
    term.  No J4-548/847-style unsatisfiable antecedent; the conclusion is a real (degenerate) structure,
    never the conclusion in disguise.  NOT `a₁ = R/6`. -/
theorem mixedEnvelope_assembly_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ)
    (hepspos : 0 < t - epsSeq m) :
    MixedDirectionsFieldHessianEnvelope g gi hC hK (fun _ => (∅ : Set (Point n))) a b i t m
      ((0 : ℝ) * t)
      (fun s z => (fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z)
      (fun s z => ⨆ x' : Point n,
        ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖) := by
  -- the empty-gate field-Hessian norm vanishes at every point.
  have hfd0 : ∀ (s : ℝ) (z x : Point n),
      ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x‖ = 0 := by
    intro s z x
    rw [QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) z x (by simp)]
    exact norm_zero
  -- the sup of the zero family is `0`.
  have hsup0 : ∀ (s : ℝ) (z : Point n),
      (⨆ x' : Point n,
        ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖) = 0 := by
    intro s z
    have : (fun x' : Point n =>
        ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖)
        = fun _ => (0 : ℝ) := by
      funext x'; exact hfd0 s z x'
    rw [this]; exact ciSup_const
  refine mixedEnvelope_of_named_carries g gi hC hK (fun _ => (∅ : Set (Point n))) a b i t m 0
    (fun _ => 0) (fun _ => 0) (le_refl 0) hepspos ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ae_of_all _ (fun s _ => le_refl 0)
  · exact ae_of_all _ (fun s _ => le_refl 0)
  · exact ae_of_all _ (fun s _ => by simp)
  · -- hLevi: |leviSeries| = 0 ≤ 0·gaussDdim.
    refine ae_of_all _ (fun s _ => ae_of_all _ (fun z => ?_))
    rw [leviSeries_emptyGate_eq_zero g gi hC hK a b s z, abs_zero, zero_mul]
  · -- hcpt: closure ∅ compact.
    exact ae_of_all _ (fun s _ => ae_of_all _ (fun z => by rw [closure_empty]; exact isCompact_empty))
  · -- hpeak: vacuous over closure ∅.
    refine ae_of_all _ (fun s _ => ae_of_all _ (fun z => ⟨fun _ => 0, continuous_const, ?_⟩))
    rw [closure_empty]; intro x hx; exact absurd hx (Set.notMem_empty x)
  · -- hbint: the product is `0`, integrable.
    refine ae_of_all _ (fun s _ => ?_)
    have : (fun z => ((fun _ => (0 : ℝ)) s * gaussDdim (2 * s) z)
        * (⨆ x' : Point n,
            ‖fderiv ℝ (fun y =>
              witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖))
        = fun _ => (0 : ℝ) := by
      funext z; rw [zero_mul, zero_mul]
    rw [this]; exact integrable_zero _ _ _
  · -- hmeas: kPrime = leviSeries • fderiv = 0 (fderiv vanishes).
    refine ae_of_all _ (fun s _ x => ?_)
    have : (fun z => kPrime g gi hC hK (fun _ => (∅ : Set (Point n))) a b i t s x z)
        = fun _ => (0 : Point n →L[ℝ] ℝ) := by
      funext z
      rw [kPrime,
        QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
          g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) z x (by simp),
        smul_zero]
    rw [this]; exact aestronglyMeasurable_const
  · -- hBFpeak: the sup is `0 ≤ 0`.
    exact ae_of_all _ (fun s _ z => by rw [hsup0 s z])

end QIQTH.MixedEnvelopeAssembly

section AxiomChecks
open QIQTH.MixedEnvelopeAssembly
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms leviSeries_emptyGate_eq_zero
#print axioms mixedEnvelope_of_named_carries
#print axioms mixedEnvelope_assembly_nonvacuous
end AxiomChecks
