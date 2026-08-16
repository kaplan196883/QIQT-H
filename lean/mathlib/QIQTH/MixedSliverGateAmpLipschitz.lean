/-
  MixedSliverGateAmpLipschitz — the CONCRETE `gateAmp` Lipschitz constant, and its wiring (together with
  the carried `leviSeries`-kernel Lipschitz constant) into the exact mixed-sliver `hqLip` triple.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It closes the
  concrete-instantiation item (b) of J4-800/801 — "concrete per-slice Lipschitz constants of
  `leviSeries` / `gateAmp` as inputs to the `hqLip` triple" — for the `gateAmp` factor, and WIRES the
  two concrete constants into `MixedSliverQLipInt.hqLip_triple_of_bounded_lipschitz`.

  ── THE `gateAmp` SIDE (genuinely new here). ─────────────────────────────────────────────────────────
  `gateAmp S z₀ A τ ζ = (S z₀).indicator (A τ ·) ζ` (J4-792) is `Set.indicator`-gated, so a priori it
  can JUMP at the gate boundary `∂(S z₀)` and NOT be Lipschitz.  The chart-surface construction removes
  the jump: the raw amplitude `A τ` carries `radialCutoff` as a LEADING factor
  (`B2MeasurabilityDissolution.radialCutoff_zero_on_frontier_collar`, J4-795 Task B) which VANISHES on
  the frontier collar and beyond — i.e. `A τ ≡ 0` off `S z₀` whenever `S z₀ ⊇ radial support`.  Under
  exactly that (already-carried) geometric condition the indicator is REDUNDANT (`gateAmp = A τ`
  pointwise), so `gateAmp` inherits verbatim the raw amplitude's Lipschitz constant `L_A` and sup-bound
  `M_A`.  This is the elementary but precise fact the task named: indicator-gated Lipschitz continuity
  follows from (a) Lipschitz of the underlying amplitude, PLUS (b) its vanishing off the gate (which
  `radialCutoff` supplies).  Off-gate vanishing is a genuine, satisfiable hypothesis (vacuous when
  `S z₀ = Set.univ`, or when `A = 0`), NEVER the conclusion.

  ── THE `leviSeries` SIDE (carried, established elsewhere). ──────────────────────────────────────────
  The Levi kernel's concrete spatial Lipschitz constant is `L_F = L_E + K·2√s` (`O(√s)`), derived by
  `HeatResidualBound.resolvent_lipschitz_pointwise` (J4-144, `LeviLipschitz.lean`) from the resolvent /
  Volterra identity `F = −E − E∗F`; the `(s−r)^{−1/2}` residual singularity integrates to `2√s`.  That
  file already defers the same Gaussian bookkeeping carries (`hE1`, `hSlice`); we carry `hFLip`/`hFbnd`
  as its OUTPUT, introducing NO new wall.  (Sympy sanity-check of the `√s` scaling in the session log.)

  ── WHAT LANDS (all abstract / carried; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `gateAmp_eq_of_vanishing_off`      — `gateAmp = A τ` pointwise when `A τ` vanishes off the gate.
    * `gateAmp_lipschitz_of_vanishing`   — the CONCRETE `gateAmp` Lipschitz constant `= L_A`.
    * `gateAmp_bound_of_vanishing`       — the CONCRETE `gateAmp` sup-bound `= M_A`.
    * `mixedSliver_hqLip_triple_via_gateAmp` — the exact `hqLip` triple for `ζ ↦ gateAmp·(F s ζ 0)`
        from the two concrete constants (`gateAmp` side derived, `leviSeries` side carried).

  Every hypothesis is satisfiable and non-vacuous, and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedNormalFormFull
import QIQTH.MixedSliverQLipInt

open MeasureTheory
open QIQTH.Curvature
open QIQTH.MixedNormalFormFull

namespace QIQTH.MixedSliverGateAmpLipschitz

variable {n : ℕ}

/-! ############################################################################
    ### The `gateAmp` redundancy lemma — the indicator disappears off-gate.
    ############################################################################ -/

/-- **`gateAmp_eq_of_vanishing_off`.**  If the raw amplitude slice `A τ` vanishes off the gate
    (`∀ ζ ∉ S z₀, A τ ζ = 0` — the `radialCutoff`-supported condition), then the `Set.indicator` gate is
    redundant: `gateAmp S z₀ A τ ζ = A τ ζ` for EVERY `ζ`.  On-gate by `gateAmp_of_mem`; off-gate both
    sides are `0` (`gateAmp_of_notMem` and the hypothesis).  ⚠ NOT `a₁ = R/6`. -/
theorem gateAmp_eq_of_vanishing_off (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (τ : ℝ) (hoff : ∀ ζ ∉ S z₀, A τ ζ = 0) :
    ∀ ζ, gateAmp S z₀ A τ ζ = A τ ζ := by
  intro ζ
  by_cases hζ : ζ ∈ S z₀
  · exact gateAmp_of_mem S z₀ A τ hζ
  · rw [gateAmp_of_notMem S z₀ A τ hζ, hoff ζ hζ]

/-- **★ `gateAmp_lipschitz_of_vanishing` — the CONCRETE `gateAmp` Lipschitz constant.**  If the raw
    amplitude slice `A τ` is `L_A`-Lipschitz in the `dist`-shape and vanishes off the gate, then the gated
    amplitude `ζ ↦ gateAmp S z₀ A τ ζ` is `L_A`-Lipschitz — the indicator introduces NO extra constant
    (it disappears, `gateAmp = A τ`).  This is the `gateAmp` half of J4-800/801 item (b).  ⚠ NOT
    `a₁ = R/6`. -/
theorem gateAmp_lipschitz_of_vanishing (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (τ L_A : ℝ)
    (hoff : ∀ ζ ∉ S z₀, A τ ζ = 0)
    (hALip : ∀ ζ ζ' : Point n, |A τ ζ - A τ ζ'| ≤ L_A * dist ζ ζ') :
    ∀ ζ ζ' : Point n, |gateAmp S z₀ A τ ζ - gateAmp S z₀ A τ ζ'| ≤ L_A * dist ζ ζ' := by
  have heq := gateAmp_eq_of_vanishing_off S z₀ A τ hoff
  intro ζ ζ'
  rw [heq ζ, heq ζ']
  exact hALip ζ ζ'

/-- **`gateAmp_bound_of_vanishing` — the CONCRETE `gateAmp` sup-bound.**  If `A τ` is bounded by `M_A`
    and vanishes off the gate, then `gateAmp S z₀ A τ` is bounded by `M_A` (the indicator disappears).
    ⚠ NOT `a₁ = R/6`. -/
theorem gateAmp_bound_of_vanishing (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (τ M_A : ℝ)
    (hoff : ∀ ζ ∉ S z₀, A τ ζ = 0)
    (hAbnd : ∀ ζ : Point n, |A τ ζ| ≤ M_A) :
    ∀ ζ : Point n, |gateAmp S z₀ A τ ζ| ≤ M_A := by
  have heq := gateAmp_eq_of_vanishing_off S z₀ A τ hoff
  intro ζ
  rw [heq ζ]
  exact hAbnd ζ

/-! ############################################################################
    ### The wiring capstone — the two concrete constants → the exact `hqLip` triple.
    ############################################################################ -/

/-- **★★ `mixedSliver_hqLip_triple_via_gateAmp` — item (b) closed to its carries.**  Assembling the two
    CONCRETE per-slice Lipschitz constants named at J4-800/801 —
      • the `gateAmp` amplitude factor `f ζ := gateAmp S z₀ A τ ζ`, `L_A`-Lipschitz and `M_A`-bounded via
        `gateAmp_lipschitz_of_vanishing` / `gateAmp_bound_of_vanishing` from its off-gate vanishing;
      • the `leviSeries` kernel factor `g ζ := F s ζ 0`, carried `L_F`-Lipschitz / `M_F`-bounded (the
        `L_F = L_E + K·2√s` output of `HeatResidualBound.resolvent_lipschitz_pointwise`) —
    into `MixedSliverQLipInt.hqLip_triple_of_bounded_lipschitz` yields the EXACT mixed-sliver `hqLip`
    triple for the product `ζ ↦ gateAmp S z₀ A τ ζ · F s ζ 0`:
      `(M_A·L_F + M_F·L_A)`-Lipschitz  ∧  AEStronglyMeasurable  ∧  bounded by `M_A·M_F`.
    This is precisely the input shape the mixed sliver `witness_sliver2_xuniform_mixed` consumes; the
    `gateAmp` constant is DERIVED here, the `leviSeries` constant CARRIED (no new wall).  ⚠ NOT `a₁ =R/6`. -/
theorem mixedSliver_hqLip_triple_via_gateAmp
    (S : Point n → Set (Point n)) (z₀ : Point n)
    (A : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ) (τ s M_A M_F L_A L_F : ℝ)
    (hoff : ∀ ζ ∉ S z₀, A τ ζ = 0)
    (hALip : ∀ ζ ζ' : Point n, |A τ ζ - A τ ζ'| ≤ L_A * dist ζ ζ')
    (hAbnd : ∀ ζ : Point n, |A τ ζ| ≤ M_A)
    (hFLip : ∀ ζ ζ' : Point n, |F s ζ 0 - F s ζ' 0| ≤ L_F * dist ζ ζ')
    (hFbnd : ∀ ζ : Point n, |F s ζ 0| ≤ M_F)
    (hmeas : AEStronglyMeasurable
        (fun ζ : Point n => gateAmp S z₀ A τ ζ * F s ζ 0) volume) :
    (∀ z w : Point n, |gateAmp S z₀ A τ z * F s z 0 - gateAmp S z₀ A τ w * F s w 0|
        ≤ (M_A * L_F + M_F * L_A) * dist z w)
    ∧ AEStronglyMeasurable (fun ζ : Point n => gateAmp S z₀ A τ ζ * F s ζ 0) volume
    ∧ ∃ M, ∀ ζ : Point n, |gateAmp S z₀ A τ ζ * F s ζ 0| ≤ M :=
  QIQTH.MixedSliverQLipInt.hqLip_triple_of_bounded_lipschitz
    (fun ζ => gateAmp S z₀ A τ ζ) (fun ζ => F s ζ 0)
    M_A M_F L_A L_F
    (gateAmp_bound_of_vanishing S z₀ A τ M_A hoff hAbnd)
    hFbnd
    (gateAmp_lipschitz_of_vanishing S z₀ A τ L_A hoff hALip)
    hFLip
    hmeas

end QIQTH.MixedSliverGateAmpLipschitz

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverGateAmpLipschitz
#print axioms gateAmp_eq_of_vanishing_off
#print axioms gateAmp_lipschitz_of_vanishing
#print axioms gateAmp_bound_of_vanishing
#print axioms mixedSliver_hqLip_triple_via_gateAmp
end AxiomChecks
