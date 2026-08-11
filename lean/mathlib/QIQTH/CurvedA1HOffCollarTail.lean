/-
  CurvedA1HOffCollarTail — J4-593: discharge/assess the `hOffCollarTail` carrier of the
  NON-VACUOUS curved a₁ = R/6 capstone (`CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  This attacks the `hOffCollarTail` carrier of the NON-VACUOUS curved a₁ = R/6
  capstone; it proves NOTHING about `R/6`.  a₁ = R/6 remains CONDITIONAL; the curved capstone still owes
  the OTHER carried residuals — `hsrc`, the census/measurability/domination piles, the convergence trio,
  `hmassone`'s pre-ρ carriers, and `hInnerCont`'s `hContDom`.  No `sorry`/`admit` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  the conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE VERDICT (from the mainline, not guessed).

  `hOffCollarTail` is the abstract `Prop` slot in the residue ledgers
  `HGpowFromCollar.collar_hGpow_residual` (J4-545) and `CurvedA1AmplitudeData.curved_amplitudeData_residual`:
  the OFF-COLLAR corrected Gaussian-tail remainder on `‖z‖ > c√τ` that RECONSTITUTES the full-space
  Hessian moment `∫ (z_i²−2τ)/(4τ²)·G_τ = 0` — destroyed by the `τ`-shrinking collar truncation — so
  that `hOnCollar + hOffCollarTail` yields the per-slice inner bound in the `K₁·(u−s)^{-1/2}+K₀` shape
  of `hinner_window` (hence the HI-leg `MemAdjHi` via `hGpow_from_innerWindow`).

  ★ THE KEY (from `SliverTailMatched` / `OffCollarTailMoment`).  The off-collar tail's LEADING integrand
  `hessGaussFactor i τ z = H_{τ,i}(z) := (z_i²−2τ)/(4τ²)·G_τ(z)` is the FLAT heat-kernel Hessian factor:
  it does **NOT** depend on `κ` / the curved metric `g^K`.  The genuinely-curved witness enters ONLY
  through the AMPLITUDE `q` (`= Aamp^K·F^K` at the call site).  Consequently the entire off-collar
  reconstitution is METRIC-INDEPENDENT and already BANKED, generic in the amplitude:
    • `SliverTailMatched.collarMoment_eq_neg_tail` (J4-354): the EXACT pairing `∫_{C_τ} H = −T_τ`.
    • `SliverTailMatched.sliver_term1_on_collar_matched` (J4-354): ★ the cancellation-aware matched
      remainder `‖(∫_{C_τ} H·q) + q(0)·T_τ‖ ≤ L·(15/2·n)/√τ` for ANY Lipschitz amplitude `q`
      (constant `L`) — the exact `√τ`-gain reconstitution that makes `hOnCollar + hOffCollarTail` yield
      the `K₁·(u−s)^{-1/2}` shape (`K₁ = L·15/2·n`, `K₀ = 0`).
    • `OffCollarTailMoment.tailMoment_collar_expSuppressed` (J4-546): the bare tail moment is
      exponentially small — `|T_τ| = |tailMoment i τ (c√τ)| ≤ (√2)ⁿ·exp(−c²/8)·(2n+1)/(2τ)`.

  CONSEQUENCE.  `hOffCollarTail` for `g^K` is DISCHARGEABLE from the banked matched-pair + exp-suppression
  machinery, generic in the (Lipschitz) amplitude.  The ledgers' attribution of it as "the GENUINE
  surviving curved geometric input" is an OVER-credit: the off-collar tail is a flat-Gaussian fact; the
  genuine curved input it CONSUMES is the Lipschitz regularity of the curved amplitude `q = Aamp^K·F^K`,
  which is the ON-collar bundle's carry (`hOnCollar` / `hjets`), NOT the tail itself.

  ## WHAT LANDS HERE.
    • `curved_hOffCollarTail_at_gate` — ★ the concrete `hOffCollarTail` shape at the curved `g^K` gate:
      for ANY Lipschitz + measurable amplitude `q` and collar radius `R = c√τ` (`0 ≤ c`), the matched
      off-collar reconstitution `‖(∫_{C_{c√τ}} H·q) + q(0)·T_{c√τ}‖ ≤ L·(15/2·n)/√τ` AND the
      exp-suppressed bare tail `|T_{c√τ}| ≤ (√2)ⁿ·exp(−c²/8)·(2n+1)/(2τ)`, both from the banked
      metric-independent engines.  (The curved gate params `κ`, `hκ` are carried as LOCATORS — the
      estimate is metric-independent, the honest finding.)
    • `curved_hOffCollarTail_satisfiable` — the hypothesis surface is jointly satisfiable at a genuinely
      curved parameter (`κ < 0`, `1 ≤ n`) with a NON-CONSTANT 1-Lipschitz amplitude (a coordinate
      projection) — so the reconstitution is not the vacuous `L = 0` witness.

  ⚠  `a₁ = R/6` remains CONDITIONAL.  Discharging `hOffCollarTail` (a flat-Gaussian tail fact, generic in
  the amplitude) does NOT derive the coefficient: the curved capstone still owes `hsrc`, the
  census/measurability/domination piles, the convergence trio, `hmassone`'s pre-ρ carriers, and
  `hInnerCont`'s `hContDom`; and the amplitude Lipschitz regularity it consumes is the ON-collar `hjets`
  carry.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SliverTailMatched
import QIQTH.OffCollarTailMoment

open MeasureTheory
open QIQTH.Curvature

namespace QIQTH.CurvedA1HOffCollarTail

variable {n : ℕ}

/-- **★ `curved_hOffCollarTail_at_gate` — THE `hOffCollarTail` CARRIER OF THE CURVED CAPSTONE,
    DISCHARGED (generic in the amplitude).**  The concrete off-collar Gaussian-tail shape carried by the
    curved a₁ = R/6 capstone at the genuinely-curved gate `g^K = curvedRNCMetric κ`.  For ANY amplitude
    `q : Point n → ℝ` that is `L`-Lipschitz and a.e.-strongly measurable, and any collar radius
    `R = c·√τ` (`0 ≤ c`, `0 < τ`), BOTH:
      (i)  the MATCHED off-collar reconstitution (the cancellation-aware remainder, `√τ`-gain):
             `‖(∫_{C_{c√τ}} H_{τ,i}·q) + q(0)·T_{c√τ}‖ ≤ L·(15/2·n)/√τ`,   `T = tailMoment`,
           obtained from the banked `SliverTailMatched.sliver_term1_on_collar_matched` (the `q(0)·T_{c√τ}`
           off-collar tail term cancels EXACTLY against the on-collar leading moment via
           `collarMoment_eq_neg_tail`, leaving only the `√τ`-small increment);
      (ii) the EXP-SUPPRESSED bare off-collar tail moment:
             `|T_{c√τ}| ≤ (√2)ⁿ · exp(−c²/8) · (2n+1)/(2τ)`,
           obtained from the banked `OffCollarTailMoment.tailMoment_collar_expSuppressed`.
    The Hessian-Gaussian factor `H_{τ,i}` is the FLAT heat kernel's — so this estimate is
    METRIC-INDEPENDENT; the curved gate params `κ`, `hκ` are carried only to LOCATE it at the `g^K` gate
    (the honest finding: `hOffCollarTail` is a flat-Gaussian tail fact, generic in the amplitude, and the
    genuine curved input it consumes is the amplitude's Lipschitz regularity = the ON-collar `hjets`
    carry).  NOT the conclusion, NOT vacuous.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hOffCollarTail_at_gate (κ : ℝ) (hκ : κ < 0)
    (τ c : ℝ) (hτ : 0 < τ) (hc : 0 ≤ c) (i : Fin n)
    (q : Point n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hqLip : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) :
    ‖(∫ z in SliverTailMatched.collar (c * Real.sqrt τ),
          SliverTailMatched.hessGaussFactor i τ z * q z)
        + q 0 * SliverTailMatched.tailMoment i τ (c * Real.sqrt τ)‖
        ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ
      ∧ |SliverTailMatched.tailMoment i τ (c * Real.sqrt τ)|
        ≤ Real.sqrt 2 ^ n * Real.exp (-(c ^ 2) / 8) * ((2 * (n : ℝ) + 1) / (2 * τ)) := by
  -- both facts are metric-independent (`κ`, `hκ` are gate locators); κ < 0 kept only for the gate.
  have _hgate : κ < 0 := hκ
  refine ⟨?_, ?_⟩
  · -- (i) the matched off-collar tail reconstitution (√τ-gain), banked, generic in Lipschitz `q`.
    exact SliverTailMatched.sliver_term1_on_collar_matched τ hτ i q L hL hqLip hqmeas
      (c * Real.sqrt τ)
  · -- (ii) the exp-suppressed bare off-collar tail moment, banked, metric-independent.
    exact OffCollarTailMoment.tailMoment_collar_expSuppressed τ c hτ hc i

/-- **`curved_hOffCollarTail_satisfiable` — NON-VACUITY of the `hOffCollarTail` carrier.**  The
    hypothesis surface of `curved_hOffCollarTail_at_gate` is JOINTLY satisfiable at a genuinely-curved
    parameter (`κ < 0`) with a NON-CONSTANT `1`-Lipschitz, a.e.-strongly-measurable amplitude (a
    coordinate projection `q = z ↦ z i₀`), for `1 ≤ n`.  This rules out the vacuous `L = 0`
    (constant-amplitude) reading: the matched reconstitution genuinely fires on a nontrivial amplitude.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hOffCollarTail_satisfiable (hn : 1 ≤ n) :
    ∃ (κ : ℝ) (q : Point n → ℝ) (L : ℝ),
      κ < 0
      ∧ 0 ≤ L
      ∧ (∀ z w, |q z - q w| ≤ L * dist z w)
      ∧ AEStronglyMeasurable q volume
      ∧ (∃ z w : Point n, q z ≠ q w) := by
  have hpos : 0 < n := hn
  refine ⟨-1, (fun z => z ⟨0, hpos⟩), 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · -- coordinate projection is 1-Lipschitz for the Pi sup-norm on `Point n = Fin n → ℝ`.
    intro z w
    rw [dist_eq_norm, one_mul]
    calc |z ⟨0, hpos⟩ - w ⟨0, hpos⟩|
        = |(z - w) ⟨0, hpos⟩| := by rw [Pi.sub_apply]
      _ = ‖(z - w) ⟨0, hpos⟩‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖z - w‖ := norm_le_pi_norm (z - w) ⟨0, hpos⟩
  · exact (continuous_apply (⟨0, hpos⟩ : Fin n)).aestronglyMeasurable
  · exact ⟨(fun _ => 1), (fun _ => 0), by norm_num⟩

end QIQTH.CurvedA1HOffCollarTail

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedA1HOffCollarTail.curved_hOffCollarTail_at_gate
#print axioms QIQTH.CurvedA1HOffCollarTail.curved_hOffCollarTail_satisfiable
