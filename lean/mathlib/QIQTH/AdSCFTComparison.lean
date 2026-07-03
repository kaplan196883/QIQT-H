/-
  The AdS/CFT dictionary — algebraic consistency identities.

  ★ COMPARISON ARTIFACT — this is NOT a QIQT-H result, and NOT a formalization of the AdS/CFT
    (Maldacena) conjecture. ★

  ⚠ WHAT THIS IS NOT. Maldacena's correspondence (hep-th/9711200) — "type IIB string theory on
  AdS₅×S⁵ is dual to N=4 super-Yang–Mills" — is an UNPROVEN *conjecture* ("we conjecture … is
  dual to …", verbatim), about string theory, which is not rigorously defined. There is no theorem
  to prove; it is not formalizable. Nothing here proves, or claims to prove, the duality.

  ⚠ WHAT THIS IS. The *algebraic dictionary*: taking the physics results as EXPLICIT INPUTS
  (definitions/hypotheses) — the radius–coupling relation R⁴ = 4π g_s N α'², the Brown–Henneaux
  central charge c = 3ℓ/2G, the Cardy formula, and the BTZ↔CFT level identification — the machine-
  checked algebraic identities they entail. The centrepiece is Strominger's 1997 result: the CFT
  Cardy entropy of the BTZ black hole equals the Bekenstein–Hawking area law A/4G. These are pure
  real-number identities; the CFT / GR / string content is carried, never derived here.

  ⚠ WHY IT IS INTERESTING (the QIQT-H comparison). It makes concrete exactly what AdS/CFT DERIVES,
  *given its inputs*: (a) the bulk Newton constant G is fixed by the gauge degree-count N
  (G ∝ 1/N²), and (b) the black-hole entropy is reproduced as a boundary-CFT state count,
  S = A/4G, with the SAME G on both sides. Since the granularity reframing
  (`InducedNewtonConstant.lean`: G = 1/(N Λ_s²)), QIQT-H fixes G by a degree-count too — both
  sides derive G from a count against ONE carried scale (AdS/CFT: N² against α'; QIQT-H: N·Λ_s²
  against the granularity), and `HolographicBridge.lean` proves the two bookkeepings agree
  (Cardy = QIQT-H capacity exponent, ℓ cancelling). What AdS/CFT still has and QIQT-H lacks is
  the INDEPENDENT CROSS-CHECK: one microscopic system (the boundary CFT) computing both G and the
  microstate count, so S = A/4G is a consistency theorem of a single theory rather than two
  bookkeepings calibrated to the same primitives. This file is deliberately NOT wired into
  `QIQTH.lean` or the inventory — it is a labelled comparison, not a QIQT-H claim.
-/
import Mathlib

namespace AdSCFT

open Real

/-! ## 1. The radius–coupling relation (Maldacena hep-th/9711200): `R⁴/α'² = 4π g_s N = λ` -/

/-- The AdS₅ radius to the fourth power — Maldacena's `R⁴ = 4π g_s N α'²`
    (`alpha2 = α'²`). -/
noncomputable def adsRadiusPow4 (gs N alpha2 : ℝ) : ℝ := 4 * π * gs * N * alpha2

/-- **The AdS radius is fixed by the gauge data.** `R⁴/α'²` equals the 't Hooft coupling
    `λ = g_YM² N = 4π g_s N`. (Input relation; a pure algebraic identity.) -/
theorem adsRadius_eq_tHooft (gs N alpha2 : ℝ) (h : alpha2 ≠ 0) :
    adsRadiusPow4 gs N alpha2 / alpha2 = 4 * π * gs * N := by
  unfold adsRadiusPow4; field_simp

/-- **`1/G ∝ N²`** — "quantum effects in AdS₅×S⁵ have the interpretation of `1/N` effects in the
    gauge theory" (Maldacena). Modelling the bulk Newton constant as `G = κ/N²` with `κ` the fixed
    geometric/string data, the `N²` gauge degrees of freedom fix `G`: `G·N² = κ`, so `G → 0` as
    `N → ∞` (the classical-gravity limit). -/
noncomputable def newtonG_of_N (kappa N : ℝ) : ℝ := kappa / N ^ 2

theorem newtonG_scales_as_inv_Nsq (kappa N : ℝ) (hN : N ≠ 0) :
    newtonG_of_N kappa N * N ^ 2 = kappa := by
  unfold newtonG_of_N; field_simp

/-! ## 2. Brown–Henneaux + Cardy ⟹ BTZ entropy `= A/4G` (Strominger, 1997) -/

/-- **Brown–Henneaux central charge** `c = 3ℓ/2G` (an exact GR asymptotic-symmetry theorem;
    carried here as a defining INPUT, not re-derived). -/
noncomputable def bhCentralCharge (ell G : ℝ) : ℝ := 3 * ell / (2 * G)

/-- **The Cardy entropy** `S = 2π√(c·L₀/6) + 2π√(c̄·L̄₀/6)` — the asymptotic density of states of a
    2d CFT (the CFT INPUT; carried, not derived). -/
noncomputable def cardyEntropy (c cbar L0 L0bar : ℝ) : ℝ :=
  2 * π * Real.sqrt (c * L0 / 6) + 2 * π * Real.sqrt (cbar * L0bar / 6)

/-- **BTZ Virasoro levels** from the horizon radii `r₊, r₋` — the BTZ↔CFT identification (INPUT). -/
noncomputable def btzL0 (rp rm G ell : ℝ) : ℝ := (rp + rm) ^ 2 / (16 * G * ell)
noncomputable def btzL0bar (rp rm G ell : ℝ) : ℝ := (rp - rm) ^ 2 / (16 * G * ell)

/-- **Bekenstein–Hawking area law for BTZ**: horizon "area" (length) `A = 2π r₊`, entropy
    `S_BH = A/4G`. -/
noncomputable def btzArea (rp : ℝ) : ℝ := 2 * π * rp
noncomputable def bekensteinHawking (rp G : ℝ) : ℝ := btzArea rp / (4 * G)

/-- **Strominger (1997) — the CFT Cardy entropy of the BTZ black hole equals `A/4G`.**
    Given the Brown–Henneaux central charge (`c = c̄ = 3ℓ/2G`) and the BTZ↔CFT level identification,
    the boundary CFT microstate count reproduces the Bekenstein–Hawking area law, `S = A/4G` with
    `A = 2π r₊`.

    ⚠ A machine-checked ALGEBRAIC identity. The Cardy formula, the Brown–Henneaux central charge,
    and the BTZ dictionary are carried as definitions/inputs — this is NOT a proof of the AdS/CFT
    conjecture. It formalizes precisely what AdS/CFT *derives, given its inputs*: black-hole entropy
    as a boundary state count, with the same `G` on both sides — the thing QIQT-H does not supply. -/
theorem btz_cardy_eq_bekensteinHawking (rp rm G ell : ℝ)
    (hG : 0 < G) (hell : 0 < ell) (hrp : 0 ≤ rp) (hrm_lo : -rp ≤ rm) (hrm_hi : rm ≤ rp) :
    cardyEntropy (bhCentralCharge ell G) (bhCentralCharge ell G)
        (btzL0 rp rm G ell) (btzL0bar rp rm G ell)
      = bekensteinHawking rp G := by
  have hsum : (0 : ℝ) ≤ rp + rm := by linarith
  have hdiff : (0 : ℝ) ≤ rp - rm := by linarith
  have hpp : (0 : ℝ) ≤ (rp + rm) / (8 * G) := div_nonneg hsum (by positivity)
  have hpm : (0 : ℝ) ≤ (rp - rm) / (8 * G) := div_nonneg hdiff (by positivity)
  -- the Cardy square-root arguments are perfect squares:
  have e1 : bhCentralCharge ell G * btzL0 rp rm G ell / 6 = ((rp + rm) / (8 * G)) ^ 2 := by
    unfold bhCentralCharge btzL0; field_simp; ring
  have e2 : bhCentralCharge ell G * btzL0bar rp rm G ell / 6 = ((rp - rm) / (8 * G)) ^ 2 := by
    unfold bhCentralCharge btzL0bar; field_simp; ring
  unfold cardyEntropy bekensteinHawking btzArea
  rw [e1, e2, Real.sqrt_sq hpp, Real.sqrt_sq hpm]
  field_simp; ring

end AdSCFT
