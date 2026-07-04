/-
  A1 — THE REGULATOR RIGIDITY THEOREM (Track A of THE_TRANSPORT_AND_ACCOUNTING_PLAN.md).

  WHAT IS PROVED. The Sakharov/Dvali **form** of the induced inverse Newton constant,
      1/G = N_eff · Λ^κ,
  is FORCED, not posited: any per-species regulator contribution `F : ℝ → ℝ` that is
  (i) positive on positive cutoffs, (ii) covariant under cutoff rescaling with SOME
  (unknown!) factor `g c` — `F (c·Λ) = g c · F Λ` — and (iii) monotone in the cutoff,
  is necessarily a pure power `F Λ = F 1 · Λ^κ` with `κ ≥ 0` (`regulator_forced_power`).
  The exponent `κ` is an OUTPUT of the rigidity argument (via the held DS5 monotone
  log-valuation theorem `monotone_logValuation`), never an input: the covariance field
  quantifies over an arbitrary `g`, and `g c = c^κ` is DERIVED. One dimensional
  calibration point then pins `κ = 2` (`regulator_dimension_calibration`), and a finite
  species family sharing one regulator inherits the calibration from a SINGLE species,
  yielding the species sum `∑ᵢ Fᵢ Λ = N_eff · Λ²` with `N_eff = ∑ᵢ Fᵢ 1`
  (`speciesRegulator_forced`) — the Sakharov (1968) / Dvali species form.

  THE VACUITY GUARD. `dyadic_covariance_insufficient` exhibits a positive function with
  DYADIC covariance only (`F (2Λ) = 4·F Λ`) that is NOT of power form — so the full
  continuous covariance hypothesis is genuinely load-bearing, and the hypothesis bundle
  is not secretly equivalent to its conclusion. `toyRegulator` (F Λ = Λ²) shows the
  bundle is non-vacuously satisfiable and realizes the held species accounting:
  `effSpeciesN S · toyRegulator.F Λ = inducedInvG S Λ` (`InducedNewtonConstant.lean`).

  ⚠ WHAT STAYS CITED. The per-species coefficients `c_i` (Seeley–DeWitt a₁ data) and
  hence the numerical value of `N_eff` remain CITED, hand-entered data — exactly as in
  `InducedNewtonConstant.lean` and `SakharovRatio`. This module forces the FORM only;
  no numerical `G` is claimed.
-/
import Mathlib
import QIQTH.Rigidity.LogValuationReal
import QIQTH.InducedNewtonConstant

namespace QIQTH.Rigidity

/-- **A regulator family** — the `Λ`-dependence of one species' contribution to `1/G`.
    The three physical hypotheses: positivity on positive cutoffs; covariance under cutoff
    rescaling with SOME factor `g` (the factor is existentially quantified and otherwise
    UNKNOWN — the power law `g c = c^κ` must come OUT); monotonicity in the cutoff. -/
structure RegulatorFamily where
  /-- the species' contribution to `1/G` as a function of the cutoff `Λ` -/
  F : ℝ → ℝ
  /-- positivity on positive cutoffs -/
  pos : ∀ Λ, 0 < Λ → 0 < F Λ
  /-- rescaling covariance with an UNKNOWN factor `g` (never posited to be a power) -/
  covariant : ∃ g : ℝ → ℝ, ∀ c, 0 < c → ∀ Λ, 0 < Λ → F (c * Λ) = g c * F Λ
  /-- monotonicity in the cutoff -/
  mono : ∀ Λ Λ', 0 < Λ → Λ ≤ Λ' → F Λ ≤ F Λ'

/-- **THE REGULATOR RIGIDITY THEOREM** — the power FORM is forced. Any regulator family
    is a pure power of the cutoff: `F Λ = F 1 · Λ^κ` with `κ ≥ 0`. The exponent `κ` is an
    OUTPUT: the additive shadow `A x = log F x − log F 1` of the covariance factor is a
    monotone multiplicative-to-additive valuation, hence `κ·log` by the held DS5 rigidity
    (`monotone_logValuation`). -/
theorem regulator_forced_power (R : RegulatorFamily) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ Λ, 0 < Λ → R.F Λ = R.F 1 * Λ ^ κ := by
  obtain ⟨g, hg⟩ := R.covariant
  have hF1 : 0 < R.F 1 := R.pos 1 one_pos
  -- the additive shadow `A x = log (F x) − log (F 1)` is additive on positives …
  have hmul : ∀ x y, 0 < x → 0 < y →
      (Real.log (R.F (x * y)) - Real.log (R.F 1))
        = (Real.log (R.F x) - Real.log (R.F 1))
          + (Real.log (R.F y) - Real.log (R.F 1)) := by
    intro x y hx hy
    have hFx : 0 < R.F x := R.pos x hx
    have hFy : 0 < R.F y := R.pos y hy
    have hFxy : 0 < R.F (x * y) := R.pos _ (mul_pos hx hy)
    -- specialize covariance at `Λ = 1`: `g x · F 1 = F x`
    have hgx : g x * R.F 1 = R.F x := by
      have h := hg x hx 1 one_pos
      rw [mul_one] at h
      exact h.symm
    have hkey : R.F (x * y) * R.F 1 = R.F x * R.F y := by
      have h1 : R.F (x * y) = g x * R.F y := hg x hx y hy
      calc R.F (x * y) * R.F 1 = g x * R.F 1 * R.F y := by rw [h1]; ring
        _ = R.F x * R.F y := by rw [hgx]
    have hlog := congrArg Real.log hkey
    rw [Real.log_mul hFxy.ne' hF1.ne', Real.log_mul hFx.ne' hFy.ne'] at hlog
    linarith
  -- … and monotone (from monotonicity of `F` and of `log` on positives)
  have hmono : ∀ x y, 0 < x → x ≤ y →
      Real.log (R.F x) - Real.log (R.F 1)
        ≤ Real.log (R.F y) - Real.log (R.F 1) := by
    intro x y hx hxy
    have := Real.log_le_log (R.pos x hx) (R.mono x y hx hxy)
    linarith
  -- the held DS5 rigidity delivers `κ`
  obtain ⟨κ, hκ0, hA⟩ := monotone_logValuation
    (fun x => Real.log (R.F x) - Real.log (R.F 1)) hmul hmono
  refine ⟨κ, hκ0, fun Λ hΛ => ?_⟩
  have hFΛ : 0 < R.F Λ := R.pos Λ hΛ
  have h1 : Real.log (R.F Λ) - Real.log (R.F 1) = κ * Real.log Λ := hA Λ hΛ
  have h2 : Real.log (R.F Λ) = Real.log (R.F 1) + κ * Real.log Λ := by linarith
  calc R.F Λ = Real.exp (Real.log (R.F Λ)) := (Real.exp_log hFΛ).symm
    _ = Real.exp (Real.log (R.F 1)) * Real.exp (κ * Real.log Λ) := by
        rw [h2, Real.exp_add]
    _ = R.F 1 * Λ ^ κ := by
        rw [Real.exp_log hF1, Real.rpow_def_of_pos hΛ, mul_comm (Real.log Λ) κ]

/-- **Dimensional calibration** — ONE calibration point pins the exponent. If the forced
    power matches the quadratic cutoff scaling at a single `c₀ > 1`, then `κ = 2`
    everywhere: `F Λ = F 1 · Λ²` for all positive cutoffs. -/
theorem regulator_dimension_calibration (R : RegulatorFamily) (c₀ : ℝ) (hc₀ : 1 < c₀)
    (hcal : R.F c₀ = R.F 1 * c₀ ^ (2 : ℝ)) :
    ∀ Λ, 0 < Λ → R.F Λ = R.F 1 * Λ ^ (2 : ℝ) := by
  obtain ⟨κ, _hκ0, hpow⟩ := regulator_forced_power R
  have hc₀pos : (0 : ℝ) < c₀ := one_pos.trans hc₀
  have hF1 : 0 < R.F 1 := R.pos 1 one_pos
  have h2 : c₀ ^ κ = c₀ ^ (2 : ℝ) :=
    mul_left_cancel₀ hF1.ne' (by rw [← hpow c₀ hc₀pos, hcal])
  have hlog : κ * Real.log c₀ = 2 * Real.log c₀ := by
    have h := congrArg Real.log h2
    rwa [Real.log_rpow hc₀pos, Real.log_rpow hc₀pos] at h
  have hκ2 : κ = 2 := mul_right_cancel₀ (ne_of_gt (Real.log_pos hc₀)) hlog
  intro Λ hΛ
  rw [← hκ2]
  exact hpow Λ hΛ

/-- **THE SPECIES FORM IS FORCED** (Sakharov/Dvali). For a finite family of regulator
    families sharing ONE covariance factor `g` (the shared-regulator condition), a single
    calibration point on a SINGLE species `i₀` pins every species, and the total
    `1/G = ∑ᵢ Fᵢ Λ` takes the Sakharov/Dvali form `N_eff · Λ²` with `N_eff = ∑ᵢ Fᵢ 1`.
    The `N_eff` numbers (the per-species `c_i` coefficients) stay CITED data. -/
theorem speciesRegulator_forced {n : ℕ} (Fam : Fin n → RegulatorFamily) (g : ℝ → ℝ)
    (hshared : ∀ i : Fin n, ∀ c, 0 < c → ∀ Λ, 0 < Λ →
      (Fam i).F (c * Λ) = g c * (Fam i).F Λ)
    (i₀ : Fin n) (c₀ : ℝ) (hc₀ : 1 < c₀)
    (hcal : (Fam i₀).F c₀ = (Fam i₀).F 1 * c₀ ^ (2 : ℝ)) :
    ∀ Λ, 0 < Λ → ∑ i, (Fam i).F Λ = (∑ i, (Fam i).F 1) * Λ ^ (2 : ℝ) := by
  intro Λ hΛ
  have hF1i₀ : 0 < (Fam i₀).F 1 := (Fam i₀).pos 1 one_pos
  have hi₀ := regulator_dimension_calibration (Fam i₀) c₀ hc₀ hcal Λ hΛ
  -- the calibrated species reveals the shared factor: `g Λ = Λ²`
  have hgΛ : g Λ = Λ ^ (2 : ℝ) := by
    have h := hshared i₀ Λ hΛ 1 one_pos
    rw [mul_one] at h
    have h3 : g Λ * (Fam i₀).F 1 = Λ ^ (2 : ℝ) * (Fam i₀).F 1 := by
      rw [← h, hi₀]; ring
    exact mul_right_cancel₀ hF1i₀.ne' h3
  -- … which transports the calibration to EVERY species
  have hper : ∀ i : Fin n, (Fam i).F Λ = (Fam i).F 1 * Λ ^ (2 : ℝ) := fun i => by
    have h := hshared i Λ hΛ 1 one_pos
    rw [mul_one, hgΛ] at h
    rw [h]; ring
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => hper i

/-! ## The vacuity guard: weakened covariance does NOT force the power form -/

/-- The dyadic witness `Λ² · (2 + sin(2π·log₂ Λ))` — positive, dyadically covariant
    (`F (2Λ) = 4·F Λ`), but NOT a pure power. -/
noncomputable def dyadicWitness (Λ : ℝ) : ℝ :=
  Λ ^ 2 * (2 + Real.sin (2 * Real.pi * Real.log Λ / Real.log 2))

theorem dyadicWitness_pos (Λ : ℝ) (hΛ : 0 < Λ) : 0 < dyadicWitness Λ := by
  have hs := Real.neg_one_le_sin (2 * Real.pi * Real.log Λ / Real.log 2)
  have h2 : (0 : ℝ) < 2 + Real.sin (2 * Real.pi * Real.log Λ / Real.log 2) := by linarith
  exact mul_pos (pow_pos hΛ 2) h2

theorem dyadicWitness_dyadic (Λ : ℝ) (hΛ : 0 < Λ) :
    dyadicWitness (2 * Λ) = 4 * dyadicWitness Λ := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have harg : 2 * Real.pi * Real.log (2 * Λ) / Real.log 2
      = 2 * Real.pi * Real.log Λ / Real.log 2 + 2 * Real.pi := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hΛ.ne']
    field_simp
    ring
  unfold dyadicWitness
  rw [harg, Real.sin_add_two_pi]
  ring

/-- **Dyadic covariance is INSUFFICIENT** — the honest witness that the CONTINUOUS
    covariance hypothesis of `RegulatorFamily` is load-bearing: there is a positive
    function with dyadic covariance (`F (2Λ) = 4·F Λ`) that is NOT of the form
    `F 1 · Λ^κ` for any `κ`. (Positivity + dyadic covariance alone do not force the
    power form; the rigidity theorem is not vacuously true.) -/
theorem dyadic_covariance_insufficient :
    ∃ F : ℝ → ℝ,
      (∀ Λ, 0 < Λ → 0 < F Λ) ∧
      (∀ Λ, 0 < Λ → F (2 * Λ) = 4 * F Λ) ∧
      ¬ ∃ κ : ℝ, ∀ Λ, 0 < Λ → F Λ = F 1 * Λ ^ κ := by
  refine ⟨dyadicWitness, dyadicWitness_pos, dyadicWitness_dyadic, ?_⟩
  rintro ⟨κ, hκ⟩
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  -- F 1 = 2
  have hF1 : dyadicWitness 1 = 2 := by
    unfold dyadicWitness
    rw [Real.log_one]
    norm_num
  -- F 2 = 8
  have hF2 : dyadicWitness 2 = 8 := by
    unfold dyadicWitness
    rw [mul_div_assoc, div_self hlog2, mul_one, Real.sin_two_pi]
    norm_num
  -- the quarter point Λ₀ = 2^(1/4): sin(π/2) = 1 sticks out of any power form
  set Λ₀ : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4) with hΛ₀def
  have hΛ₀pos : 0 < Λ₀ := Real.rpow_pos_of_pos two_pos _
  have hlogΛ₀ : Real.log Λ₀ = (1 / 4) * Real.log 2 := Real.log_rpow two_pos _
  have hΛ₀sq : Λ₀ ^ 2 = Real.sqrt 2 := by
    rw [hΛ₀def, ← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ) / 4)) 2,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow]
    norm_num
  have hFΛ₀ : dyadicWitness Λ₀ = 3 * Real.sqrt 2 := by
    unfold dyadicWitness
    have harg : 2 * Real.pi * Real.log Λ₀ / Real.log 2 = Real.pi / 2 := by
      rw [hlogΛ₀]
      field_simp
      ring
    rw [harg, Real.sin_pi_div_two, hΛ₀sq]
    ring
  -- the power form at Λ = 2 forces 2^κ = 4 …
  have h2κ : (2:ℝ) ^ κ = 4 := by
    have h := hκ 2 two_pos
    rw [hF2, hF1] at h
    linarith
  -- … hence Λ₀^κ = 4^(1/4) = √2
  have h4 : (2:ℝ) ^ (2:ℝ) = 4 := by
    norm_num
  have hΛ₀κ : Λ₀ ^ κ = Real.sqrt 2 := by
    rw [hΛ₀def, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), h2κ, ← h4,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow]
    norm_num
  -- contradiction: 3√2 = 2√2
  have hcontra := hκ Λ₀ hΛ₀pos
  rw [hFΛ₀, hF1, hΛ₀κ] at hcontra
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  linarith

/-! ## Non-vacuity: the held toy realizes the hypothesis bundle -/

/-- **Non-vacuity witness** `F Λ = Λ²` (with covariance factor `g c = c²`): all three
    `RegulatorFamily` hypotheses hold. This is exactly the shape of the held species
    accounting `inducedInvG S Λ = effSpeciesN S · Λ²` (`InducedNewtonConstant.lean`),
    so the axioms are realized by the QIQT-H induced-gravity toy. -/
noncomputable def toyRegulator : RegulatorFamily where
  F := fun Λ => Λ ^ 2
  pos := fun _Λ hΛ => pow_pos hΛ 2
  covariant := ⟨fun c => c ^ 2, fun c _hc Λ _hΛ => by ring⟩
  mono := fun Λ Λ' hΛ hle => by nlinarith

/-- The toy regulator realizes the held species accounting: scaling by the (CITED)
    effective species number `N_eff = effSpeciesN S` gives exactly `inducedInvG S Λ`. -/
theorem toyRegulator_realizes_inducedInvG (S : QIQTH.InducedG.SpeciesContent) (Λ : ℝ) :
    QIQTH.InducedG.effSpeciesN S * toyRegulator.F Λ = QIQTH.InducedG.inducedInvG S Λ := rfl

end QIQTH.Rigidity
