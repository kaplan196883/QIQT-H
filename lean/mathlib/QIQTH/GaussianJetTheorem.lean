/-
  GaussianJetTheorem — J4-322: the ON-GATE / OFF-GATE GAUSSIAN JET DICHOTOMY (`hGateData`/`hGateData'`,
  the B5 pair of the `hCConv` facade) — the satisfiability VERDICT + the bankable scalar workhorses.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is one
  brick of the `a₁ = R/6` heat-kernel campaign.  NO `sorry` (prose excepted), NO new axioms, NO
  `:= True`, NO vacuous / unsatisfiable hypotheses in this file's OWN theorems.  No existing file is
  edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (G0) THE RECON — the EXACT `hGateData` RHS and the SATISFIABILITY VERDICT.

  ### The field (VERBATIM from `QIQTH.CConvFacade.CConvEnvelopeData`, lines 157-169; and its
  ### quantifier-swapped twin `hGateData'`, lines 170-182):

    hGateData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∉ K ∨
          (∃ Pval : Fin n → ℝ,
            z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
            (∀ k, HasDerivAt (fun r ↦ uniformInverseChart g gi hC hK z (update x i r) k) (Pval k) (x i)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b (t-s) z) i x ∧
            |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2*(t-s)))| ≤ Bs ∧   -- (‡)
            |chartFieldAmp g gi hC hK a b (t-s) z x| ≤ Ba ∧
            |pd (chartFieldAmp g gi hC hK a b (t-s) z) i x| ≤ Bd ∧
            (1/2) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))

  ### What the three constants bound.  The witness field-slot derivative is (`EngineInstantiation`,
  `HenvUInstantiation`, `G2CarryDischarge.witnessFieldDeriv_gate_envelope_coercive`):
      witnessFieldDeriv = (∂ᵢ log G)·G·amp + G·∂ᵢamp,   G := gaussDdim (t-s) (W_z x),
  and the coercive envelope bounds it by `(Bs·Ba+Bd)·(√2)ⁿ · gaussDdim (2(t-s)) z`, where
      Bs  ≥ |∂ᵢ log G| = |(-(∑ₖ Wₖ · Pvalₖ))/(2(t-s))|   ← the conjunct (‡),
      Ba  ≥ |amp|,   Bd ≥ |∂ᵢ amp|.
  Here `Wₖ = uniformInverseChart … z x k`, `Pvalₖ = ∂ᵢ Wₖ` (the chart Jacobian column, `s`-INDEPENDENT),
  so  ∑ₖ Wₖ Pvalₖ = ½ ∂ᵢ‖W_z x‖² = ½ ∂ᵢ (rncRadialSq (W_z x))  — the log-gradient of the Gaussian.

  ### ⚠⚠  THE VERDICT: **UNSATISFIABLE (FALSE) at any nonempty gate.**  THE `s`-POWER ACCOUNTING.

    • gaussDdim τ v = (4πτ)^{-n/2} · exp(−‖v‖²/(4τ)),  τ := t−s   (`FlatHeatEquation.gaussDdim`,
      `rncRadialSq v = ∑ vₖ²`).  So the VALUE bound RHS `gaussDdim (2(t-s)) z` carries the prefactor
      `τ^{-n/2}` (`s`-power −n/2) and the exponent `−‖z‖²/(8τ)`.

    • The conjunct (‡) demands a **CONSTANT** `Bs` (`s`-power 0) for the bare log-gradient
      `|∂ᵢ log G| = |∑ₖ Wₖ Pvalₖ| / (2τ)`.  On-gate ‖W_z x‖ < c is BOUNDED and the numerator
      `∑ₖ Wₖ Pvalₖ = ½ ∂ᵢ‖W_z x‖²` is `s`-INDEPENDENT and generically ≠ 0.  Hence
          |∂ᵢ log G| = |numerator| / (2(t−s))  →  +∞   as  s → t⁻,
      and the blow-up region `s ∈ (t−ε, t)` has POSITIVE `volume`.  So NO constant `Bs` works and
      `∀ᵐ s` cannot escape it.  The **true** cost of the first (spatial) derivative is `(t−s)^{-1/2}`
      (the standard heat-kernel gradient estimate `|∇ₓG_τ| ≤ C·τ^{-1/2}·G_{2τ}`, see brick β below),
      NOT `(t−s)^0`.  The facade demands `s`-power 0 where `s`-power −1/2 is FORCED.

    • CONSEQUENTLY the fixed-`C` value bound `|witnessFieldDeriv| ≤ C·gaussDdim(2τ)z` is ALSO false
      (off by an intrinsic `τ^{-1/2}`).  `HenvUInstantiation.henvU_assembled` is a TRUE implication with
      an UNSATISFIABLE antecedent — precisely the `∀S/hFbd` FACADE-ARTEFACT pattern (a valid entailment
      whose hypothesis is forced empty at the concrete instantiation).  This is a RESULT, not a failure.

    §2 (`gateData_numerator_shape_unsat`) encodes the verdict as a Lean impossibility theorem
    (parallel to `HgateSatAudit.gate_Sconj_impossible`, but for the `τ→0` poison, not the
    S-membership poison).  Every hypothesis there is genuinely SATISFIABLE.

  ### THE HONEST FIX (the SATISFIABLE facade-variant, PROSE — see §3).  Replace the per-factor decomposition
  by the `(t−s)^{-1/2}`-weighted VALUE-level Gaussian domination (still `s`-integrable on `(0,t)`,
  since `∫₀ᵗ (t−s)^{-1/2} ds < ∞`, so it suffices for the downstream `∫₀ᵗ` differentiation-under-∫):
      |witnessFieldDeriv g gi hC hK S a b i (t−s) x z| ≤ C · (t−s)^{-1/2} · gaussDdim (2(t−s)) z    (⋆)
  with the off-gate `z ∉ K` branch giving `0`.  The scalar CORE of (⋆) is brick β (`gaussian_beats_linear`)
  below: `r·s⁻¹·exp(−a r²/s) ≤ C·s^{-1/2}·exp(−a′ r²/s)` — the `s^{-1/2}` is UNAVOIDABLE and appears
  EXPLICITLY, confirming the verdict.

  ## (G1) BRICK β — the scalar "Gaussian beats polynomial" workhorses (pure real analysis; BANKED
      regardless of the verdict).
    • `mul_exp_neg_le_one`        : u·exp(−u) ≤ 1                    (u·e^{−u} maximizer, crude).
    • `mul_exp_neg_sq_le_half`    : y·exp(−y²) ≤ ½                   (x·e^{−x²} maximizer, crude).
    • `mul_exp_neg_mul_sq_le`     : y·exp(−d y²) ≤ 1/(2√d)           (d>0; the rescaled maximizer).
    • `one_add_mul_exp_neg_le`    : (1+p)·exp(−d p) ≤ (d+1)/d        (d>0, p≥0).
    • `gaussian_beats_linear`     : r·s⁻¹·exp(−a r²/s) ≤ (1/(2√(a−a′)))·s^{-1/2}·exp(−a′ r²/s)   [β1].
    • `gaussian_beats_quadratic`  : (s⁻¹+r²s⁻²)·exp(−a r²/s) ≤ ((a−a′+1)/(a−a′))·s⁻¹·exp(−a′ r²/s)  [β2].
  β1 is the heat-kernel FIRST-derivative estimate (`s^{-1/2}` on the RHS — the load-bearing `s`-power);
  β2 is the SECOND-derivative estimate (`s⁻¹`).  These are the workhorses the TRUE bound (⋆) is built on.

  ## (G2/G3) status.  The verdict is NEGATIVE, so brick α (the chart two-sided comparison) and brick γ
  (the assembly) toward the FALSE `hGateData` are moot; the deliverable is §2 (the Lean falsification)
  + the TRUE `(t−s)^{-1/2}` scalar estimate (β1) + the corrected facade-variant statement (⋆) above.

  NOT `a₁ = R/6`.
-/
import Mathlib

open MeasureTheory Filter
open scoped Topology BigOperators

namespace QIQTH.GaussianJetTheorem

/-! ###############################################################################
    ### §1 — BRICK β : the scalar "Gaussian beats polynomial" absorption lemmas.
    ###        Pure real analysis; no project dependencies.  BANKED regardless of verdict.
    ############################################################################### -/

/-- **`mul_exp_neg_le_one`.**  `u·exp(−u) ≤ 1` for every real `u` (crude `u·e^{−u}` bound).  From
    `u ≤ exp u` (`Real.add_one_le_exp`).  NOT `a₁ = R/6`. -/
theorem mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos u)]
  linarith [Real.add_one_le_exp u]

/-- **`mul_exp_neg_sq_le_half`.**  `y·exp(−y²) ≤ ½` for every real `y` (crude `x·e^{−x²}` maximizer).
    For `y ≤ 0` the LHS is `≤ 0`; for `y > 0` use `2y ≤ y²+1 ≤ exp(y²)`.  NOT `a₁ = R/6`. -/
theorem mul_exp_neg_sq_le_half (y : ℝ) : y * Real.exp (-y ^ 2) ≤ 1 / 2 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [Real.add_one_le_exp (y ^ 2), sq_nonneg (y - 1)]

/-- **`mul_exp_neg_mul_sq_le`.**  `y·exp(−d y²) ≤ 1/(2√d)` for `d > 0`, every real `y` (the rescaled
    maximizer, substitute `w = √d·y`).  NOT `a₁ = R/6`. -/
theorem mul_exp_neg_mul_sq_le (d : ℝ) (hd : 0 < d) (y : ℝ) :
    y * Real.exp (-(d * y ^ 2)) ≤ 1 / (2 * Real.sqrt d) := by
  have hsqd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hne : Real.sqrt d ≠ 0 := ne_of_gt hsqd
  have hsqd2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hEeq : Real.exp (-(d * y ^ 2)) = Real.exp (-((Real.sqrt d * y) ^ 2)) := by
    rw [show -(d * y ^ 2) = -((Real.sqrt d * y) ^ 2) from by rw [mul_pow, hsqd2]]
  rw [hEeq]
  have hfac : y * Real.exp (-((Real.sqrt d * y) ^ 2))
      = (Real.sqrt d)⁻¹ * ((Real.sqrt d * y) * Real.exp (-((Real.sqrt d * y) ^ 2))) := by
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqd), one_mul]
  rw [hfac]
  calc (Real.sqrt d)⁻¹ * ((Real.sqrt d * y) * Real.exp (-((Real.sqrt d * y) ^ 2)))
      ≤ (Real.sqrt d)⁻¹ * (1 / 2) :=
        mul_le_mul_of_nonneg_left (mul_exp_neg_sq_le_half (Real.sqrt d * y)) (inv_nonneg.mpr hsqd.le)
    _ = 1 / (2 * Real.sqrt d) := by rw [mul_one_div]; field_simp

/-- **`one_add_mul_exp_neg_le`.**  `(1+p)·exp(−d p) ≤ (d+1)/d` for `d > 0`, `p ≥ 0`.  Splits as
    `exp(−dp) ≤ 1` plus `p·exp(−dp) ≤ 1/d` (from `u·e^{−u} ≤ 1` at `u = dp`).  NOT `a₁ = R/6`. -/
theorem one_add_mul_exp_neg_le (d : ℝ) (hd : 0 < d) (p : ℝ) (hp : 0 ≤ p) :
    (1 + p) * Real.exp (-(d * p)) ≤ (d + 1) / d := by
  have h1 : Real.exp (-(d * p)) ≤ 1 := by
    have hle : -(d * p) ≤ 0 := by linarith [mul_nonneg hd.le hp]
    calc Real.exp (-(d * p)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
      _ = 1 := Real.exp_zero
  have h2 : p * Real.exp (-(d * p)) ≤ 1 / d := by
    have key := mul_exp_neg_le_one (d * p)
    have hmul : (1 / d) * ((d * p) * Real.exp (-(d * p))) ≤ (1 / d) * 1 :=
      mul_le_mul_of_nonneg_left key (by positivity)
    rw [show (1 / d) * ((d * p) * Real.exp (-(d * p))) = p * Real.exp (-(d * p)) from by
          rw [one_div, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hd), one_mul],
        mul_one] at hmul
    exact hmul
  calc (1 + p) * Real.exp (-(d * p))
      = Real.exp (-(d * p)) + p * Real.exp (-(d * p)) := by ring
    _ ≤ 1 + 1 / d := add_le_add h1 h2
    _ = (d + 1) / d := by field_simp

/-- **★ `gaussian_beats_linear` (brick β1) — the heat-kernel FIRST-derivative estimate.**  For `a′ < a`,
    `s > 0`, every real `r`:
        `r · s⁻¹ · exp(−a r²/s)  ≤  (1/(2√(a−a′))) · s^{-1/2} · exp(−a′ r²/s)`.
    The Gaussian log-gradient `r·s⁻¹·exp(−a r²/s)` (the `∂ᵢ log G` × `G` shape) costs an EXPLICIT
    `s^{-1/2}` — the load-bearing `s`-power the facade's `hGateData` (‡) illegitimately drops.
    Proof: split `exp(−a r²/s) = exp(−a′ r²/s)·exp(−(a−a′)r²/s)`, reduce to `y·exp(−(a−a′)y²) ≤
    1/(2√(a−a′))` with `y = r/√s` (`mul_exp_neg_mul_sq_le`).  NOT `a₁ = R/6`. -/
theorem gaussian_beats_linear (a a' : ℝ) (haa' : a' < a) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    r * s⁻¹ * Real.exp (-(a * r ^ 2 / s))
      ≤ (1 / (2 * Real.sqrt (a - a'))) * (Real.sqrt s)⁻¹ * Real.exp (-(a' * r ^ 2 / s)) := by
  have hd0 : 0 < a - a' := by linarith
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hexp : Real.exp (-(a * r ^ 2 / s))
      = Real.exp (-(a' * r ^ 2 / s)) * Real.exp (-((a - a') * r ^ 2 / s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsinv : s⁻¹ = (Real.sqrt s)⁻¹ * (Real.sqrt s)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hs.le]
  have hsq : ((Real.sqrt s)⁻¹) ^ 2 = s⁻¹ := by rw [sq, ← hsinv]
  set y := r * (Real.sqrt s)⁻¹ with hydef
  have hrs : r * s⁻¹ = y * (Real.sqrt s)⁻¹ := by rw [hydef, hsinv]; ring
  have hexpo : (a - a') * r ^ 2 / s = (a - a') * y ^ 2 := by
    rw [hydef, mul_pow, hsq]; ring
  have hred : r * s⁻¹ * Real.exp (-((a - a') * r ^ 2 / s))
      ≤ (1 / (2 * Real.sqrt (a - a'))) * (Real.sqrt s)⁻¹ := by
    rw [hrs, hexpo, mul_comm (1 / (2 * Real.sqrt (a - a'))) ((Real.sqrt s)⁻¹),
      show y * (Real.sqrt s)⁻¹ * Real.exp (-((a - a') * y ^ 2))
        = (Real.sqrt s)⁻¹ * (y * Real.exp (-((a - a') * y ^ 2))) from by ring]
    exact mul_le_mul_of_nonneg_left (mul_exp_neg_mul_sq_le (a - a') hd0 y) (inv_nonneg.mpr hsqs.le)
  calc r * s⁻¹ * Real.exp (-(a * r ^ 2 / s))
      = (r * s⁻¹ * Real.exp (-((a - a') * r ^ 2 / s))) * Real.exp (-(a' * r ^ 2 / s)) := by
        rw [hexp]; ring
    _ ≤ ((1 / (2 * Real.sqrt (a - a'))) * (Real.sqrt s)⁻¹) * Real.exp (-(a' * r ^ 2 / s)) :=
        mul_le_mul_of_nonneg_right hred (Real.exp_pos _).le
    _ = (1 / (2 * Real.sqrt (a - a'))) * (Real.sqrt s)⁻¹ * Real.exp (-(a' * r ^ 2 / s)) := by ring

/-- **★ `gaussian_beats_quadratic` (brick β2) — the heat-kernel SECOND-derivative estimate.**  For
    `a′ < a`, `s > 0`, every `r`:
        `(s⁻¹ + r²·s⁻²) · exp(−a r²/s)  ≤  ((a−a′+1)/(a−a′)) · s⁻¹ · exp(−a′ r²/s)`.
    The second-derivative polynomial `s⁻¹ + r² s⁻²` is absorbed against the Gaussian with cost `s⁻¹`.
    Proof: factor `s⁻¹`, reduce to `(1+p)·exp(−(a−a′)p) ≤ (a−a′+1)/(a−a′)` with `p = r²/s`
    (`one_add_mul_exp_neg_le`).  NOT `a₁ = R/6`. -/
theorem gaussian_beats_quadratic (a a' : ℝ) (haa' : a' < a) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (s⁻¹ + r ^ 2 * (s ^ 2)⁻¹) * Real.exp (-(a * r ^ 2 / s))
      ≤ ((a - a' + 1) / (a - a')) * s⁻¹ * Real.exp (-(a' * r ^ 2 / s)) := by
  have hd0 : 0 < a - a' := by linarith
  have hexp : Real.exp (-(a * r ^ 2 / s))
      = Real.exp (-(a' * r ^ 2 / s)) * Real.exp (-((a - a') * r ^ 2 / s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hred : (s⁻¹ + r ^ 2 * (s ^ 2)⁻¹) * Real.exp (-((a - a') * r ^ 2 / s))
      ≤ ((a - a' + 1) / (a - a')) * s⁻¹ := by
    have hp0 : 0 ≤ r ^ 2 / s := div_nonneg (sq_nonneg r) hs.le
    have hfac1 : s⁻¹ + r ^ 2 * (s ^ 2)⁻¹ = s⁻¹ * (1 + r ^ 2 / s) := by
      field_simp
    have hfac2 : (a - a') * r ^ 2 / s = (a - a') * (r ^ 2 / s) := by ring
    rw [hfac1, hfac2, mul_assoc, mul_comm (((a - a') + 1) / (a - a')) s⁻¹]
    exact mul_le_mul_of_nonneg_left
      (one_add_mul_exp_neg_le (a - a') hd0 (r ^ 2 / s) hp0) (by positivity)
  calc (s⁻¹ + r ^ 2 * (s ^ 2)⁻¹) * Real.exp (-(a * r ^ 2 / s))
      = ((s⁻¹ + r ^ 2 * (s ^ 2)⁻¹) * Real.exp (-((a - a') * r ^ 2 / s)))
          * Real.exp (-(a' * r ^ 2 / s)) := by rw [hexp]; ring
    _ ≤ (((a - a' + 1) / (a - a')) * s⁻¹) * Real.exp (-(a' * r ^ 2 / s)) :=
        mul_le_mul_of_nonneg_right hred (Real.exp_pos _).le
    _ = ((a - a' + 1) / (a - a')) * s⁻¹ * Real.exp (-(a' * r ^ 2 / s)) := by ring

/-! ###############################################################################
    ### §2 — THE VERDICT AS A LEAN IMPOSSIBILITY THEOREM (the `τ→0` poison).
    ###
    ### Parallel to `HgateSatAudit.gate_Sconj_impossible` (which refuted the S-membership-as-conclusion
    ### poison), this refutes the DISTINCT `τ→0` poison of the `hGateData` conjunct (‡):  a CONSTANT `Bs`
    ### cannot bound `|numerator / (2(t−s))|` on-gate, because the numerator `N z := ∑ₖ Wₖ Pvalₖ` is
    ### `s`-INDEPENDENT and generically nonzero, so the quotient blows up on a POSITIVE-measure `s`-set as
    ### `s → t⁻`.  All hypotheses are SATISFIABLE (a positive-measure gate subset on which `|N| ≥ c > 0`
    ### is the generic chart non-degeneracy).
    ############################################################################### -/

/-- **★★★ `gateData_numerator_shape_unsat` — the exact `hGateData` conjunct (‡) is UNSATISFIABLE at a
    nonempty gate.**  Fully GENERIC in the field measure space `(α, μ)`.  Take any measurable-space `α`,
    a base set `K`, an `s`-independent "numerator" `N : α → ℝ` (the on-gate `∑ₖ Wₖ Pvalₖ = ½ ∂ᵢ‖W_z·‖²`
    at a fixed field point), and a POSITIVE-measure subset `A ⊆ K` on which `|N| ≥ c > 0`.  Then NO
    constant `Bs ≥ 0` can validate the `∀ᵐ s → ∀ᵐ z` on-gate/off-gate dichotomy shape
        `∀ᵐ s, s ∈ uIoc 0 t → ∀ᵐ z, z ∉ K ∨ |(-(N z)) / (2(t−s))| ≤ Bs`.
    Proof: for `s ∈ Ioo (t−δ) t` (`δ := min (t/2) (c/(2(Bs+1))) > 0`, a positive-`volume` interval), on
    every `z ∈ A` one has `z ∈ K` and `|(-(N z))/(2(t−s))| = |N z|/(2(t−s)) ≥ c/(2(t−s)) > Bs`, so the
    inner `∀ᵐ z` fails on the positive-measure set `A`; hence the inner ae is false on a positive-`volume`
    `s`-set, contradicting the outer ae.  This is the `s`-power−0-vs-`s`-power−1/2 FACADE ARTEFACT made
    into a theorem.  NOT `a₁ = R/6`. -/
theorem gateData_numerator_shape_unsat {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (t Bs : ℝ) (ht : 0 < t) (hBs : 0 ≤ Bs)
    (K : Set α) (N : α → ℝ) (A : Set α)
    (hApos : 0 < μ A) (hAK : A ⊆ K)
    (c : ℝ) (hc : 0 < c) (hNlb : ∀ z ∈ A, c ≤ |N z|) :
    ¬ (∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t → ∀ᵐ z ∂μ,
        z ∉ K ∨ |(-(N z)) / (2 * (t - s))| ≤ Bs) := by
  intro h
  have hBs1 : (0 : ℝ) < Bs + 1 := by linarith
  set δ : ℝ := min (t / 2) (c / (2 * (Bs + 1))) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδc : δ ≤ c / (2 * (Bs + 1)) := min_le_right _ _
  have hδt : δ ≤ t / 2 := min_le_left _ _
  -- key: `(Bs+1)*(2δ) ≤ c`.
  have hprod : (Bs + 1) * (2 * δ) ≤ c := by
    rw [le_div_iff₀ (by positivity)] at hδc
    nlinarith [hδc]
  -- the bad `s`-interval `Ioo (t-δ) t` lies in the outer-ae null set.
  have hbad : Set.Ioo (t - δ) t ⊆
      {s : ℝ | ¬ (s ∈ Set.uIoc 0 t → ∀ᵐ z ∂μ, z ∉ K ∨ |(-(N z)) / (2 * (t - s))| ≤ Bs)} := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have htδpos : 0 < t - δ := by linarith
    have hspos : 0 < s := lt_trans htδpos hs1
    have h2ts : 0 < 2 * (t - s) := by linarith
    have hsmem : s ∈ Set.uIoc 0 t := by rw [Set.uIoc_of_le ht.le]; exact ⟨hspos, hs2.le⟩
    -- for each `z ∈ A`, the on/off dichotomy FAILS.
    have hzfail : ∀ z ∈ A, ¬ (z ∉ K ∨ |(-(N z)) / (2 * (t - s))| ≤ Bs) := by
      intro z hzA
      have hzK : z ∈ K := hAK hzA
      have hbig : Bs < |(-(N z)) / (2 * (t - s))| := by
        rw [abs_div, abs_neg, abs_of_pos h2ts, lt_div_iff₀ h2ts]
        have h2ts_lt : 2 * (t - s) < 2 * δ := by linarith
        have hb1 : Bs * (2 * (t - s)) ≤ Bs * (2 * δ) :=
          mul_le_mul_of_nonneg_left h2ts_lt.le hBs
        have hb2 : Bs * (2 * δ) < (Bs + 1) * (2 * δ) := by nlinarith [hδpos]
        have hb3 : Bs * (2 * (t - s)) < c := by linarith [hb1, hb2, hprod]
        linarith [hb3, hNlb z hzA]
      rintro (hnk | hle)
      · exact hnk hzK
      · exact absurd hle (not_le.mpr hbig)
    -- so the inner ae `∀ᵐ z, dich` is false.
    intro himp
    have hinner := himp hsmem
    rw [ae_iff] at hinner
    have hAsub : A ⊆ {z | ¬ (z ∉ K ∨ |(-(N z)) / (2 * (t - s))| ≤ Bs)} := fun z hz => hzfail z hz
    have hle : μ A ≤ 0 := le_of_le_of_eq (measure_mono hAsub) hinner
    exact (hle.trans_lt hApos).false
  -- the measure contradiction on `s`.
  rw [ae_iff] at h
  have hcontr : volume (Set.Ioo (t - δ) t) ≤ 0 := le_of_le_of_eq (measure_mono hbad) h
  rw [Real.volume_Ioo, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hcontr
  linarith [hcontr]

end QIQTH.GaussianJetTheorem

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GaussianJetTheorem
#print axioms mul_exp_neg_le_one
#print axioms mul_exp_neg_sq_le_half
#print axioms mul_exp_neg_mul_sq_le
#print axioms one_add_mul_exp_neg_le
#print axioms gaussian_beats_linear
#print axioms gaussian_beats_quadratic
#print axioms gateData_numerator_shape_unsat
end AxiomChecks
