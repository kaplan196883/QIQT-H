/-
  DaLimCurvedGauge — J4-512: DECOUPLING the flat frame condition `hframeK` (g = δ on a whole
  neighbourhood `K`) from the Da-limit gauge members of `GlobalRawBoundFacade.hDaLimLU_from_labelled`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  DECOUPLING brick: it re-expresses the gauge sub-assembly `GlobalRawBoundFacade.gauge_from_geometry`
  so that it consumes ONLY the pointwise Riemann-normal-coordinate (RNC) VALUE gauge
  `hg0 : g(0) = δ` — the 0-jet — instead of the flat neighbourhood condition
  `hframeK : ∀ q ∈ K, g q = δ`.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE AUDIT (why this is the whole decoupling).

  Inside `GlobalRawBoundFacade.hDaLimLU_from_labelled`, the flat frame `hframeK` is consumed at EXACTLY
  ONE place:
      `obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0`
  and `gauge_from_geometry` produces the two POINTWISE-AT-0 census members
      `MemGaugeGi   gi    = ∀ i j, gi 0 i j = δ_{ij}`      (inverse metric AT 0 = identity)
      `MemGaugeGamma g gi = ∀ k i j, christoffel g gi k i j 0 = 0`   (Christoffel AT 0 = 0).
  •  `MemGaugeGamma` is built by `DaLimCensusRecon.memGaugeGamma_of_hdg0` from ONLY the first-derivative
     gauge `hdg0 : ∂_e g_{ab}(0) = 0` — `hframeK` is NOT used.
  •  `MemGaugeGi` is built by the chain `memGaugeGi_of_geometry → hgi_of_geometry → hg0_of_hframeK`,
     and `hg0_of_hframeK` is LITERALLY `hframeK 0 hK0` — i.e. `hframeK` is used ONLY to extract the
     VALUE `g(0) = δ`.  The genuine work, `OuterCarryRecon.hgi_of_hg0_hinvF`, already derives
     `gi(0) = δ` from the pointwise value `g(0) = δ` plus the (everywhere) inverse relation `hinvF`.

  VERDICT: `hframeK` is role **(c) JET-REDUCIBLE** — in fact VALUE-reducible to the 0-jet value
  `g(0) = δ`.  The Da-limit residual gauge does NOT need `g = δ` on a neighbourhood; only the value at
  the centre survives into the two pointwise gauge members.  (Confirmed adversarially: nothing else in
  the capstone touches `hframeK`, and the τ→0 concentration only collapses the multiplicative
  normalization to its centre value — it does not need a flat neighbourhood.)

  ## THE CURVED SATISFIABILITY GATE (defeating a vacuous weakening).

  The whole point of J4-509 was that `hframeK` (g = δ on open `K`) forces `∂²g = 0` on `K`, hence
  `Riemann = 0`, hence `Ric(0) = 0` — FLAT-ONLY.  The weakened package `{hg0, hdg0, hinvF}` places NO
  constraint on `∂²g(0)`.  We CERTIFY this is not a vacuous weakening by exhibiting a genuinely curved
  witness (`confMetric` on `Point 2`, a conformal metric) that satisfies all three weakened hypotheses
  `hg0`/`hdg0`/`hinvF` yet has `∂²g₀₀(0) = 2 ≠ 0` — the exact second-jet datum that `hframeK` destroys.
  So the weakened antecedent is INHABITED BY A CURVED METRIC.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.OuterCarryRecon
import QIQTH.DaLimCensusRecon

open QIQTH.Curvature QIQTH.DaLimLUWallRecon
open scoped BigOperators

namespace QIQTH.DaLimCurvedGauge

variable {n : ℕ}

/-! ###############################################################################
    ### PART A — the DECOUPLED gauge sub-assembly (consumes the 0-jet value, not `hframeK`).
    ############################################################################### -/

/-- **A1 — `memGaugeGi_of_hg0`.**  The RNC inverse-metric normalization census member `MemGaugeGi gi`
    (`gi(0) = δ`) DISCHARGED from ONLY the pointwise 0-jet VALUE gauge `hg0 : g(0) = δ` and the
    (everywhere) inverse relation `hinvF` — via the value-based `OuterCarryRecon.hgi_of_hg0_hinvF`.
    NO neighbourhood frame `hframeK` is consumed: this is the curved-compatible replacement of the
    `hg0_of_hframeK`-fronted chain.  NOT `a₁ = R/6`. -/
theorem memGaugeGi_of_hg0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg0 : ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    MemGaugeGi (n := n) gi :=
  fun a b => QIQTH.OuterCarryRecon.hgi_of_hg0_hinvF g gi hg0 hinvF a b

/-- **A2 — `gauge_from_pointwise`.**  The curved-compatible drop-in replacement for
    `GlobalRawBoundFacade.gauge_from_geometry`: both gauge census members `MemGaugeGi gi` and
    `MemGaugeGamma g gi` from the pointwise RNC jet `{hg0 (0-jet value), hdg0 (1-jet), hinvF}` — with
    the neighbourhood frame condition `hframeK` (and `hK0`) REMOVED.  This is exactly what
    `hDaLimLU_from_labelled` needs from the geometry group (it feeds only `hgi`/`hΓ` downstream); with
    `hframeK` gone, `∂²g(0)` is free and the antecedent becomes curved-satisfiable.  NOT `a₁ = R/6`. -/
theorem gauge_from_pointwise (g gi : Point n → Fin n → Fin n → ℝ)
    (hg0 : ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0) :
    MemGaugeGi (n := n) gi ∧ MemGaugeGamma (n := n) g gi :=
  ⟨memGaugeGi_of_hg0 g gi hg0 hinvF,
   QIQTH.DaLimCensusRecon.memGaugeGamma_of_hdg0 g gi hdg0⟩

/-- **A3 — `hg0_of_hframeK_relax`.**  SOUNDNESS of the weakening: the old flat frame `hframeK`
    (+ `0 ∈ K`) IMPLIES the new pointwise value gauge `hg0`.  So `gauge_from_pointwise` is a genuine
    RELAXATION of `gauge_from_geometry` — anything the flat frame proved, the 0-jet value proves — and
    `hg0` is strictly weaker (it does not constrain `g` off `0`).  Thin re-export of the existing
    `OuterCarryRecon.hg0_of_hframeK`.  NOT `a₁ = R/6`. -/
theorem hg0_of_hframeK_relax (g : Point n → Fin n → Fin n → ℝ) {K : Set (Point n)}
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∀ i j, g (0 : Point n) i j = if i = j then (1 : ℝ) else 0 :=
  fun i j => QIQTH.OuterCarryRecon.hg0_of_hframeK g hK0 hframeK i j

/-! ###############################################################################
    ### PART B — the CURVED satisfiability witness (`∂²g(0) ≠ 0` with `{hg0, hdg0, hinvF}` all true).
    ############################################################################### -/

/-- A genuinely curved conformal witness metric on `Point 2`: `g_{ij}(y) = (1 + (y₀)²) δ_{ij}`.
    Value at `0` is `δ`, first jet at `0` vanishes, but the second `y₀`-derivative of `g₀₀` is `2 ≠ 0`
    — a curved 2-jet, forbidden by any flat neighbourhood frame `hframeK`. -/
noncomputable def confMetric (y : Point 2) (a b : Fin 2) : ℝ :=
  if a = b then 1 + (y 0) ^ 2 else 0

/-- The inverse of `confMetric`: `gi_{ij}(y) = (1 + (y₀)²)⁻¹ δ_{ij}`. -/
noncomputable def confMetricInv (y : Point 2) (a b : Fin 2) : ℝ :=
  if a = b then (1 + (y 0) ^ 2)⁻¹ else 0

theorem confMetric_pos (y : Point 2) : (0 : ℝ) < 1 + (y 0) ^ 2 := by positivity

/-- **B1 (hg0) — the witness satisfies the pointwise 0-jet value gauge `g(0) = δ`.** -/
theorem confMetric_hg0 : ∀ i j, confMetric (0 : Point 2) i j = if i = j then (1 : ℝ) else 0 := by
  intro i j
  simp only [confMetric, Pi.zero_apply]
  norm_num

/-- **B2 (hinvF) — the witness satisfies the everywhere inverse relation.** -/
theorem confMetric_hinvF :
    ∀ y a b, (∑ σ, confMetric y a σ * confMetricInv y σ b) = if a = b then 1 else 0 := by
  intro y a b
  have hne : (1 : ℝ) + (y 0) ^ 2 ≠ 0 := (confMetric_pos y).ne'
  fin_cases a <;> fin_cases b <;>
    simp [confMetric, confMetricInv, mul_inv_cancel₀ hne]

/-- A convenience: the `y₀`-slice derivative `d/dt (1 + t²) = 2t`. -/
theorem hasDerivAt_one_add_sq (x : ℝ) :
    HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
  have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x)
  simpa using h.const_add (1 : ℝ)

/-- **B3 (hdg0) — the witness satisfies the pointwise 1-jet gauge `∂_e g_{ab}(0) = 0`.** -/
theorem confMetric_hdg0 :
    ∀ a b e, pd (fun y => confMetric y a b) e (0 : Point 2) = 0 := by
  intro a b e
  by_cases hab : a = b
  · subst hab
    have hfun : (fun y : Point 2 => confMetric y a a) = (fun y => 1 + (y 0) ^ 2) := by
      funext y; simp [confMetric]
    rw [hfun]
    simp only [pd, Pi.zero_apply]
    by_cases he : e = 0
    · -- e = 0 : the slice is `t ↦ 1 + t²`, derivative `2·0 = 0` at `0`.
      subst he
      have hupd : (fun t : ℝ => 1 + ((Function.update (0 : Point 2) 0 t) 0) ^ 2)
          = (fun t : ℝ => 1 + t ^ 2) := by
        funext t; rw [Function.update_self]
      rw [hupd]
      simpa using (hasDerivAt_one_add_sq (0 : ℝ)).deriv
    · -- e ≠ 0 : the `0`-coordinate is untouched, the slice is the constant `1`.
      have h0e : (0 : Fin 2) ≠ e := fun h => he h.symm
      have hupd : (fun t : ℝ => 1 + ((Function.update (0 : Point 2) e t) 0) ^ 2)
          = (fun _ : ℝ => (1 : ℝ)) := by
        funext t
        rw [Function.update_of_ne h0e t (0 : Point 2)]
        simp
      rw [hupd]; simp
  · simp only [confMetric, if_neg hab]
    exact pd_const 0 e (0 : Point 2)

/-- The inner first partial `∂₀ g₀₀ (y) = 2·(y₀)` — a genuinely non-constant field. -/
theorem confMetric_pd00 (y : Point 2) :
    pd (fun x => confMetric x 0 0) 0 y = 2 * (y 0) := by
  have hfun : (fun x : Point 2 => confMetric x 0 0) = (fun x => 1 + (x 0) ^ 2) := by
    funext x; simp [confMetric]
  rw [hfun]
  simp only [pd]
  have hupd : (fun t : ℝ => 1 + ((Function.update y 0 t) 0) ^ 2)
      = (fun t : ℝ => 1 + t ^ 2) := by
    funext t; rw [Function.update_self]
  rw [hupd]
  exact (hasDerivAt_one_add_sq (y 0)).deriv

/-- **B4 (CURVED) — the witness has `∂²g₀₀(0) = 2 ≠ 0`.**  The second `y₀`-derivative of `g₀₀` at the
    centre is nonzero: the metric 2-jet is genuinely curved-order, NOT the flat `∂²g = 0` that any
    neighbourhood frame `hframeK` would force.  This is the datum `hframeK` destroys and the weakened
    package `{hg0, hdg0, hinvF}` leaves free. -/
theorem confMetric_second_jet_ne_zero :
    pd (fun y => pd (fun x => confMetric x 0 0) 0 y) 0 (0 : Point 2) = 2 := by
  have hcongr : (fun y => pd (fun x => confMetric x 0 0) 0 y) = (fun y => 2 * (y 0)) :=
    funext confMetric_pd00
  rw [hcongr]
  simp only [pd, Pi.zero_apply]
  have hupd : (fun t : ℝ => 2 * ((Function.update (0 : Point 2) 0 t) 0))
      = (fun t : ℝ => 2 * t) := by
    funext t; rw [Function.update_self]
  rw [hupd]
  have : HasDerivAt (fun t : ℝ => 2 * t) 2 (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
  simpa using this.deriv

/-- **B5 (CAPSTONE GATE) — the curved witness INHABITS the weakened gauge antecedent.**  The conformal
    metric `{confMetric, confMetricInv}` satisfies the full weakened hypothesis package
    `{hg0, hdg0, hinvF}` of `gauge_from_pointwise` (hence yields both gauge members), WHILE having a
    nonzero second jet `∂²g₀₀(0) = 2`.  So the decoupled gauge antecedent is genuinely CURVED-satisfiable
    — the weakening is NOT vacuous and NOT secretly flat.  NOT `a₁ = R/6`. -/
theorem curved_gauge_inhabited :
    (MemGaugeGi (n := 2) confMetricInv ∧ MemGaugeGamma (n := 2) confMetric confMetricInv)
      ∧ pd (fun y => pd (fun x => confMetric x 0 0) 0 y) 0 (0 : Point 2) ≠ 0 :=
  ⟨gauge_from_pointwise confMetric confMetricInv confMetric_hg0 confMetric_hinvF confMetric_hdg0,
   by rw [confMetric_second_jet_ne_zero]; norm_num⟩

end QIQTH.DaLimCurvedGauge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimCurvedGauge.memGaugeGi_of_hg0
#print axioms QIQTH.DaLimCurvedGauge.gauge_from_pointwise
#print axioms QIQTH.DaLimCurvedGauge.hg0_of_hframeK_relax
#print axioms QIQTH.DaLimCurvedGauge.confMetric_hg0
#print axioms QIQTH.DaLimCurvedGauge.confMetric_hinvF
#print axioms QIQTH.DaLimCurvedGauge.confMetric_hdg0
#print axioms QIQTH.DaLimCurvedGauge.confMetric_second_jet_ne_zero
#print axioms QIQTH.DaLimCurvedGauge.curved_gauge_inhabited
