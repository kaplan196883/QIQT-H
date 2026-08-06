/-
  CConvV2EnvelopeFromStar — J4-324 (facade-v2 brick 5 of 14): the ENVELOPE / DOMINATION layer,
  RE-DERIVED FROM THE V2 CONTRACTS (`hStar` + `hFpair`) to replace the ADJUDICATED-FALSE
  `HenvUInstantiation.hdomS_assembled` / `.henv_assembled` (which rode on the false `hGateData`/`hFbd`
  facade fields).  ONE brick of the `a₁ = R/6` heat-kernel campaign (SOL CONSULT #9,
  docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It re-derives
  the classical dominated-differentiation ENVELOPE input from the two v2 contract fields.  NO `sorry`
  (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis in this
  file's own theorems, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (E0) THE OLD OUTPUT SHAPES + WHAT WAS POISONED.

  The OLD `HenvUInstantiation.hdomS_assembled` produced (for `dH := witnessFieldDeriv`):
      `∀ x₀ ∈ u, ∀ i, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s, s ∈ uIoc 0 t → ∀ᵐ z,`
        `‖witnessFieldDeriv … i (t−s) x z · F s z‖ ≤ (C₀·Cf) · gaussDdim (2(t−s)) z`,
  with `C₀ = (Bs·Ba+Bd)·(√2)ⁿ`.  Its `henv_assembled` sibling produced the SAME inequality in the
  `∀ᵐ s → ∀ᶠ x → ∀ᵐ z` order.

  ── POISONED PARTS (the `Bs`/`Ba`/`Bd` factor-decomposition + the uniform `Cf`).  The constant `C₀`
     came from `hGateData`'s demand of a CONSTANT `Bs` bounding the bare Gaussian log-gradient
     `|N/2(t−s)|` — FALSE (`GaussianJetTheorem.gateData_numerator_shape_unsat`; the true cost is
     `(t−s)^{−1/2}`, not `O(1)`).  The `Cf` came from `hFbd`'s uniform `|F s z| ≤ Cf` — FALSE for the
     concrete Levi source near the diagonal.  So BOTH the `C₀` and the `Cf` factor are facade
     artefacts; the constant-times-`gaussDdim` dominator shape is unattainable.

  ── SURVIVING PARTS (the dominated-differentiation INPUT SHAPE).  What the downstream C¹/diff-under-∫
     genuinely consumes survives: a per-`(x,i,s,z)` pointwise bound `‖dH · F‖ ≤ φ` by an
     `s`-integrable `z`-envelope `φ`, plus that envelope's `s`-integrability.  The v2 contracts supply
     BOTH with the TRUE dominator `C · ((t−s)^{−1/2} · gaussDdim (2(t−s)) z · |F s z|)` (`hStar` gives
     the `(t−s)^{−1/2}` gradient cost; `hFpair` gives the `s`-integrability of its `z`-integral).

  ## WHAT THIS FILE LANDS (E1–E4).
    • (E1) `pointwise_dom_v2`  — `‖wfd · F‖ ≤ C·((t−s)^{−1/2}·gaussDdim(2(t−s))z·|F s z|)` (from `hStar`
      + `abs_mul`; POINTWISE-UNIFORM on `u`, both filter orders derivable trivially).
    • (E2) `envelope_integrable_v2` — the `z`-integral envelope `s ↦ C·(t−s)^{−1/2}·∫ gaussDdim·|F|` is
      `IntegrableOn (Ioc 0 t)` (from `hFpair` as a constant multiple).
    • (E3) `hdomS_v2` / `henv_v2` — the assembled filtered domination in BOTH old output orders
      (`∀ᶠ x → ∀ᵐ s → ∀ᵐ z` and `∀ᵐ s → ∀ᶠ x → ∀ᵐ z`), the v2 dominator, from `hStar` (the `∀ᶠ x`
      leg uses the honest neighbourhood hypothesis `hu : u ∈ 𝓝 x₀`, satisfiable for `u` open / univ —
      `hStar` is `u`-uniform, so it dropped the `∀ᶠ` the old input carry had).
    • (E4) `zslice_integrable_v2` — for a fixed on-window `(x,i,s)`, the `z`-slice
      `z ↦ wfd · F` is `Integrable`, from the domination (E1) + the honest satisfiable carries
      `hmeas` (slice measurability) and `hint` (integrability of `gaussDdim·|F|`).

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvV2Contracts

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.CConvV2Contracts
open scoped Topology BigOperators

namespace QIQTH.CConvV2EnvelopeFromStar

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — (E1) the POINTWISE `hStar`-driven domination `‖wfd · F‖ ≤ C·((t−s)^{−1/2}·G·|F|)`.
    ############################################################################### -/

/-- **★ (E1) `pointwise_dom_v2`.**  From the v2 envelope contract's `hStar`, the product `wfd · F`
    obeys the pointwise dominated bound with the TRUE `(t−s)^{−1/2}`-weighted Gaussian dominator, for
    `x ∈ u`, `s ∈ Ioc 0 t`, all `z` (POINTWISE-UNIFORM — no `∀ᶠ`/`∀ᵐ`):
        `|wfd i (t−s) x z · F s z| ≤ C · ((t−s)^{−1/2} · gaussDdim (2(t−s)) z · |F s z|)`.
    Proof: `abs_mul` + `hStar` (`|wfd| ≤ C·(t−s)^{−1/2}·G`) times `|F| ≥ 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem pointwise_dom_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) (F : ℝ → Point n → ℝ)
    (env : CConvWitnessEnvelopeDataV2 g gi hC hK S a b t u Bs Ba Bd) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z|
        ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z * |F s z|) := by
  obtain ⟨C, hC0, hStar⟩ := env.hStar
  refine ⟨C, hC0, fun x hx i s hs z => ?_⟩
  rw [abs_mul]
  have h1 := hStar x hx i s hs z
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z) * |F s z| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z * |F s z|) := by ring

/-! ###############################################################################
    ### §2 — (E2) the `z`-integral ENVELOPE `s ↦ C·(t−s)^{−1/2}·∫ G·|F|` is `IntegrableOn`.
    ############################################################################### -/

/-- **★ (E2) `envelope_integrable_v2`.**  The `s`-envelope `φ s := C · (t−s)^{−1/2} · ∫ z, gaussDdim
    (2(t−s)) z · |F s z|` is `IntegrableOn (Ioc 0 t)` — this is the v2 source contract's `hFpair`
    integrand scaled by the constant `C` (`IntegrableOn.const_mul`).  This is the `s`-integrability the
    downstream differentiation-under-∫ consumes.  ⚠ NOT `a₁ = R/6`. -/
theorem envelope_integrable_v2 (F : ℝ → Point n → ℝ) (t C : ℝ)
    (source : CConvSourceDataV2 F t) :
    IntegrableOn
      (fun s : ℝ => C * ((t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n))))
      (Set.Ioc 0 t) (volume : Measure ℝ) :=
  source.hFpair.const_mul C

/-! ###############################################################################
    ### §3 — (E3) the ASSEMBLED filtered domination in BOTH old output orders.
    ############################################################################### -/

/-- **★ (E3) `hdomS_v2`.**  The v2 analogue of the OLD `hdomS_assembled` output slot — same
    `∀ᶠ x → ∀ᵐ s → ∀ᵐ z` order, the v2 dominator:
        `∀ x₀ ∈ u, ∀ i, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s, s ∈ uIoc 0 t → ∀ᵐ z,`
          `‖wfd i (t−s) x z · F s z‖ ≤ C · ((t−s)^{−1/2} · gaussDdim (2(t−s)) z · |F s z|)`.
    From `pointwise_dom_v2` (E1), lifting the `u`-uniform pointwise bound through the neighbourhood
    hypothesis `hu` (`hStar` is `u`-uniform, so the `∀ᶠ x` leg comes from `u ∈ 𝓝 x₀`) and the
    `uIoc 0 t = Ioc 0 t` identification (`ht : 0 ≤ t`).  ⚠ NOT `a₁ = R/6`. -/
theorem hdomS_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 ≤ t) (u : Set (Point n)) (Bs Ba Bd : ℝ) (F : ℝ → Point n → ℝ)
    (hu : ∀ x₀ ∈ u, u ∈ 𝓝 x₀)
    (env : CConvWitnessEnvelopeDataV2 g gi hC hK S a b t u Bs Ba Bd) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z * |F s z|) := by
  obtain ⟨C, hC0, hp⟩ := pointwise_dom_v2 g gi hC hK S a b t u Bs Ba Bd F env
  refine ⟨C, hC0, fun x₀ hx₀ i => ?_⟩
  filter_upwards [hu x₀ hx₀] with x hxu
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Set.uIoc_of_le ht] at hs
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hp x hxu i s hs z

/-- **★ (E3) `henv_v2`.**  The v2 analogue of the OLD `henv_assembled` output slot — the
    `∀ᵐ s → ∀ᶠ x → ∀ᵐ z` order (genuinely distinct from `hdomS_v2`'s), the SAME v2 dominator.  Since
    `hStar` is pointwise-UNIFORM on `u`, both orders come trivially from the same E1 bound.  ⚠ NOT
    `a₁ = R/6`. -/
theorem henv_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 ≤ t) (u : Set (Point n)) (Bs Ba Bd : ℝ) (F : ℝ → Point n → ℝ)
    (hu : ∀ x₀ ∈ u, u ∈ 𝓝 x₀)
    (env : CConvWitnessEnvelopeDataV2 g gi hC hK S a b t u Bs Ba Bd) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ ∈ u, ∀ i : Fin n,
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
            ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z * |F s z|) := by
  obtain ⟨C, hC0, hp⟩ := pointwise_dom_v2 g gi hC hK S a b t u Bs Ba Bd F env
  refine ⟨C, hC0, fun x₀ hx₀ i => ?_⟩
  refine Filter.Eventually.of_forall (fun s hs => ?_)
  rw [Set.uIoc_of_le ht] at hs
  filter_upwards [hu x₀ hx₀] with x hxu
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hp x hxu i s hs z

/-! ###############################################################################
    ### §4 — (E4) the `z`-slice INTEGRABILITY of `z ↦ wfd · F` (fixed on-window `(x,i,s)`).
    ############################################################################### -/

/-- **★ (E4) `zslice_integrable_v2`.**  For a fixed `x ∈ u`, coordinate `i`, and on-window
    `s ∈ Ioc 0 t`, the `z`-slice `z ↦ witnessFieldDeriv i (t−s) x z · F s z` is `Integrable`.  Route:
    `Integrable.mono'` against the dominator `(C·(t−s)^{−1/2}) · (gaussDdim (2(t−s)) z · |F s z|)`
    (integrable = `hint` scaled) using the E1 pointwise bound.  The slice measurability `hmeas` and the
    dominator integrability `hint` (of `gaussDdim·|F|`) are the honest satisfiable carries (true for
    `F ≡ 0`: both slices collapse to `0`).  ⚠ NOT `a₁ = R/6`. -/
theorem zslice_integrable_v2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) (F : ℝ → Point n → ℝ)
    (env : CConvWitnessEnvelopeDataV2 g gi hC hK S a b t u Bs Ba Bd)
    (x : Point n) (hx : x ∈ u) (i : Fin n) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t)
    (hmeas : AEStronglyMeasurable
      (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z) volume)
    (hint : Integrable (fun z => gaussDdim (2 * (t - s)) z * |F s z|) (volume : Measure (Point n))) :
    Integrable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z)
      (volume : Measure (Point n)) := by
  obtain ⟨C, hC0, hStar⟩ := env.hStar
  refine Integrable.mono' (hint.const_mul (C * (t - s) ^ (-(1 : ℝ) / 2))) hmeas ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hStar x hx i s hs z
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (2 * (t - s)) z) * |F s z| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = (C * (t - s) ^ (-(1 : ℝ) / 2)) * (gaussDdim (2 * (t - s)) z * |F s z|) := by ring

end QIQTH.CConvV2EnvelopeFromStar

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2EnvelopeFromStar
#print axioms pointwise_dom_v2
#print axioms envelope_integrable_v2
#print axioms hdomS_v2
#print axioms henv_v2
#print axioms zslice_integrable_v2
end AxiomChecks
