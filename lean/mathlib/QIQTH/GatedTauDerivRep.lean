/-
  GatedTauDerivRep — J4-217: the τ-DERIVATIVE gate-equation representative (measurability brick G-c).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  measurability plumbing brick.  No `sorry` (prose excepted), no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise.  Every carried hypothesis is a genuine MEASURABILITY or a
  genuine on-gate `HasDerivAt` fact (never a joint-continuity / `C¹` obligation) — the same style as the
  fixed-field-point suppliers and one product coordinate up, mirroring `GatedDerivRepProduct` (J4-216).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FEEDS.  `HEmeasBorelAudit.BorelDischargeSurface` (J4-215) is the continuity-free
  discharge surface of the triple `hEmeas` (S1) under Route B (`E3d`).  Its FIRST conjunct is exactly
    `StronglyMeasurable (fun w : ℝ × Point n × Point n => deriv (fun u => G u w.2.1 w.2.2) w.1)`,
  the `∂_τ` derivative field of the concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`
  (the `hDτ` hypothesis of `triple_hEmeas_of_borel_deriv_fields`).  J4-216 discharged the field-`pd`
  conjuncts (2) + the diagonal of (3); this file mirrors that exact product gate-equation pattern for
  the τ slot.

  ── THE τ ON-GATE FACTORISATION (the point of a HARD, `τ`-INDEPENDENT gate).  On the gate
  (`q ∈ K`, `p ∈ S q`) the witness factors, for EVERY `u`, as a genuine `funext` equality
    `vanVleckGatedWitness … u p q = gaussDdim u (W q p) · chartFieldAmp … u q p`,
  `W q := uniformInverseChart g gi hC hK q`.  Because the set-gate does not depend on `u`, no
  neighbourhood / eventually-equal manoeuvre is needed in the `u`-axis (unlike the field-`pd` slot which
  needed a field neighbourhood): the two `u`-functions coincide identically, so their `deriv`s coincide.

  ── THE τ=0 / OFF-GATE HONEST RESOLUTION.  The witness vanishes for ALL `u ≤ 0` (`gaussDdim u = 0`,
  `0 < n`), so on `Iic τ` (for any `τ ≤ 0`) the `u`-function is `≡ 0`.  Hence its left window has
  derivative `0`, and `HasDerivWithinAt.deriv_eq_zero` (which internally splits differentiable-or-not:
  at the heat-kernel diagonal `W q p = 0` the `u`-function is genuinely non-differentiable at `0` and
  Lean's `deriv` returns the junk value `0`; off the diagonal it is flat-differentiable with derivative
  `0`) gives `deriv (fun u => G u p q) τ = 0` for every `τ ≤ 0`, matching the representative (whose every
  term carries a `gaussDdim τ` factor, hence `= 0` for `τ ≤ 0`).  So the everywhere identity closes at
  `τ = 0` with NO case analysis on the diagonal and NO flatness computation.

  ── THE REPRESENTATIVE.  `gatedTauRepProd` — the `w.2.2 ∈ K`-indicator of the on-gate `∂_τ` closed form
    `(∑ᵢ ((W q p)ᵢ²/(4τ²) − 1/(2τ)))·G_τ(W q p)·A(u=τ)  +  G_τ(W q p)·(∂_τ A)`,
  the Gaussian's `t`-derivative closed form (`gaussDdim_heat_eqn` + `gaussDdim_pd_pd_i`) times the
  amplitude, plus the Gaussian times the carried amplitude `τ`-derivative `Cfield` (`A = chartFieldAmp`
  is affine in `τ`, so `∂_τ A` is a genuine measurable field carried with its `HasDerivAt` witness).

  ── THE MEASURABILITY + EVERYWHERE IDENTITY + CAPSTONE.  `gatedTauRepProd_measurable` (factor-by-factor
  Borel, `gaussDdim` via `gaussDdim_uncurry_measurable`, `1/τ`/`1/τ²` denominators `measurable_fst`-built),
  `witnessTauDeriv_eq_gatedTauRepProd` (the three-way dichotomy everywhere identity), and
  `tauDeriv_prod_stronglyMeasurable` (BorelDischargeSurface CONJUNCT (1), CONCRETE).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedDerivRepProduct
import QIQTH.AmplitudePackage
import QIQTH.GlobalHunifAssembly
import QIQTH.EngineInstantiation

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedTauDerivRep

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — G-c: the τ-derivative product representative + measurability.
    ############################################################################### -/

/-- **`gatedTauRepProd` — the product-coordinate measurable representative of `∂_τ` of the witness.**
    Field point `w.2.1`, base `w.2.2`, time `w.1`; carried amplitude `τ`-derivative field
    `Cfield : base → fieldpt → ℝ`.  The `w.2.2 ∈ K`-indicator of the on-gate `∂_τ` closed form: the
    Gaussian's `t`-derivative closed form (`gaussDdim_heat_eqn`) times the amplitude, plus the Gaussian
    times `Cfield`.  Every term carries a `gaussDdim w.1` factor, so the value is `0` for `w.1 ≤ 0`.
    NOT `a₁ = R/6`. -/
noncomputable def gatedTauRepProd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
    (fun w : ℝ × Point n × Point n =>
      ((∑ i, ((uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1)))
            * gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) * Cfield w.2.2 w.2.1)

/-- **★ `gatedTauRepProd_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the τ representative,
    from `hKmeasSet` (`MeasurableSet K`), `hChartMeas` (Borel chart jointly in base+fieldpt),
    `hAmpMeas` (amplitude), `hCmeas` (the carried `∂_τ` amplitude field).  `gaussDdim` factor via
    `gaussDdim_uncurry_measurable`; the `1/τ`, `1/τ²` denominators are `measurable_fst`-built
    (measurability, not integrability).  NO continuity.  NOT `a₁ = R/6`. -/
theorem gatedTauRepProd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (Cfield : Point n → Point n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hCmeas : Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)) :
    Measurable (gatedTauRepProd g gi hC hK a b Cfield) := by
  unfold gatedTauRepProd
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hCoef : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ i, ((uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2)
              - 1 / (2 * w.1))) := by
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have h1 : Measurable
        (fun w : ℝ × Point n × Point n =>
          (uniformInverseChart g gi hC hK w.2.2 w.2.1 i) ^ 2 / (4 * w.1 ^ 2)) :=
      (((measurable_pi_apply i).comp hChartMeas).pow_const 2).div
        (measurable_const.mul (measurable_fst.pow_const 2))
    have h2 : Measurable (fun w : ℝ × Point n × Point n => (1 : ℝ) / (2 * w.1)) :=
      measurable_const.div (measurable_const.mul measurable_fst)
    exact h1.sub h2
  exact (((hCoef.mul hG).mul hAmpMeas).add (hG.mul hCmeas)).indicator
    (measurable_snd.snd hKmeasSet)

/-- **★ `witnessTauDeriv_eq_gatedTauRepProd` — THE τ EVERYWHERE IDENTITY.**  The raw `∂_τ` kernel of the
    concrete witness EQUALS the product representative at every `w = (τ,p,q)`, via the three-way
    dichotomy:
      • `w.2.2 ∉ K` — the `u`-function is `≡ 0` (off the base gate), so `deriv = 0 =` indicator;
      • `w.2.2 ∈ K`, `w.1 ≤ 0` — the `u`-function is `≡ 0` on `Iic w.1` (`gaussDdim u = 0` for `u ≤ 0`),
        so `deriv = 0` (`HasDerivWithinAt.deriv_eq_zero`, no diagonal case split), and the representative
        is `0` (its shared `gaussDdim w.1` factor vanishes);
      • `w.2.2 ∈ K`, `0 < w.1` — the on-gate `funext` factorisation `G u = gaussDdim u (W)·A(u)` (gate is
        `τ`-independent) + the product rule, with `∂_τ gaussDdim` from `gaussDdim_heat_eqn` and `∂_τ A`
        the carried `Cfield` (via `hgate`'s `HasDerivAt`).
    NOT `a₁ = R/6`. -/
theorem witnessTauDeriv_eq_gatedTauRepProd (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) :
    ∀ w : ℝ × Point n × Point n,
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1
        = gatedTauRepProd g gi hC hK a b Cfield w := by
  intro w
  simp only [gatedTauRepProd]
  by_cases hzK : w.2.2 ∈ K
  · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    set v := uniformInverseChart g gi hC hK w.2.2 w.2.1 with hvdef
    by_cases hτ : 0 < w.1
    · -- ON GATE, τ > 0: the funext factorisation + product rule.
      obtain ⟨hpS, hamp⟩ := hgate w hzK hτ
      have hfe : (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2)
          = (fun u => gaussDdim u v * chartFieldAmp g gi hC hK a b u w.2.2 w.2.1) := by
        funext u
        rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK hpS]
        simp only [chartFieldAmp, hvdef]
        ring
      -- the Gaussian `t`-derivative closed form.
      have hgauss_deriv_eq : deriv (fun u => gaussDdim u v) w.1
          = (∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v := by
        rw [gaussDdim_heat_eqn w.1 hτ v, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i w.1 hτ v i)
      have hgd : DifferentiableAt ℝ (fun u => gaussDdim u v) w.1 := by
        have h := HasDerivAt.fun_finsetProd
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => heatKernel1D_hasDerivAt_t w.1 (v i) hτ)
        simpa only [gaussDdim] using h.differentiableAt
      have hg : HasDerivAt (fun u => gaussDdim u v)
          ((∑ i, ((v i) ^ 2 / (4 * w.1 ^ 2) - 1 / (2 * w.1))) * gaussDdim w.1 v) w.1 := by
        have h0 := hgd.hasDerivAt
        rwa [hgauss_deriv_eq] at h0
      -- product rule; `(hg.mul hamp).deriv` matches the goal up to beta (defeq).
      rw [hfe]
      exact (hg.mul hamp).deriv
    · -- ON GATE, τ ≤ 0: both sides `0`.
      rw [not_lt] at hτ
      have hzero_le : ∀ u : ℝ, u ≤ 0 →
          vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2 = 0 := by
        intro u hu
        by_cases hpS : w.2.1 ∈ S w.2.2
        · rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK hpS,
              gaussDdim_eq_zero_of_nonpos hn u (uniformInverseChart g gi hC hK w.2.2 w.2.1) hu]
          ring
        · unfold vanVleckGatedWitness
          exact gatedKernel_apply_of_notMem K S _ u w.2.1 w.2.2 (Or.inr hpS)
      have hDW : HasDerivWithinAt
          (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) 0 (Set.Iic w.1) w.1 := by
        refine (hasDerivAt_const w.1 (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact eventuallyEq_of_mem self_mem_nhdsWithin
            (fun u hu => hzero_le u (le_trans (Set.mem_Iic.mp hu) hτ))
        · exact hzero_le w.1 hτ
      have hderiv0 : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1 = 0 :=
        hDW.deriv_eq_zero (uniqueDiffWithinAt_Iic w.1)
      rw [hderiv0, hvdef, gaussDdim_eq_zero_of_nonpos hn w.1
        (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · -- OFF the base gate: the `u`-function is identically `0`.
    rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    have hzero : (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2)
        = (fun _ => (0 : ℝ)) := by
      funext u
      unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ u w.2.1 w.2.2 (Or.inl hzK)
    rw [hzero]
    simp

/-- **★★ `tauDeriv_prod_stronglyMeasurable` — BorelDischargeSurface CONJUNCT (1), CONCRETE.**  For the
    concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`,
      `StronglyMeasurable (fun w => deriv (fun u => G u w.2.1 w.2.2) w.1)`,
    the EXACT shape of `HEmeasBorelAudit.BorelDischargeSurface`'s first conjunct (the `hDτ` slot of
    `triple_hEmeas_of_borel_deriv_fields`).  The carried `hcar` supplies the amplitude `τ`-derivative
    field `Cfield`, the factor measurabilities, and the on-gate `HasDerivAt` data; the everywhere
    identity glues the raw `∂_τ` kernel to `gatedTauRepProd`, and ℝ-valued `Measurable ⟹ StronglyMeasurable`.
    CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem tauDeriv_prod_stronglyMeasurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1) := by
  obtain ⟨Cfield, hChartMeas, hAmpMeas, hCmeas, hgate⟩ := hcar
  have hrw : (fun w : ℝ × Point n × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u w.2.1 w.2.2) w.1)
      = gatedTauRepProd g gi hC hK a b Cfield := by
    funext w
    exact witnessTauDeriv_eq_gatedTauRepProd hn g gi hC hK S a b Cfield hgate w
  rw [hrw]
  exact (gatedTauRepProd_measurable g gi hC hK a b Cfield hKmeasSet hChartMeas hAmpMeas
    hCmeas).stronglyMeasurable

/-! ###############################################################################
    ### §B — STRETCH: the concrete triple `hEmeas` with ONLY the mixed field-Hessian carried.
    ############################################################################### -/

/-- **★★ `tripleHEmeas_concrete_of_mixed` — S1 FOR THE CONCRETE WITNESS, MIXED SLICE ISOLATED.**  The
    triple `hEmeas` (S1) of `HEmeasBorelAudit.tripleHEmeas` for the concrete gated van-Vleck witness
    `G := vanVleckGatedWitness g gi hC hK S a b`, assembled through
    `HEmeasBorelAudit.tripleHEmeas_of_surface`, with:
      • conjunct (1) — the `∂_τ` field — DISCHARGED here by `tauDeriv_prod_stronglyMeasurable` (G-c,
        this file) from `hcarTau`;
      • conjunct (2) — the FIRST field-`pd` — DISCHARGED by
        `GatedDerivRepProduct.firstFieldPd_prod_stronglyMeasurable` (G-a, J4-216) from `hcarField`;
      • conjunct (3) — the SECOND field-`pd` Hessian `∂ᵢ(∂ⱼ …)` — CARRIED as `hP2`.  Its `i = j`
        DIAGONAL is separately banked (`GatedDerivRepProduct.secondFieldPd_prod_diag_measurable`, G-b
        diagonal), so the genuinely-open residue inside `hP2` is precisely the MIXED `i ≠ j` off-diagonal
        slice (the `gaussComp_amp_pd_pd_mixed` gap of §B in J4-216);
      • conjuncts (4)/(5) — the coefficient `gi` / `christoffel` measurabilities — CARRIED.
    This isolates the last measurability gap of Route B for the concrete witness as the single carried
    Hessian hypothesis `hP2` (open part = its `i ≠ j` slice).  Continuity-free.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_concrete_of_mixed (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hP2 : ∀ i j : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  refine QIQTH.HEmeasBorelAudit.tripleHEmeas_of_surface g gi
    (vanVleckGatedWitness g gi hC hK S a b) ⟨?_, ?_, hP2, hgi, hchr⟩
  · exact tauDeriv_prod_stronglyMeasurable hn g gi hC hK S a b hKmeasSet hcarTau
  · exact QIQTH.GatedDerivRepProduct.firstFieldPd_prod_stronglyMeasurable hn g gi hC hK S a b
      hKmeasSet hcarField

end QIQTH.GatedTauDerivRep

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedTauDerivRep
#print axioms gatedTauRepProd_measurable
#print axioms witnessTauDeriv_eq_gatedTauRepProd
#print axioms tauDeriv_prod_stronglyMeasurable
#print axioms tripleHEmeas_concrete_of_mixed
end AxiomChecks
