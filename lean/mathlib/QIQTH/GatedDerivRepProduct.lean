/-
  GatedDerivRepProduct — J4-216: the VARYING-FIELD-POINT (product-coordinate) extension of the gated
  derivative representatives (measurability brick **G-a**, plus the diagonal slice of **G-b**).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  measurability plumbing brick.  No `sorry` (prose excepted), no new axioms, no vacuous / unsatisfiable
  hypotheses, no conclusion-in-disguise.  Every carried hypothesis is a genuine MEASURABILITY (never a
  joint-continuity / `C¹` obligation) — the same style as the fixed-field-point suppliers
  `GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq` (J4-185) and
  `SecondDerivEnvelope.witnessFieldDeriv2_measurable_of_gateEq` (J4-198), one product coordinate up.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FEEDS.  `HEmeasBorelAudit.BorelDischargeSurface` (J4-215) is the continuity-free
  discharge surface of the triple `hEmeas` (S1) under Route B (`E3d
  heatOp_stronglyMeasurable_of_deriv_fields`).  Its conjuncts (2)/(3) literally need the FIRST/SECOND
  field-`pd` of the concrete witness `G` measurable over the FULL product coordinate
  `w = (τ, p, q) : ℝ × Point n × Point n` — the field point `p = w.2.1` VARIES, unlike the fixed-`x`
  banked bricks (which give measurability in `(time, base) = (s, z)` only).  This file supplies:

    • conjunct (2) — `∀ k, StronglyMeasurable (fun w => pd (fun x => G w.1 x w.2.2) k w.2.1)` — for
      `G := vanVleckGatedWitness g gi hC hK S a b`, since
      `pd (fun x => vanVleckGatedWitness … w.1 x w.2.2) k w.2.1 = witnessFieldDeriv … k w.1 w.2.1 w.2.2`
      by definition.  Discharged CONTINUITY-FREE below via the product representative `gatedDerivRepProd`.

    • conjunct (3), DIAGONAL slice `i = i` — the product-coordinate second field-`pd`, via the diagonal
      product representative `gatedDeriv2RepProd`.  ⚠  The FULL conjunct (3) needs the MIXED index
      `pd_i (pd_j …)` for `i ≠ j`; that mixed off-diagonal closed form is genuinely NEW algebra (the
      banked `witnessFieldDeriv2` / `gaussComp_amp_pd_pd` is diagonal-only), so it is NOT discharged
      here — see the G-b gap note in §B.

  ── THE REPRESENTATIVES (product analogues of `gatedDerivRep` / `gatedDeriv2Rep`, field point varying).

    • `gatedDerivRepProd`  — the `w.2.2 ∈ K`-indicator of the order-1 on-gate closed form, at time `w.1`,
        base `w.2.2`, VARYING field point `w.2.1`, carrying a field-point-dependent first jet field
        `Pfield : base → fieldpt → dir → ℝ`.
    • `gatedDeriv2RepProd` — the order-2 (diagonal) analogue, carrying first/second jet fields.

  ── THE MEASURABILITIES.  `gatedDerivRepProd_measurable` / `gatedDeriv2RepProd_measurable`: manifestly
     joint `(τ,p,q)`-Borel from the carried factor measurabilities (chart, jet fields, amplitude and its
     field-`pd`s), the `gaussDdim` uncurried envelope `gaussDdim_uncurry_measurable`, and the measurable
     `w.2.2 ∈ K` indicator set.  NO continuity anywhere.

  ── THE EVERYWHERE IDENTITIES + CAPSTONES.  `witnessFieldDeriv_eq_gatedDerivRepProd` (and the order-2
     diagonal `witnessFieldDeriv2_eq_gatedDeriv2RepProd`): the raw derivative kernel EQUALS the product
     representative at every `w`, via the same three-way dichotomy (`w.2.2 ∉ K` / `w.2.2 ∈ K, w.1 ≤ 0`
     / `w.2.2 ∈ K, 0 < w.1`).  Then `firstFieldPd_prod_measurable` /
     `firstFieldPd_prod_stronglyMeasurable` (conjunct 2) and `secondFieldPd_prod_diag_measurable`
     (conjunct 3 diagonal).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HEmeasBorelAudit

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open scoped Topology BigOperators ContDiff

namespace QIQTH.GatedDerivRepProduct

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — G-a: the VARYING-FIELD-POINT first-derivative representative + measurability.
    ############################################################################### -/

/-- **`gatedDerivRepProd` — the product-coordinate measurable representative of `witnessFieldDeriv`.**
    Field point `w.2.1`, base `w.2.2`, time `w.1`; carried first-jet field
    `Pfield : base → fieldpt → dir → ℝ`.  The `w.2.2 ∈ K`-indicator of the order-1 on-gate closed form
    (`witnessFieldDeriv_gate_eq`), with the field point now a product coordinate.  NOT `a₁ = R/6`. -/
noncomputable def gatedDerivRepProd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) : ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * (-(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)

/-- **★ `gatedDerivRepProd_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the product
    representative, from `hKmeasSet` (`MeasurableSet K`), `hChartMeas` (Borel chart jointly in
    base+fieldpt), `hPmeas` (jet field), `hAmpMeas`/`hAmpDerivMeas` (amplitude + its field-`pd`).
    `gaussDdim` factor via `gaussDdim_uncurry_measurable`; the `w.2.2 ∈ K` indicator set is measurable
    (`measurable_snd.snd`).  NO continuity.  NOT `a₁ = R/6`. -/
theorem gatedDerivRepProd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)) :
    Measurable (gatedDerivRepProd g gi hC hK a b k Pfield) := by
  unfold gatedDerivRepProd
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hSum : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hChartMeas).mul (hPmeas j)
  have hSc : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hSum.neg.div (measurable_const.mul measurable_fst)
  exact (((hG.mul hSc).mul hAmpMeas).add (hG.mul hAmpDerivMeas)).indicator
    (measurable_snd.snd hKmeasSet)

/-- **★ `witnessFieldDeriv_eq_gatedDerivRepProd` — THE PRODUCT EVERYWHERE IDENTITY.**  The raw first
    field-derivative kernel EQUALS the product representative at every `w = (τ,p,q)`, via the three-way
    dichotomy: `w.2.2 ∉ K` (both `0`), `w.2.2 ∈ K` ∧ `w.1 ≤ 0` (both `0`, shared `gaussDdim` factor
    vanishes), `w.2.2 ∈ K` ∧ `0 < w.1` (the on-gate formula `witnessFieldDeriv_gate_eq`, using the
    carried per-field-point jet/openness data `hgate`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_gatedDerivRepProd (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2
        = gatedDerivRepProd g gi hC hK a b k Pfield w := by
  intro w
  simp only [gatedDerivRepProd]
  by_cases hzK : w.2.2 ∈ K
  · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hpS, hjet, hamp⟩ := hgate w hzK hτ
      exact witnessFieldDeriv_gate_eq g gi hC hK S a b k w.1 hτ w.2.2 hzK hSopen w.2.1 hpS
        (Pfield w.2.2 w.2.1) hjet hamp
    · rw [not_lt] at hτ
      rw [QIQTH.GatedDInstantiation.witnessFieldDeriv_eq_zero_of_nonpos hn g gi hC hK S a b k
            w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    exact witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b k w.1 w.2.1 w.2.2 hzK

/-- **★★ `firstFieldPd_prod_measurable` — G-a, the per-direction product-coordinate first-`pd`
    measurability.**  The joint `(τ,p,q)`-Borel measurability of the raw first field-derivative kernel
    with the FIELD POINT VARYING, via the product everywhere identity glued to `gatedDerivRepProd_measurable`.
    The varying-field-point extension of `GatedDInstantiation.witnessFieldDeriv_measurable_of_gateEq`.
    NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_measurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (k : Fin n) (Pfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
          (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2)
      = gatedDerivRepProd g gi hC hK a b k Pfield := by
    funext w
    exact witnessFieldDeriv_eq_gatedDerivRepProd hn g gi hC hK S a b k Pfield hgate w
  rw [hrw]
  exact gatedDerivRepProd_measurable g gi hC hK a b k Pfield hKmeasSet hChartMeas hPmeas
    hAmpMeas hAmpDerivMeas

/-- **★★ `firstFieldPd_prod_stronglyMeasurable` — BorelDischargeSurface CONJUNCT (2), CONCRETE.**  For
    the concrete gated witness `G := vanVleckGatedWitness g gi hC hK S a b`,
      `∀ k, StronglyMeasurable (fun w => pd (fun x => G w.1 x w.2.2) k w.2.1)`,
    the EXACT shape of `HEmeasBorelAudit.BorelDischargeSurface`'s second conjunct.  Each fibre `k`
    supplies (via `hcar`) its field-point-dependent first jet field and the factor measurabilities +
    on-gate data; the pd equals `witnessFieldDeriv … k w.1 w.2.1 w.2.2` by definition, so
    `firstFieldPd_prod_measurable` closes it, and ℝ-valued `Measurable ⟹ StronglyMeasurable`.
    CONTINUITY-FREE.  NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_stronglyMeasurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (hKmeasSet : MeasurableSet K)
    (hcar : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
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
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)) :
    ∀ k : Fin n, StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) k w.2.1) := by
  intro k
  obtain ⟨Pfield, hChartMeas, hPmeas, hAmpMeas, hAmpDerivMeas, hgate⟩ := hcar k
  exact (firstFieldPd_prod_measurable hn g gi hC hK S a b k Pfield hKmeasSet hChartMeas hPmeas
    hAmpMeas hAmpDerivMeas hgate).stronglyMeasurable

/-! ###############################################################################
    ### §B — G-b (DIAGONAL slice): the product-coordinate second-derivative representative.

    ⚠  G-b GAP NOTE.  The banked order-2 on-gate closed form `witnessFieldDeriv2_gate_eq` /
    `ChartJetHessian.gaussComp_amp_pd_pd` is the DIAGONAL Hessian `pd_i (pd_i …)` (one direction `i`).
    The full `BorelDischargeSurface` conjunct (3) needs `pd_i (pd_j …)` for ALL `i, j` — the MIXED
    off-diagonal second field-`pd`.  Its closed form is a genuinely NEW Leibniz–Gaussian normal form
    (mixed Gaussian second moments `∂_i ∂_j G`, cross jet terms `Pᵢ·Pⱼ`, `∂_i ∂_j A`), not the
    diagonal `gaussComp_amp_pd_pd`.  This file therefore discharges only the DIAGONAL slice of conjunct
    (3) — the varying-field-point extension of `SecondDerivEnvelope.gatedDeriv2Rep` (`i = i`).  The
    mixed case is deferred to a follow-on brick supplying `gaussComp_amp_pd_pd_mixed`.
    ############################################################################### -/

/-- **`gatedDeriv2RepProd` — the product-coordinate (diagonal) representative of `witnessFieldDeriv2`.**
    Field point `w.2.1`, base `w.2.2`, time `w.1`; carried first/second jet fields
    `Pfield : base → fieldpt → dir → ℝ`, `Qfield : base → fieldpt → dir → ℝ`.  The `w.2.2 ∈ K`-indicator
    of the diagonal order-2 on-gate closed form (`witnessFieldDeriv2_gate_eq`).  NOT `a₁ = R/6`. -/
noncomputable def gatedDeriv2RepProd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Point n → Fin n → ℝ) :
    ℝ × Point n × Point n → ℝ :=
  Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K}
    (fun w : ℝ × Point n × Point n =>
      gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
          * ((∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) ^ 2
                / (4 * w.1 ^ 2)
              - ((∑ j, Pfield w.2.2 w.2.1 j ^ 2)
                  + (∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Qfield w.2.2 w.2.1 j))
                / (2 * w.1))
          * chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1
        + 2 * (gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
              * (-(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j)
                  / (2 * w.1)))
            * pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1
        + gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)
            * pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1)

/-- **★ `gatedDeriv2RepProd_measurable`.**  Joint `(τ,p,q)`-Borel measurability of the product diagonal
    order-2 representative, from the carried factor measurabilities (chart, first/second jet fields,
    amplitude and its first/second field-`pd`s).  `gaussDdim` via `gaussDdim_uncurry_measurable`; the
    `1/τ²`/`1/τ` denominators are `measurable_fst`-built (measurability, not integrability).  NO
    continuity.  NOT `a₁ = R/6`. -/
theorem gatedDeriv2RepProd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hQmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1)) :
    Measurable (gatedDeriv2RepProd g gi hC hK a b i Pfield Qfield) := by
  unfold gatedDeriv2RepProd
  have hG : Measurable
      (fun w : ℝ × Point n × Point n =>
        gaussDdim w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1)) :=
    gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hChartMeas)
  have hVP : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hChartMeas).mul (hPmeas j)
  have hPP : Measurable
      (fun w : ℝ × Point n × Point n => ∑ j, Pfield w.2.2 w.2.1 j ^ 2) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact (hPmeas j).pow_const 2
  have hVQ : Measurable
      (fun w : ℝ × Point n × Point n =>
        ∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Qfield w.2.2 w.2.1 j) := by
    refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp hChartMeas).mul (hQmeas j)
  have hden2 : Measurable (fun w : ℝ × Point n × Point n => 4 * w.1 ^ 2) :=
    measurable_const.mul (measurable_fst.pow_const 2)
  have hden1 : Measurable (fun w : ℝ × Point n × Point n => 2 * w.1) :=
    measurable_const.mul measurable_fst
  have hHess : Measurable
      (fun w : ℝ × Point n × Point n =>
        (∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) ^ 2
            / (4 * w.1 ^ 2)
          - ((∑ j, Pfield w.2.2 w.2.1 j ^ 2)
              + (∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Qfield w.2.2 w.2.1 j))
            / (2 * w.1)) :=
    ((hVP.pow_const 2).div hden2).sub ((hPP.add hVQ).div hden1)
  have hGrad : Measurable
      (fun w : ℝ × Point n × Point n =>
        -(∑ j, uniformInverseChart g gi hC hK w.2.2 w.2.1 j * Pfield w.2.2 w.2.1 j) / (2 * w.1)) :=
    hVP.neg.div hden1
  exact ((((hG.mul hHess).mul hAmpMeas).add
      ((measurable_const.mul (hG.mul hGrad)).mul hAmpDerivMeas)).add
      (hG.mul hAmpDeriv2Meas)).indicator (measurable_snd.snd hKmeasSet)

/-- **★ `witnessFieldDeriv2_eq_gatedDeriv2RepProd` — THE PRODUCT DIAGONAL EVERYWHERE IDENTITY.**  The
    raw diagonal second field-derivative kernel EQUALS the product representative at every `w`, via the
    three-way dichotomy (`w.2.2 ∉ K` / `w.2.2 ∈ K, w.1 ≤ 0` / `w.2.2 ∈ K, 0 < w.1`, the on-gate
    diagonal order-2 formula `witnessFieldDeriv2_gate_eq`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv2_eq_gatedDeriv2RepProd (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Point n → Fin n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ y j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) j)
          (Pfield w.2.2 y j) (y i)) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => Pfield w.2.2 (Function.update w.2.1 i s) j) (Qfield w.2.2 w.2.1 j) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1) :
    ∀ w : ℝ × Point n × Point n,
      witnessFieldDeriv2 g gi hC hK S a b i w.1 w.2.1 w.2.2
        = gatedDeriv2RepProd g gi hC hK a b i Pfield Qfield w := by
  intro w
  simp only [gatedDeriv2RepProd]
  by_cases hzK : w.2.2 ∈ K
  · rw [Set.indicator_of_mem (show w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    by_cases hτ : 0 < w.1
    · obtain ⟨hSopen, hpS, hjetV, hjetP, hamp1, hamp2⟩ := hgate w hzK hτ
      exact QIQTH.SecondDerivEnvelope.witnessFieldDeriv2_gate_eq g gi hC hK S a b i w.1 hτ
        w.2.2 hzK hSopen w.2.1 hpS (Pfield w.2.2) (Qfield w.2.2 w.2.1) hjetV hjetP hamp1 hamp2
    · rw [not_lt] at hτ
      rw [QIQTH.SecondDerivEnvelope.witnessFieldDeriv2_eq_zero_of_nonpos hn g gi hC hK S a b i
            w.1 w.2.1 w.2.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn w.1 (uniformInverseChart g gi hC hK w.2.2 w.2.1) hτ]
      ring
  · rw [Set.indicator_of_notMem (show w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hzK)]
    exact witnessFieldDeriv2_offGate_eq_zero g gi hC hK S a b i w.1 w.2.1 w.2.2 hzK

/-- **★★ `secondFieldPd_prod_diag_measurable` — G-b, the DIAGONAL product-coordinate second-`pd`
    measurability.**  The joint `(τ,p,q)`-Borel measurability of the raw DIAGONAL second field-derivative
    kernel with the field point varying, via the product diagonal identity + `gatedDeriv2RepProd_measurable`.
    Discharges the `i = i` slice of `BorelDischargeSurface` conjunct (3); the mixed `i ≠ j` case needs
    the new off-diagonal closed form (see §B gap note).  NOT `a₁ = R/6`. -/
theorem secondFieldPd_prod_diag_measurable (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (Pfield : Point n → Point n → Fin n → ℝ) (Qfield : Point n → Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1))
    (hPmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
    (hQmeas : ∀ j, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 j))
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1))
    (hAmpDerivMeas : Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1))
    (hAmpDeriv2Meas : Measurable
      (fun w : ℝ × Point n × Point n =>
        pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1))
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
        (∀ y j, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) j)
          (Pfield w.2.2 y j) (y i)) ∧
        (∀ j, HasDerivAt
          (fun s : ℝ => Pfield w.2.2 (Function.update w.2.1 i s) j) (Qfield w.2.2 w.2.1 j) (w.2.1 i)) ∧
        (∀ y, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) ∧
        PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i y) i w.2.1) :
    Measurable (fun w : ℝ × Point n × Point n =>
      witnessFieldDeriv2 g gi hC hK S a b i w.1 w.2.1 w.2.2) := by
  have hrw : (fun w : ℝ × Point n × Point n =>
        witnessFieldDeriv2 g gi hC hK S a b i w.1 w.2.1 w.2.2)
      = gatedDeriv2RepProd g gi hC hK a b i Pfield Qfield := by
    funext w
    exact witnessFieldDeriv2_eq_gatedDeriv2RepProd hn g gi hC hK S a b i Pfield Qfield hgate w
  rw [hrw]
  exact gatedDeriv2RepProd_measurable g gi hC hK a b i Pfield Qfield hKmeasSet hChartMeas hPmeas
    hQmeas hAmpMeas hAmpDerivMeas hAmpDeriv2Meas

end QIQTH.GatedDerivRepProduct

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedDerivRepProduct
#print axioms gatedDerivRepProd_measurable
#print axioms witnessFieldDeriv_eq_gatedDerivRepProd
#print axioms firstFieldPd_prod_measurable
#print axioms firstFieldPd_prod_stronglyMeasurable
#print axioms gatedDeriv2RepProd_measurable
#print axioms witnessFieldDeriv2_eq_gatedDeriv2RepProd
#print axioms secondFieldPd_prod_diag_measurable
end AxiomChecks
