/-
  HCompNearCarryKPrimeBaseFieldCoV — J4-1010: wiring J4-1008's base-slot change-of-variables into
  the LITERAL `kPrime` shape of `hcomp`'s NEAR carry `nb`, at the field point `q₀ := x` — honest
  PARTIAL progress on item (ii) (the base↔field change of variables), at the single-Gaussian layer.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `VanVleckGatedSpatialSymmetry.hcomp`'s per-direction √ε sliver carry `nb`
  (`HCompNearFarSplit.kPrime_sliver_near_far`, J4-860) bounds
      `|∫ s ∫_{ball x ρ} (kPrime … i t s x z)(eⱼ)| ≤ nb`,
  with base point `z` VARYING (slot 1, the K-gated CENTER of `uniformInverseChart`) and field point
  `x` FIXED (slot 2, the eval point).  Item (ii) of `nb`'s STEP-4c deliverable is the base↔field
  change of variables `v = uniformInverseChart g gi hC hK z x` transporting `∫_z` onto a chart image.

  J4-882 (`HCompNearCarryChartSurfaceWired.kPrime_apply_single_on_gate_eq_mixedNormalForm`) gave the
  on-gate closed form of the concrete `kPrime` component as a 4-term mixed Leibniz–Gaussian normal
  form, EACH term carrying the common base-slot Gaussian factor `G := gaussDdim (t−s) (U z x)`.
  J4-1008 (`BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_gaussian_change_variables_generalK`)
  gave, for GENERAL `q₀ ∈ interior K`, the Layer-B change-of-variables identity for ANY amplitude `B`:
      `∫ z in S', gaussDdim τ (U z q₀) · B z = ∫ w in W''S', gaussDdim τ w · (B (V w) / |det|)`,
  but explicitly did NOT wire it into the literal `kPrime` shape.

  THIS FILE composes the two, at `q₀ := x` (the field point):
    • `kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp` (★ BRICK 1) — the pure `ring` factorization
      of J4-882's 4-term normal form exhibiting the common `G` factor:
          `(kPrime … i t s x z)(eⱼ) = gaussDdim (t−s) (U z x) · Bfac(z)`,
      `Bfac(z) := Levi(s,z)·(hsMixed·A + grⱼ·∂ⱼA + grᵢ·∂ᵢA + ∂ⱼ∂ᵢA)`.  This is the EXACT
      `gaussDdim τ (U z x) · B z` shape J4-1008's CoV consumes — the object that makes the CoV
      APPLICABLE to the literal `kPrime` integrand.
    • `kPrime_baseField_CoV_of_factorization` (BRICK 2, CONDITIONAL ADAPTER) — instantiating J4-1008's
      CoV at `q₀ := x` (needs `x ∈ interior K`) and rewriting the LHS back to `∫ kPrime` via the
      factorization hypothesis `hfac` (dischargeable pointwise on the gate by BRICK 1):
          `hfac → ∫ z in S', (kPrime … x z)(eⱼ) = ∫ w in W''S', gaussDdim (t−s) w · (Bfac(V w)/|det|)`.
      This is the FIRST wiring of the base-slot CoV into the literal `kPrime` shape (which J4-1008's
      own docstring, part (b) of "WHAT THIS FILE DOES NOT DO", explicitly flagged as unwired).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is
  the pure COMPOSITION of two banked results (J4-882's on-gate normal form + J4-1008's abstract CoV),
  and lands ONLY at the SINGLE-GAUSSIAN change-of-variables layer.  It does **NOT** discharge item (ii)
  as `nb` ultimately consumes it, and is honestly PARTIAL (Sol `gpt-5.6-sol`, high, 2026-08-22,
  plan-reviewed before Lean).  The precise remaining residuals for `nb` (Sol-enumerated, none supplied
  here):
    (r1) a CoV neighbourhood `S' ⊆ interior K` (J4-882's normal form is ON-GATE, `z ∈ K`);
    (r2) J4-882's full on-gate jet/differentiability bundle uniformly over `z ∈ S'`;
    (r3) reconcile the original domain `ball x ρ` with the IFT set `S'`;
    (r4) reconcile the chart image `W''S'` with `ball 0 R`;
    (r5) the slot-reversal identity connecting `U z x`, `U x z`, and `T_x = terminalVelAt`;
    (r6) the ANTISYMMETRIZATION producing the near-isometry DIFFERENCE `G_τ(T_x v) − G_τ(v)` — the
         CoV lands on a SINGLE Gaussian `gaussDdim τ w`, NOT the difference the J4-879 template
         (`terminalVelAt_chartReplace_sliver_bound`) consumes; producing the difference and cancelling
         the reference term is a GENUINELY SEPARATE, still-open mechanism the CoV does not supply.
  BRICK 2 is a CONDITIONAL adapter: `hfac` is a hypothesis (satisfiable — `gaussDdim > 0`, so
  `Bfac := kPrime/gaussDdim` makes it hold, and BRICK 1 supplies the MEANINGFUL geometric `Bfac` on
  the gate), NOT discharged over the IFT-selected `S'` (that would need r1+r2).  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryChartSurfaceWired
import QIQTH.BaseSlotM1M4Assembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryKPrimeBaseFieldCoV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### BRICK 1 — the common-Gaussian factorization of `kPrime`'s mixed normal form.
    ############################################################################### -/

/-- **★ `kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp` — BRICK 1.**  The pure `ring`
    factorization of J4-882's on-gate mixed Leibniz–Gaussian normal form, pulling the common base-slot
    Gaussian factor `G := gaussDdim (t−s) (U z x)` out of all four summands:
        `(kPrime … i t s x z)(Pi.single j 1)
            = gaussDdim (t−s) (U z x) · Bfac`,
    `Bfac := Levi(s,z)·(hsMixed·A + grⱼ·∂ⱼA + grᵢ·∂ᵢA + ∂ⱼ∂ᵢA)`, with the same scalar shorthands as
    J4-882.  This exhibits the concrete `kPrime` integrand in the EXACT `gaussDdim τ (U z x) · B z`
    shape that `ChartGaussianChangeVar.chart_gaussian_change_variables` (and hence J4-1008's base-slot
    CoV corollary) consumes.  Same on-gate hypothesis bundle as J4-882.  NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) (x z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (hx : x ∈ S z) (hτ : 0 < t - s)
    (hd : DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ y k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y j σ) k) (PI y k) (y j))
    (hJetVj : ∀ y k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ y k) (y i))
    (hJetQ : ∀ k, HasDerivAt
      (fun σ : ℝ => PJ (Function.update x j σ) k) (Q k) (x j))
    (hAmpj1 : ∀ y, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
    (hAmpi1 : PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x)
    (hAmp2 : PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) :
    (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
      = gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
          * (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              * (((∑ k, uniformInverseChart g gi hC hK z x k * PI x k)
                      * (∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (4 * (t - s) ^ 2)
                    - ((∑ k, PI x k * PJ x k)
                        + (∑ k, uniformInverseChart g gi hC hK z x k * Q k)) / (2 * (t - s)))
                    * chartFieldAmp g gi hC hK a b (t - s) z x
                  + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (2 * (t - s)))
                      * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
                  + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI x k) / (2 * (t - s)))
                      * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
                  + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x)) := by
  rw [QIQTH.HCompNearCarryChartSurfaceWired.kPrime_apply_single_on_gate_eq_mixedNormalForm
        g gi hC hK S a b i j t s x z hz hSopen hx hτ hd PI PJ Q
        hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]
  ring

/-! ###############################################################################
    ### BRICK 2 — the CONDITIONAL literal-`kPrime` base↔field change of variables.
    ############################################################################### -/

/-- **`kPrime_baseField_CoV_of_factorization` — BRICK 2 (CONDITIONAL ADAPTER).**  Instantiating
    J4-1008's base-slot change of variables at the field point `q₀ := x` (needs `x ∈ interior K`),
    and rewriting the LHS back to the LITERAL `kPrime` integral via the factorization hypothesis
    `hfac : ∀ z ∈ S', (kPrime … x z)(eⱼ) = gaussDdim (t−s) (U z x) · Bfac z` (dischargeable pointwise
    on the gate by BRICK 1):
        `hfac → (∫ z in S', (kPrime … i t s x z)(Pi.single j 1))
                  = ∫ w in W''S', gaussDdim (t−s) w · (Bfac (V w) / |det (fderiv W (V w))|)`,
    `W := fun p => uniformInverseChart g gi hC hK p x`.  This is the FIRST wiring of the base-slot CoV
    into the literal `kPrime` shape.  `hfac` is a HYPOTHESIS (satisfiable — `gaussDdim > 0`; BRICK 1
    supplies the MEANINGFUL geometric `Bfac` on the gate), NOT discharged over the IFT-selected `S'`
    (see file firewall residuals r1/r2).  The CoV lands on a SINGLE Gaussian `gaussDdim (t−s) w`, NOT
    the near-isometry DIFFERENCE `G_τ(T_x v) − G_τ(v)` the J4-879 template consumes (residual r6).
    NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_factorization
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) {x : Point n} (hxint : x ∈ interior K)
    (Bfac : Point n → ℝ) :
    ∃ (S' : Set (Point n)) (V : Point n → Point n),
      IsOpen S' ∧ x ∈ S' ∧
      ((∀ z ∈ S', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
            = gaussDdim (t - s) (uniformInverseChart g gi hC hK z x) * Bfac z) →
        (∫ z in S', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
          = ∫ w in (fun p => uniformInverseChart g gi hC hK p x) '' S',
              gaussDdim (t - s) w
                * (Bfac (V w)
                    / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p x) (V w)).det|)) := by
  obtain ⟨S', V, hopen, hxS', heq⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_gaussian_change_variables_generalK
      g gi hC hK hxint (t - s) Bfac
  refine ⟨S', V, hopen, hxS', ?_⟩
  intro hfac
  have hcong : (∫ z in S', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = ∫ z in S', gaussDdim (t - s) (uniformInverseChart g gi hC hK z x) * Bfac z :=
    setIntegral_congr_fun hopen.measurableSet (fun z hz => hfac z hz)
  rw [hcong]
  exact heq

end QIQTH.HCompNearCarryKPrimeBaseFieldCoV

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryKPrimeBaseFieldCoV
#print axioms kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp
#print axioms kPrime_baseField_CoV_of_factorization
end AxiomChecks
