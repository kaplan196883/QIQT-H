/-
  HCompNearCarryChartSurfaceWired — J4-882: the CONCRETE `kPrime`-through-mixed-normal-form WIRING
  (item (i) of `hcomp`'s NEAR carry `nb`), on the gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `VanVleckGatedSpatialSymmetry.hcomp`'s per-direction √ε sliver carry `nb`
  (`HCompNearFarSplit.kPrime_sliver_near_far`, J4-860) bounds
      `|∫ s ∫_{ball x ρ} (kPrime … i t s x z)(eⱼ)| ≤ nb`.
  J4-788 (`KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd`) identified the concrete component
      `(kPrime … i t s x z)(eⱼ) = Levi(s,z) · ∂ⱼ∂ᵢ H_G(field = x, base = z)`
  (the abstract CLM component = Levi factor × the MIXED second field partial).  J4-218
  (`ChartJetHessianMixed.witnessMixed_gate_eq`) gave the exact ON-GATE closed form of that mixed second
  field partial as the Leibniz–Gaussian normal form.

  THIS FILE composes the two: on the gate (`z ∈ K`, field point `x ∈ S z`, `0 < t − s`), the concrete
  `kPrime` component EQUALS the Levi factor times the explicit mixed Leibniz–Gaussian normal form —
      `(kPrime … i t s x z)(eⱼ)
          = Levi(s,z) · [ G_τ(U z x)·hsMixed·A + (G·grⱼ)·∂_j A + (G·grᵢ)·∂_i A + G·∂_j∂_i A ]`,
      `τ := t − s`,  `U z x := uniformInverseChart g gi hC hK z x`,  `G := gaussDdim τ (U z x)`,
      `hsMixed := ⟨U,Pi⟩·⟨U,Pj⟩/(4τ²) − (⟨Pi,Pj⟩ + ⟨U,Q⟩)/(2τ)`,
      `grⱼ := −⟨U,Pj⟩/(2τ)`,  `grᵢ := −⟨U,Pi⟩/(2τ)`.
  This is exactly the object item (i) of `nb` asks for: the concrete `kPrime` component brought into the
  chart-replacement-ready normal form whose base-slot Gaussian factor `G_τ(U z x)` the J4-880 evenness
  link (`gaussDdim_reversal_link`, `G_τ(U z x) = G_τ(T_x(U x z))`) and the J4-879/880 prefactor sliver
  estimate consume — after the (still-open) base↔field change of variables `v = uniformInverseChart x z`
  transports `ball x ρ → ball 0 R`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  pure COMPOSITION of two already-banked EQUALITIES (J4-788 CLM-component identity + J4-218 on-gate mixed
  normal form) — a pointwise algebraic wiring, never a bound.  It does NOT close `nb`: the residual is
  (ii) the base↔field change of variables `v = uniformInverseChart x z` (which needs the chart to be a
  C¹ diffeomorphism on `ball x ρ` — the JOINT-`C²`-CHART wall, the SAME single named wall shared by
  `hbint` and `hCConv`), plus the antisymmetrization that produces the `G_τ(T_x v) − G_τ(v)` chart-
  replacement DIFFERENCE the near cancellation rests on.  Every hypothesis is a genuine on-gate
  first/second field jet (`HasDerivAt`), a genuine amplitude `PdiffAt`, or the genuine field-
  differentiability `hd` of the first field-derivative kernel — all satisfiable on the gate (where the
  witness is the smooth chart-Gaussian), none equal to the conclusion.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.FderivBulkConcrete
import QIQTH.ChartJetHessianMixed
import QIQTH.KPrimeMixedPdBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryChartSurfaceWired

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-882 — `kPrime_apply_single_on_gate_eq_mixedNormalForm`.**  ITEM (i) of `hcomp`'s NEAR
    carry `nb`: the CONCRETE `kPrime` component wired through the MIXED Leibniz–Gaussian normal form,
    on the gate.  For base `z ∈ K`, field point `x ∈ S z`, and `0 < t − s` (write `τ := t − s`,
    `U z x := uniformInverseChart g gi hC hK z x`), given

      • `hd` — field-differentiability of the first field-derivative kernel `witnessFieldDeriv … i τ · z`
        at `x` (J4-788's carry),
      • `Pi`/`Pj` — the first field jets of `U z ·` in the `j`/`i` directions (resp.),
      • `Q`   — the mixed second field jet (`∂_j` of the `i`-line `Pj`-jet at `x`),
      • the amplitude `PdiffAt` data `hAmpj1`/`hAmpi1`/`hAmp2`,

    the `j`-th basis component of the abstract CLM derivative kernel `kPrime` equals the field-independent
    Levi factor times the explicit mixed normal form of `∂_j∂_i H_G` at `x`:
      `(kPrime … i t s x z)(Pi.single j 1)
          = Levi(s,z) ·
             ( G_τ(U z x)·[⟨U,Pi⟩⟨U,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨U,Q⟩)/(2τ)]·A
               + (G_τ(U z x)·(−⟨U,Pj⟩/(2τ)))·∂_j A
               + (G_τ(U z x)·(−⟨U,Pi⟩/(2τ)))·∂_i A
               + G_τ(U z x)·∂_j∂_i A ) `,
    `A := chartFieldAmp g gi hC hK a b τ z`.  Route: rewrite `(kPrime …)(eⱼ)` through J4-788 to
    `Levi · pd (pd H_G i) j x`, then rewrite that mixed second field partial through J4-218's on-gate
    closed form `ChartJetHessianMixed.witnessMixed_gate_eq` with the index roles `(i,j)` swapped (so its
    outer/inner `∂` align with J4-788's `∂_j∂_i`).  Pure equality composition; NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_on_gate_eq_mixedNormalForm
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
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        * (gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
              * ((∑ k, uniformInverseChart g gi hC hK z x k * PI x k)
                    * (∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (4 * (t - s) ^ 2)
                  - ((∑ k, PI x k * PJ x k)
                      + (∑ k, uniformInverseChart g gi hC hK z x k * Q k)) / (2 * (t - s)))
              * chartFieldAmp g gi hC hK a b (t - s) z x
            + (gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
                  * (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ x k) / (2 * (t - s))))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
            + (gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
                  * (-(∑ k, uniformInverseChart g gi hC hK z x k * PI x k) / (2 * (t - s))))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
            + gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)
                * pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) := by
  rw [QIQTH.KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd
        g gi hC hK S a b i j t s x z hd,
      QIQTH.ChartJetHessianMixed.witnessMixed_gate_eq
        g gi hC hK S a b j i (t - s) hτ z hz hSopen x hx PI PJ Q
        hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]

end QIQTH.HCompNearCarryChartSurfaceWired

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCompNearCarryChartSurfaceWired
#print axioms kPrime_apply_single_on_gate_eq_mixedNormalForm
end AxiomChecks
