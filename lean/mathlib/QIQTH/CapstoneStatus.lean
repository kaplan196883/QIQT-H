/-
  CapstoneStatus — J4-146: the CAPSTONE INVENTORY.

  This is an ASSEMBLY / INVENTORY brick.  It does NOT prove any new analysis.  It threads the
  ~30 banked bricks of the a₁ = R/6 campaign (J4-101 … J4-145) into the single reduced capstone
  `ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`, SPECIALIZED to the
  concrete `N = 1` gated van-Vleck witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, and
  packages the result as ONE final-reduction theorem `a1_R6_of_residue` whose hypotheses are exactly
  the genuinely-remaining residue of the whole programme.

  ⚠ THIS IS NOT `a₁ = R/6`.  The residue below is REAL and OPEN.  `a1_R6_of_residue` is the
  campaign's state-of-the-art: the diagonal short-time coefficient theorem
      `trueHeatKernel H_G (leviSeries (heatOp g gi H_G)) t 0 0`
        `= G_t(0)ⁿ · (1 + (∑ᵢ Ricᵢᵢ / 6)·t + t²·(…tail… + heatConv-remainder/(G_t(0)ⁿ·t²)))`
  (with the heat-equation solving fact), CONDITIONAL on the explicit machine-checked residue.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## S1 — the per-input supply table (input → banked supplier → its own carries).

  The capstone consumes 17 hypotheses.  Against the concrete witness `H_G` they split as follows.

    STRUCTURAL (discharged here, genuinely, in `a1_R6_of_residue`):
      • `hHdiag`  ⟸ `gatedWitnessN1_diag_eval_vanVleck` (J4-105) — the `N = 1` diagonal identification
                     `H_G t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0`.
                     Carries: `0 ∈ K`, `0 ∈ S 0`, `W₀ 0 = 0` (the last ⟸ `uniformInverseChart_zero`).
      • `hDH`     ⟸ `gatedWitnessN1_hDH` (J4-112, D3) — `t`-differentiability of `u ↦ H_G u 0 0`
                     via the explicit `(√(4πu))⁻ⁿ·(a₀+a₁u)` diagonal form.  Same three carries + `0 < t`.

    GAUGE (the capstone's own geometric inputs, KEPT as hypotheses — genuine RNC/metric data for a
    normal-coordinate metric at the origin; satisfiable, never the conclusion):
      • `hg, hg0, hgi, hΓ, hdg0, htr, hsrc` — `g(0)=δ`, `Γ(0)=0`, `∂g(0)=0`, the `−⅔·Ric` Hessian-trace
        `htr`, and transport-source smoothness `hsrc`.

    ANALYTIC-RESIDUE (KEPT as hypotheses of `a1_R6_of_residue` — the genuinely-open analytic surface,
    each with a banked REDUCTION supplier documented for the discharge route):
      • `hEboundW_le` ⟸ `gatedWitnessN1_hEboundW_le_vanVleck_final` (J4-115, CoeffU1Fix) — LANDED as
        an existential; re-exported as `capstone_hEboundW_le_supplied`.  Residue when specialized to a
        chosen `(a,b,C,S)`: none beyond the gauge/coefficient-smoothness inputs it already consumes.
      • `hInt`        ⟸ `gatedWitnessN1_hInt_of_kernelContinuity` (J4-110, GatedWitnessEmeas) — hInt
        from `{Continuous H_G, Continuous ∂ⱼH_G, gi/Γ measurable}`; re-exported as
        `capstone_hInt_supplied`.  Residue: the flow's joint base-point `q`-regularity (the 3×-surfacing
        ODE-measurability wall).
      • `hDuhamel`    ⟸ `hDuhamel_leviSeries_final` / `hDuhamel_final_of_f2carries` (J4-123 / J4-145)
        ⊕ `hDuhamel_penultimate` (J4-142).  Residue: `hDaLimLU` (the sole hard loc-unif LapTrunc limit,
        whose analytic core `witness_sliver2_grand` (J4-137) IS proven) + the F2 family `hCross`,
        `hMeasFII`, `hInnerCont` + the boundary-interface + domination families.
      • `hInter`      ⟸ `heatConv_leviSeries_interchange` (J4-131/LeviInterchange).  Residue: the
        `hEbound/hEzero/hEmeas` Levi carries.
      • `hDConv`      ⟸ `hDConv_gatedWitnessN1_of_delta_final` (J4-117) ⊕ `hDelta_gatedWitnessN1_final`
        (J4-120).  Residue: `hDelta` (Lemma-3.14 delta-family; the singular content, boundary term never
        evaluated — DISCHARGED to `hDaLim`) + `hMeasFII` + the joint `HasFDerivAt` engine family.
      • `hCH`         — `ContDiffAt ℝ 2 (fun p => H_G t p 0) 0`.  The `C²` chart tower makes this
        satisfiable (`uniformInverseChart` is `ContDiffOn ℝ 2`); KEPT.
      • `hCConv`      — `ContDiffAt ℝ 2 (fun p => heatConv H_G (leviSeries …) t p 0) 0`.  Rides on the
        spatial-`C²` convolution regularity (the `hLap`/`hInterchange` machinery); KEPT.

  ## S2 — `a1_R6_of_residue`: the capstone SPECIALIZED to `H_G`, with the two STRUCTURAL slots
     (`hHdiag`, `hDH`) genuinely discharged and the GAUGE + ANALYTIC-RESIDUE surface carried.  See its
     conclusion (verbatim) and residue below.  `N` is pinned to `1` (the witness diagonal is order-1;
     the `Finset.Ico 2 (1+1) = ∅` tail then collapses).

  ## S3 — THE COMPLETE, GROUPED RESIDUE of `a1_R6_of_residue` (honest gap map):
    GATE DATA        : `hChr` (Christoffel `C∞`), `hK` (compact `K`), the gate `S`, radii `0<a<b`,
                       origin memberships `0∈K`, `0∈S 0`.
    GAUGE            : `hg, hg0, hgi, hΓ, hdg0, htr, hsrc`  (RNC metric 2-jet + `−⅔Ric` + source `C∞`).
    ANALYTIC-RESIDUE : `hEboundW_le` (width-2 residual bound — LANDED existentially),
                       `hInt` (iterated-conv integrability — residue = joint-`q` flow regularity),
                       `hDuhamel` (Duhamel identity — residue = `hDaLimLU` + F2 + boundary/domination),
                       `hInter` (tsum↔heatConv interchange — residue = Levi `hEbound/hEzero/hEmeas`),
                       `hDConv` (diagonal-conv `t`-differentiability — residue = `hDelta`/Lemma 3.14),
                       `hCH`, `hCConv` (spatial `C²` of `H_G` and of the convolution slice).
    The irreducible physical/analytic frontier inside these is: the joint base-point `q`-regularity of
    the RNC flow map (ODE-measurability), and the boundary delta-family loc-unif limit `hDaLimLU`
    (Rosenberg Lemma 3.14 / Gilkey §1.6 in analytic form) — every OTHER conjunct has a landed reduction.

  NO `sorry`.  NO new axioms.  NO `expRho` in statements.  All carried hypotheses are satisfiable,
  non-vacuous, and never equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConcreteDominations
import QIQTH.ConvApproximants
import QIQTH.GatedWitnessEmeas

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound QIQTH.PullbackMetric
open scoped BigOperators Topology Interval

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### S1 — the per-input supply lemmas (at `H := vanVleckGatedWitness g gi hChr hK S a b`). -/

/-- **S1 — `capstone_hHdiag_supplied`.**  The capstone's `hHdiag` slot for the concrete `N = 1` gated
    van-Vleck witness `H_G`, discharged VERBATIM by `gatedWitnessN1_diag_eval_vanVleck` (J4-105) with
    the origin-fixing chart fact `uniformInverseChart_zero`.  Genuine carries: `0 ∈ K`, `0 ∈ S 0`,
    `0 < a < b`.  NOT `a₁ = R/6`. -/
theorem capstone_hHdiag_supplied (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) :
    vanVleckGatedWitness g gi hChr hK S a b t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
  gatedWitnessN1_diag_eval_vanVleck g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t hK0 hS0
    (uniformInverseChart_zero g gi hChr hK hK0)

/-- **S1 — `capstone_hDH_supplied`.**  The capstone's `hDH` slot for `H_G`, discharged by
    `gatedWitnessN1_hDH` (J4-112, D3).  NOT `a₁ = R/6`. -/
theorem capstone_hDH_supplied (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t : ℝ) (ht : 0 < t)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) :
    DifferentiableAt ℝ (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 0) t :=
  gatedWitnessN1_hDH g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t ht hK0 hS0
    (uniformInverseChart_zero g gi hChr hK hK0)

/-- **S1 — `capstone_hEboundW_le_supplied`.**  The capstone's `hEboundW_le` slot, re-exported from the
    LANDED existential `gatedWitnessN1_hEboundW_le_vanVleck_final` (J4-115): there EXIST gate parameters
    `(a,b,C,S)` for which the concrete `N = 1` gated van-Vleck witness obeys the `(0,t]`-restricted
    width-2 primitive `|heatOp g gi H_G τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q`.  This is the
    existential form; `a1_R6_of_residue` carries the specialized-`(a,b,C,S)` instance directly.
    NOT `a₁ = R/6`. -/
theorem capstone_hEboundW_le_supplied (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
      ∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  gatedWitnessN1_hEboundW_le_vanVleck_final g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0

/-! ### S2 — THE FINAL REDUCTION. -/

/-- **★★★ J4-146 (S2) — `a1_R6_of_residue`: the campaign's STATE-OF-THE-ART.**  The reduced true-kernel
    diagonal `a₁ = R/6` capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`, SPECIALIZED to
    the concrete `N = 1` gated van-Vleck witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, with
    the two STRUCTURAL slots (`hHdiag`, `hDH`) GENUINELY DISCHARGED from the banked suppliers
    (`gatedWitnessN1_diag_eval_vanVleck` ⊕ `uniformInverseChart_zero`; `gatedWitnessN1_hDH`), and the
    GAUGE + ANALYTIC-RESIDUE surface carried as the explicit, honest, still-open residue.

    CONCLUSION: `H_G`'s Levi-corrected true kernel BOTH solves the heat equation on the diagonal AND
    has the `a₁ = R/6` short-time expansion (the `∑ᵢ Ricᵢᵢ / 6` leading correction), with an explicit
    heat-convolution remainder.  `N` is pinned to `1`, so the transport tail `∑ k ∈ Ico 2 (1+1)` is the
    empty sum.

    ⚠ NOT `a₁ = R/6`.  The residue (grouped in the signature) remains: GATE DATA + GAUGE + the seven
    ANALYTIC hypotheses `hEboundW_le / hInt / hDuhamel / hInter / hDConv / hCH / hCConv`, each with a
    banked reduction supplier (see the header S1/S3 census).  The irreducible frontier inside is the
    RNC flow's joint base-point `q`-regularity and the boundary delta-family limit `hDaLimLU`. -/
theorem a1_R6_of_residue (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    -- GATE DATA (needed to build and pin the concrete witness `H_G`)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (H : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b)
    -- GAUGE (the capstone's own geometric inputs)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- ANALYTIC-RESIDUE (at `H`; each with a banked reduction supplier — see header)
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  subst hHeq
  -- STRUCTURAL discharges from the banked suppliers.
  have hHdiag : vanVleckGatedWitness g gi hChr hK S a b t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    capstone_hHdiag_supplied g gi hChr hK S a b ha hab t hK0 hS0
  have hDH : DifferentiableAt ℝ (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 0) t :=
    capstone_hDH_supplied g gi hChr hK S a b ha hab t ht hK0 hS0
  -- The reduced capstone, fully instantiated at `N = 1` and `H := H_G`.
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted_C2 g gi Ric 1 le_rfl t ht
    (vanVleckGatedWitness g gi hChr hK S a b) C hCnn hg hg0 hgi hΓ hdg0 htr hsrc
    hHdiag hEboundW_le hInt hDuhamel hInter hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms capstone_hHdiag_supplied
#print axioms capstone_hDH_supplied
#print axioms capstone_hEboundW_le_supplied
#print axioms a1_R6_of_residue
end AxiomChecks
