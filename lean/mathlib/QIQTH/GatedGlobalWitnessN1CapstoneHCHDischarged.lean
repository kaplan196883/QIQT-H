/-
  GatedGlobalWitnessN1CapstoneHCHDischarged — the ORDER-`N = 1` partial Seeley–DeWitt capstone with
  BOTH `hEboundW` (J4-774) AND `hCH` GENUINELY DISCHARGED, on the LIVE `TrueKernelA1Reduced`/restricted
  lineage.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS IS.  A pure WIRING ADAPTER that rebases the live J4-774 capstone
  `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged`
  (`GatedGlobalWitnessN1CapstoneEbdDischarged.lean`) onto the `C²`-WEAKENED restricted capstone
  `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` (`ConcreteDominations.lean`, D4 verdict).

  ── THE D4 VERDICT (already banked in `ConcreteDominations.lean`).  The restricted capstone's
     `hCH : ContDiff ℝ ⊤ (fun p => H t p 0)` / `hCConv : ContDiff ℝ ⊤ (…)` are OVERKILL and, worse,
     UNSATISFIABLE for the concrete van-Vleck witness `H_G` (its inverse chart `uniformInverseChart`
     is only `ContDiffOn ℝ 2`, and the hard gate is discontinuous at `∂(S q)`).  These two `⊤` carries
     flow to EXACTLY ONE consumer — `trueHeatKernel_heat_eqn_levi` → `heatOp_add` →
     `laplaceBeltrami_add` — which uses at most TWO spatial derivatives.  So the fully-correct target
     is the `ContDiffAt ℝ 2 … 0` port `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`, which is
     ACTUALLY satisfiable by `H_G` (gate-interiority: `0` is in the open interior of `S 0`, so a whole
     neighborhood of `0` sits inside the gate where the indicator ≡ 1, and there the germ equals the
     ungated `C²` van-Vleck germ).

  ── THE `hCH` DISCHARGE.  The live witness
       `H := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
               (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`
     is DEFINITIONALLY EQUAL to `vanVleckGatedWitness g gi hChr hK S a b` (`ConvApproximants.lean`).
     `InftyRebaseCapstone.hCH_discharge_from_geometry` proves
       `ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) 0`
     from the `C^∞` geometry `{hg, hgiC, hgpos, hg0}` plus the gate-centre facts `0 ∈ S 0` /
     `IsOpen (S 0)` — BOTH exported by `gatedWitnessN1_package_open` (the same package that supplies
     the `(0,t]`-affine `hEboundW`).  So on THIS lineage the `hCH` carry is discharged with NO
     smooth-cutoff redesign: the diagonal capstone never needed the global `⊤` form, only the local
     `C²`-at-`0` form, which the hard gate genuinely satisfies.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  NET REDUCTION vs. J4-774.  The J4-774 capstone carries `{hEmeas, hDuhamel, hDConv, hCH, hCConv}` with
  `hCH`/`hCConv` in the FALSE-as-stated `ContDiff ℝ ⊤` form.  Here `hCH` is DISCHARGED (internally from
  geometry, `C²`-at-`0`) and `hCConv` is WEAKENED from the unsatisfiable `ContDiff ℝ ⊤` to the
  satisfiable `ContDiffAt ℝ 2 … 0`.  Surviving carries drop to
      `{hEmeas, hDuhamel, hDConv, hCConv (ContDiffAt ℝ 2 … 0)}`
  — ONE fewer open hypothesis, and the remaining spatial-regularity carry is now the genuinely-true
  local form rather than an unsatisfiable global one.  Cost: the two standard geometric inputs the
  discharge needs — `hgiC` (inverse-metric `C^∞`) and `hgpos` (positive metric determinant) — both
  satisfiable, neither vacuous nor the conclusion (mirrors `a1_R6_of_residue_inf_v4`, J4-204).

  ⚠ HONEST FIREWALL.  STILL CONDITIONAL; NOT `a₁ = R/6`.  The remaining carries `hEmeas` (base joint
  strong measurability), `hDuhamel`/`hDConv` (Duhamel / diagonal-convolution differentiability),
  `hCConv` (spatial `C²`-at-`0` of the diagonal Duhamel convolution) are genuine, satisfiable analytic
  facts about the order-1 residual — none the conclusion, none vacuous.  No `sorry`, no new axioms,
  no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1Diag
import QIQTH.ConcreteDominations
import QIQTH.GatedWitnessMeas
import QIQTH.GateOpennessExport
import QIQTH.InterchangeLocalRebase
import QIQTH.InftyRebaseCapstone
import QIQTH.CapstoneWiring

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.TransitionAnnulusCont
open QIQTH.GateOpennessExport QIQTH.InterchangeLocalRebase QIQTH.InftyRebaseCapstone
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ The ORDER-1 partial Seeley–DeWitt capstone with `hEboundW` AND `hCH` GENUINELY DISCHARGED.**

    Rebase of `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged` (J4-774) onto the
    `C²`-weakened restricted capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` (D4
    verdict).  The order-1 gated van-Vleck cutoff-parametrix witness
        `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
                 (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`,
    with `a, b, S` (and the `(0,t]`-affine bound + origin gate membership + gate openness) sourced from
    `gatedWitnessN1_package_open`.  `hEboundW` is discharged exactly as in J4-774; ADDITIONALLY `hCH`
    is discharged internally via `hCH_discharge_from_geometry` (the witness being defeq to
    `vanVleckGatedWitness`), and `hCConv` is carried in the satisfiable `ContDiffAt ℝ 2 … 0` form.

    RESULT vs. J4-774: surviving carries `{hEmeas, hDuhamel, hDConv, hCConv (C²-at-0)}` — `hCH`
    discharged, `hCConv` weakened from unsatisfiable `⊤` to satisfiable `C²`-at-`0`.  STILL
    CONDITIONAL; NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_hCH_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n),
      (let H := gatedKernel K S
          (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK));
        StronglyMeasurable (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) →
        heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
            = leviSeries (heatOp g gi H) t 0 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
        DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
        ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n) →
        heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
        ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- Source `a, b, C, S` + the `(0,t]`-affine bound + origin gate membership + gate openness.
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, ha, hab, S, ?_⟩
  intro H hEmeas hDuhamel hDConv hCConv
  -- gate-centre facts, FREE from the package's exported fields.
  have hS0 : (0 : Point n) ∈ S 0 := hmemS0 hK0
  have hSopen : IsOpen (S 0) := hopenS0 hK0
  -- The effective (0,t]-restricted constant.
  have hCeff0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hC0 (by linarith)
  -- Matrix-`1` form of `g 0 = δ`.
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ `hEboundW_le` — the `(0,t]`-restricted affine bound, DISCHARGED from the package.
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun τ p q hτ hτt => hbound t τ p q hτ hτt
  -- the order-1 residual nonpositive-time vanishing (needs `1 ≤ n`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)
  -- the every-ceiling `(0,T]`-local bound family.
  have hlocal : ∀ T : ℝ, 0 < T → ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ τ p q, 0 < τ → τ ≤ T →
        |heatOp g gi H τ p q| ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun T hT => ⟨C * (1 + T), mul_nonneg hC0 (by linarith),
      fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩
  -- `hInt` — the FULL `IterConvIntegrableW`, from the `(0,T]`-LOCAL bound via the `timeCap` producer.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 (C * (1 + t)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas (heatOp g gi H) (C * (1 + t))
      hEzero hEmeas hlocal
  -- `hInter` — the tsum/heatConv interchange from the `(0,T]`-LOCAL data.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    hInter_from_local_data (heatOp g gi H) (C * (1 + t)) t hCeff0 ht
      (fun τ p q hτ hτt => hbound t τ p q hτ hτt) hEzero hEmeas hlocal t ht le_rfl 0 0
  -- ★ `hHdiag` at `N = 1` — GENUINELY TRUE; `hS0` supplied by the package's exported gate membership.
  have hHdiag : H t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    gatedGlobalWitnessN1_diag_hHdiag g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t
      hK0 hS0 (uniformInverseChart_zero g gi hChr hK hK0)
  -- `hDH` diagonal time-differentiability at the order-1 witness.
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitnessN1_diag_hDH g gi hChr hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b S t ht
  -- ★ `hCH` — the spatial-`C²`-at-`0` witness diagonal, DISCHARGED from the `C^∞` geometry.
  -- The live `H` is DEFEQ to `vanVleckGatedWitness g gi hChr hK S a b`, so the discharge lands directly.
  have hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n) :=
    hCH_discharge_from_geometry g gi hChr hK S a b t hK0 hS0 hSopen hg hgiC hgpos hg0'
  -- Close with the `C²`-weakened `(0,t]`-RESTRICTED capstone.
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted_C2 g gi Ric 1 (le_refl 1) t ht H
    (C * (1 + t)) hCeff0 hg hg0' hgi hΓ hdg0 htr hsrc hHdiag hEboundW_le hInt hDuhamel hInter
    hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
