/-
  FlatBaseAbsorb — J4-747 (OPTION B): GROUP-D′ ABSORPTION at the FLAT base metric.

  `HgateOpenFlowballAbsorb.a1_R6_from_data_v4d` carries a base-metric block "group (D′)":
    `gb gib` (base metric + inverse), `hCb` (Christoffel `C^∞`), `hgPull` (the defining
    equation `g = expPullbackMetric gb gib hCb 0`), and the F4 residues `hsymmb`/`hinvb`/`hgb`/
    `hgaugeb`.  This file supplies a CONCRETE base metric — the flat Kronecker metric
    `flatBase = δ` — for which the five *gb-side* residues (`hCb`,`hsymmb`,`hinvb`,`hgb`,`hgaugeb`)
    are ALL discharged as trivial banked facts.  `a1_R6_from_data_v4e` is then `v4d` specialized to
    `gb := gib := flatBase`, so group (D′) collapses to the single defining equation `hgPull`
    (a `g = expPullbackMetric flatBase flatBase … 0` constraint the caller supplies).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It only removes the five gb-side residues of
  group (D′) by committing the base metric to `δ`; it closes NOTHING deeper.  The `g`-side surface is
  UNCHANGED: the raw-chart jet suppliers `hcarTau`/`hcarField`/`hcarField2`, the convergence-trio
  `slots`, and the defining equation `hgPull` are re-exposed verbatim.  The choice `gb = δ` is a
  SATISFIABLE concrete witness (the flat metric genuinely IS symmetric, self-inverse, smooth, and
  origin-gauged), NOT a vacuous antecedent — matching cp466 discipline.  No `sorry`, no `admit`,
  no `:= True`, no new axiom (`std-3` only), no existing file edited.  `a₁ = R/6` stays CONDITIONAL.
-/
import Mathlib
import QIQTH.HgateOpenFlowballAbsorb
import QIQTH.ChristoffelSmooth

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix
open QIQTH.A1R6FromData QIQTH.HGaussAbsorb QIQTH.CurvedHgateGlue
open QIQTH.HeatParametrixOrder QIQTH.GaussianPolyBound QIQTH.RNCDecay
open QIQTH.HgateOpenFlowballAbsorb
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.FlatBaseAbsorb

variable {n : ℕ}

/-- **The flat (Kronecker `δ`) base metric.** -/
def flatBase (_ : Point n) (i j : Fin n) : ℝ := if i = j then 1 else 0

@[simp] theorem flatBase_apply (y : Point n) (i j : Fin n) :
    flatBase y i j = if i = j then (1 : ℝ) else 0 := rfl

/-- F4 residue `hgb` — the flat base metric is `C^∞` (it is constant in the point). -/
theorem flatBase_contDiff (a b : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => flatBase y a b) :=
  contDiff_const

/-- F4 residue `hsymmb` — the flat base metric is symmetric. -/
theorem flatBase_symm (y : Point n) (a b : Fin n) :
    flatBase y a b = flatBase y b a := by
  simp only [flatBase]; by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

/-- F4 residue `hgaugeb` — the flat base metric is `δ` at the origin (trivially, everywhere). -/
theorem flatBase_gauge (a b : Fin n) :
    flatBase (0 : Point n) a b = if a = b then (1 : ℝ) else 0 := rfl

/-- F4 residue `hinvb` — the flat base metric is its own inverse (`∑_σ δ_{aσ} δ_{σb} = δ_{ab}`). -/
theorem flatBase_inv (y : Point n) (a b : Fin n) :
    (∑ σ, flatBase y a σ * flatBase y σ b) = if a = b then (1 : ℝ) else 0 := by
  simp only [flatBase]
  have hfun : (fun σ => (if a = σ then (1 : ℝ) else 0) * (if σ = b then 1 else 0))
      = (fun σ => if σ = a then (if a = b then (1 : ℝ) else 0) else 0) := by
    funext σ; by_cases h : a = σ
    · subst h; simp
    · rw [if_neg h, zero_mul, if_neg (fun h' => h h'.symm)]
  rw [hfun, Finset.sum_ite_eq' Finset.univ a (fun _ => if a = b then (1 : ℝ) else 0)]
  simp

/-- F4 residue `hCb` — the Christoffel symbols of the flat base metric are `C^∞`
    (via `christoffel_contDiff`, since both `flatBase` and its inverse `flatBase` are `C^∞`). -/
theorem flatBase_christoffel_contDiff (a b c : Fin n) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (flatBase (n := n)) flatBase a b c y) :=
  christoffel_contDiff flatBase flatBase flatBase_contDiff flatBase_contDiff a b c

/-! ###############################################################################
    ### `a1_R6_from_data_v4e` — `v4d` at the flat base metric: group (D′) → `hgPull` only.
    ############################################################################### -/

set_option maxHeartbeats 1600000 in
/-- **★★★★★ J4-747 (OPTION B) — `a1_R6_from_data_v4e`.**  `HgateOpenFlowballAbsorb.a1_R6_from_data_v4d`
    specialized to the CONCRETE flat base metric `gb := gib := flatBase = δ`.  The five gb-side F4
    residues (`hCb`,`hsymmb`,`hinvb`,`hgb`,`hgaugeb`) are discharged by the banked `flatBase_*` facts;
    the base-metric block of group (D′) collapses to the single defining equation `hgPull`.  Same
    conclusion as `v4d`.  Pure specialization.  NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v4e (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hcarTau : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ k : Fin n,
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t)
    (hgPull : g = expPullbackMetric flatBase flatBase flatBase_christoffel_contDiff 0) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
    (heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) :=
  a1_R6_from_data_v4d hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc hgnd hinvF hframeK hw hgiMeas hchrMeas
    hcarTau hcarField hcarField2 slots
    flatBase flatBase flatBase_christoffel_contDiff hgPull
    flatBase_symm flatBase_inv flatBase_contDiff flatBase_gauge

end QIQTH.FlatBaseAbsorb

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FlatBaseAbsorb
#print axioms flatBase_christoffel_contDiff
#print axioms flatBase_inv
#print axioms a1_R6_from_data_v4e
end AxiomChecks
