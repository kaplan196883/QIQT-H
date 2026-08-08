/-
  HGaussAbsorb — J4-411: the closing-sequence brick #1, ABSORB `hGauss` into the capstone.
  From the banked Gauss-lemma arc (J4-341..347), supply the single labelled gauge carry `hGauss`
  (group (D) of `A1R6FromData.a1_R6_from_data`) internally, and restate the capstone WITHOUT its
  group-(D) binder as `a1_R6_from_data_v2`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠⚠⚠ HONESTY FIREWALL — THIS FILE IS **NOT** an unconditional `a₁ = R/6`. ⚠⚠⚠
  `a1_R6_from_data_v2` is STILL the maximally-unconditional **CONDITIONAL** two-jet.  Absorbing
  `hGauss` removes ONE labelled carry (group (D)); it does NOT close any of the deeper conditionality:
  the `A1R6GateSlots` censuses (Duhamel/W1-free/L2), the `ConstGateAssemblyData` carries
  (`hgate`/measurability/`hpkgBound`/`hmemS0`/`hopenS0`), and the convergence-trio content living
  inside the Duhamel census all remain CONDITIONAL.  No `sorry`, no `admit`, no `:= True`, no new axiom
  (`std-3` only).  `a₁ = R/6` stays CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (G1) THE SHAPE MAP — supplier vs consumer verdict (dont-undercredit: grepped first).

  ── CONSUMER shape.  The capstone `A1R6FromData.a1_R6_from_data`'s group-(D) binder — and, upstream,
     `FinalA1Slots.finalA1Slots_from_data` → `A1R6SlotAdapters.htr_adapter` →
     `NCRiemannTwoJet.htr_from_hGauss` / `NCGaussToCyclicT.cyclicT_of_hGauss` — all consume the SAME
     germ, VERBATIM:
        `hGauss : ∀ i, (fun x => ∑ j, M x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)`
     where `M` is the metric the capstone works with (the capstone's abstract `g`).

  ── SUPPLIER shape.  The banked Gauss arc terminates in `GaussInteriorMVT.hGauss_pullback_concrete`
     (= `GaussLemmaFlowData.hGauss_pullback` with the per-point first-variation carry discharged by the
     interior-MVT closure `gauss_interior_identity`), whose conclusion is the germ at `M :=
     expPullbackMetric g gi hC p`:
        `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j) =ᶠ[𝓝 0] (fun x => x i)`.

  ── VERDICT.  The two shapes are the **SAME `=ᶠ` germ** — there is NO germ-vs-labelled *conversion*
     (both are literally the eventual-equality germ; the "germ" IS the "labelled form").  The ONLY
     gap is metric IDENTITY: the supplier proves the germ for a metric that is literally an
     exp-pullback `expPullbackMetric g gi hC p`, whereas the consumer's `g` is abstract.  So the
     bridge is **INSTANTIATION** (`g := expPullbackMetric …`), NOT shape conversion.  When the
     capstone's metric IS the pullback metric, `hGauss_pullback_concrete` supplies its `hGauss` binder
     VERBATIM (this is architecturally intended: the whole a₁ chain — `RNCExpansion.heat_a1_of_gauge_c2`
     — is meant to run at `g̃ = expPullbackMetric`, cf. the RNCExpansion `_c2` header).

  ## (G2) `hGauss_concrete` — the bridge: the consumer-shaped `hGauss` binder for the pullback metric,
     from the base geometry inputs.  A verbatim re-export of `hGauss_pullback_concrete`; its POINT is
     that its conclusion type unifies with the capstone's `hGauss` binder once the capstone metric is
     instantiated at `expPullbackMetric gb gib hCb p`.

  ## (G3) `a1_R6_from_data_v2` — the capstone with group (D) REMOVED.  The maximal honest reduction:
     the abstract capstone metric `g` is tied to a base metric by the single named carry
     `hgPull : g = expPullbackMetric gb gib hCb 0`; `hGauss` is then discharged INTERNALLY via G2 from
     the base geometry premises, and the two-jet is re-exported from `a1_R6_from_data`.  Every OTHER
     binder (about the — now pullback — metric `g`) is carried honestly for the caller to establish
     (the F4 residues of `GaussLemmaFlowData`: the C∞-vs-C⁴ smoothness, `∂g̃(0)=0`, inverse-positivity);
     NONE is the conclusion.  Group (D) is gone; the conclusion is unchanged.  ⚠ STILL CONDITIONAL —
     NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.A1R6FromData
import QIQTH.GaussInteriorMVT

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
open QIQTH.A1R6FromData QIQTH.GaussInteriorMVT
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HGaussAbsorb

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (G2) `hGauss_concrete` — the bridge (consumer-shaped `hGauss` for the pullback metric).
    ############################################################################### -/

/-- **★★ (G2) `hGauss_concrete`.**  THE BRIDGE.  From the base geometry data — the `C∞` Christoffel
    (`hC`), the metric symmetry `hsymm`, the exact inverse relation `hinv`, the `C∞` metric `hg`, and
    the base gauge `g_p = I` (`hgauge`) — this supplies the germ that `A1R6FromData.a1_R6_from_data`'s
    group-(D) `hGauss` binder wants, at the metric `M := expPullbackMetric g gi hC p`:
      `∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j · x^j) =ᶠ[𝓝 0] (fun x => x^i)`.
    This is a VERBATIM re-export of the banked interior-MVT terminus
    `GaussInteriorMVT.hGauss_pullback_concrete` (per the G1 verdict there is NO germ-vs-labelled
    conversion — the shapes are identical; the bridge is the metric instantiation).  ⚠ NOT `a₁ = R/6`. -/
theorem hGauss_concrete
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (p : Point n) (hgauge : ∀ a b, g p a b = if a = b then 1 else 0) :
    ∀ i, (fun x => ∑ j, expPullbackMetric g gi hC p x i j * x j)
      =ᶠ[𝓝 (0 : Point n)] (fun x => x i) :=
  hGauss_pullback_concrete g gi hC hsymm hinv hg p hgauge

/-! ###############################################################################
    ### (G3) `a1_R6_from_data_v2` — the capstone with group (D) absorbed.
    ############################################################################### -/

/-- **★★★★★ (G3) `a1_R6_from_data_v2`.**  The public capstone `A1R6FromData.a1_R6_from_data` RESTATED
    WITHOUT its group-(D) `hGauss` binder.  Group (D) is replaced by the geometric identification of the
    capstone metric with a base-metric exp-pullback — the base metric `(gb, gib)` with its `C∞`
    Christoffel `hCb`, the single named carry `hgPull : g = expPullbackMetric gb gib hCb 0`, and the
    base geometry premises `hsymmb`/`hinvb`/`hgb`/`hgaugeb` — from which `hGauss` is discharged INTERNALLY
    via `hGauss_concrete` (G2).  The conclusion is UNCHANGED: the a₁ two-jet at the literal
    constant-radius gate with the Ricci source `(∑ᵢ ricci g gi i i 0)/6` in the `O(t)` coefficient.

    ⚠ THE HONEST SUMMARY.  This is the maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT an
    unconditional `a₁ = R/6`.  Absorbing `hGauss` removes exactly one labelled carry (group (D)); it
    closes nothing deeper.  What remains CONDITIONAL:
      (a) the `A1R6GateSlots` censuses (Duhamel/W1-free/L2 slot);
      (b) the `ConstGateAssemblyData` carries (`hgate`, the v4 measurability, `hpkgBound`/`hmemS0`/`hopenS0`);
      (c) the base-metric identification `hgPull` and the F4 pullback residues carried on the OTHER binders
          (the C∞-vs-C⁴ smoothness, `∂g̃(0)=0`, inverse-positivity) — all satisfiable, carried honestly;
      (d) the convergence-trio content inside the Duhamel census — NEVER claimed closed.
    ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v2 (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders:
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
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ── (B) the `ConstGateAssemblyData` semantic carries:
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
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
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
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
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    -- ── (C) the ONE semantic slot package (Duhamel + W1-free + L2 censuses bundled):
    (slots : A1R6GateSlots g gi hChr hK c a b t)
    -- ── (D′) group (D) ABSORBED: the base-metric exp-pullback identification + base geometry premises.
    (gb gib : Point n → Fin n → Fin n → ℝ)
    (hCb : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel gb gib a b c y))
    (hgPull : g = expPullbackMetric gb gib hCb 0)
    (hsymmb : ∀ y a b, gb y a b = gb y b a)
    (hinvb : ∀ y a b, (∑ σ, gb y a σ * gib y σ b) = if a = b then 1 else 0)
    (hgb : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gb y a b))
    (hgaugeb : ∀ a b, gb 0 a b = if a = b then 1 else 0) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
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
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- (G3) discharge the group-(D) carry internally: `g` is the base exp-pullback metric, whose Gauss
  -- germ is supplied verbatim by G2 (`hGauss_concrete` = `hGauss_pullback_concrete`).
  have hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i) := by
    rw [hgPull]
    exact hGauss_concrete gb gib hCb hsymmb hinvb hgb 0 hgaugeb
  -- re-export the CONDITIONAL two-jet from the banked capstone with `hGauss` now discharged.
  exact a1_R6_from_data hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    P₀ P₁ hP₀ hP₁ hgate hKSmeas hcarTau hcarField hcarField2 hgiMeas hchrMeas
    hpkgBound hmemS0 hopenS0 slots hGauss

end QIQTH.HGaussAbsorb

/-! ###############################################################################
    ### THE AUDITS — `#print axioms` per public decl (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.HGaussAbsorb
#print axioms hGauss_concrete
#print axioms a1_R6_from_data_v2
end AxiomChecks
