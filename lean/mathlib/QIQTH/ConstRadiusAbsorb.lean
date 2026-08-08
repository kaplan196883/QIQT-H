/-
  ConstRadiusAbsorb — J4-412: Sol #18 closing sequence 2/4, THE constRadius ABSORPTION.

  We DISCHARGE the three honest "constant-radius package" carries of the capstone
  `HGaussAbsorb.a1_R6_from_data_v2` — `hpkgBound`/`hmemS0`/`hopenS0` — by CONSUMING the banked
  existential package `ConstRadiusGateExport.constRadius_package_and_S1` INSIDE the proof (Route (ii),
  the ∃-consuming capstone), and restate the capstone as `a1_R6_from_data_v3`.

  ⚠ HONESTY FIREWALL.  This is **NOT** an unconditional `a₁ = R/6`.  `a1_R6_from_data_v3` is STILL the
  maximally-unconditional **CONDITIONAL** a₁ two-jet.  Absorbing the constant-radius package removes
  EXACTLY the three carries `hpkgBound`/`hmemS0`/`hopenS0`; it closes nothing deeper.  What remains
  CONDITIONAL is UNCHANGED from `a1_R6_from_data_v2`:
    (a) the `A1R6GateSlots` censuses (Duhamel/W1-free/L2 slot) — now supplied ∀-over-gates;
    (b) the remaining `ConstGateAssemblyData` carries (`hgate`, the v4 measurability) — ∀-over-gates;
    (c) the base-metric identification `hgPull` and the F4 pullback residues (group (D′));
    (d) the convergence-trio content inside the Duhamel census — NEVER claimed closed.
  ⚠ NOT `a₁ = R/6`.

  ── THE ROUTE VERDICT (Route (ii), not Route (i)).
  Route (i) (a parametric re-run of `constRadius_package_and_S1` taking `(a,b,c)` explicitly with
  admissibility hypotheses) does NOT discharge the carries.  The radii `(a,b,c)` are genuinely
  load-bearing: `a,b` are the cutoff-annulus radii chosen INSIDE
  `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` so the parametrix RESIDUAL is width-2
  Gaussian-bounded, and `c = (b+ρc)/2` is derived from `b` and the geometric reach
  `ρc = min (min rN δ₀) r₁`.  The width-2 bound holds ONLY at those chosen radii; a version keeping
  `(a,b,c)` free would have to re-expose the residual bound as a hypothesis — i.e. re-expose
  `hpkgBound` itself.  So Route (i) merely re-parametrizes; it cannot DISCHARGE.  To discharge the
  three carries one MUST accept the ∃-chosen radii ⟹ Route (ii).

  ── THE HONESTY COST of Route (ii).
  Consuming the ∃ forces two shape changes on the public signature:
    • the CONCLUSION becomes `∃ a b c, 0 < a ∧ a < b ∧ b < c ∧ (the two-jet at that gate)` — the a₁
      two-jet holds AT SOME constant-radius gate (the geometry-produced one), not at a caller-chosen one;
    • the remaining `(a,b,c)`-dependent carriers (`hgate`, the v4 measurability, `slots`) become
      ∀-QUANTIFIED over admissible gate triples `∀ a b c, 0 < a → a < b → b < c → …`.  This is a
      STRONGER hypothesis to supply than a per-gate one (the caller must supply it FOR WHATEVER gate the
      geometry produces) — noted honestly.
  In exchange the public signature quantifies NO gate radii and carries NO
  `hpkgBound`/`hmemS0`/`hopenS0`; the constant-radius package (bound + origin membership + origin
  openness) is discharged internally from geometry-only inputs.
-/
import Mathlib
import QIQTH.HGaussAbsorb
import QIQTH.ConstRadiusGateExport

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
open QIQTH.A1R6FromData QIQTH.HGaussAbsorb QIQTH.ConstRadiusGateExport
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.ConstRadiusAbsorb

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (J4-412) `a1_R6_from_data_v3` — the capstone with the constant-radius package ABSORBED.
    ############################################################################### -/

/-- **★★★★★ J4-412 — `a1_R6_from_data_v3`.**  The public capstone `HGaussAbsorb.a1_R6_from_data_v2`
    RESTATED WITHOUT its three constant-radius package carries `hpkgBound`/`hmemS0`/`hopenS0`.  They are
    discharged INTERNALLY by consuming `ConstRadiusGateExport.constRadius_package_and_S1`'s existential
    (Route (ii), the ∃-consuming capstone), which — from geometry-only inputs (`hgnd`, `hinvF`,
    `hframeK`, `hw`, `hu`, …) — produces gate radii `(a,b,C,c)` together with the ALL-`t` width-2
    Gaussian bound, the origin gate membership, and the origin gate-openness at the LITERAL
    constant-radius gate `constGate g gi hChr hK c`.

    Because the gate radii are now internal geometric data, the CONCLUSION is existentially quantified
    over `(a,b,c)`, and the remaining `(a,b,c)`-dependent carriers (`hgate`, the v4 measurability,
    `slots`) are supplied ∀-QUANTIFIED over admissible gate triples — a STRONGER (∀-over-gates) supply
    than a per-gate one; noted honestly.

    ⚠ THE HONEST SUMMARY.  This is the maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT an
    unconditional `a₁ = R/6`.  Absorbing the constant-radius package removes exactly the three carries;
    it closes nothing deeper.  What remains CONDITIONAL is UNCHANGED from `a1_R6_from_data_v2`:
    the `A1R6GateSlots` censuses, the remaining `ConstGateAssemblyData` carries, the base-metric
    identification `hgPull` (group (D′)), and the convergence-trio content inside the Duhamel census.
    ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v3 (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders (unchanged from v2):
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
    -- ── (A′) the constant-radius package's EXTRA geometry-only inputs (new; all honest / satisfiable):
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── (B) the remaining `(a,b,c)`-dependent carriers, ∀-QUANTIFIED over admissible gate triples:
    -- the affine on-gate width-4/3 quadratic carry `hgate` (with its `P₀`,`P₁` gate-local):
    (hgate : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        (∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
          p ∈ closure (constGate g gi hChr hK c q) →
          |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
            ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                    * gaussDdim (4 / 3 * τ) (p - q))))
    -- the v4 measurability carriers, ∀-over-gates:
    (hKSmeas : ∀ c : ℝ, MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
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
    -- the ONE semantic slot package (Duhamel + W1-free + L2 censuses bundled), ∀-over-gates:
    (slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t)
    -- ── (D′) group (D) ABSORBED (unchanged from v2): base-metric exp-pullback + base geometry premises.
    (gb gib : Point n → Fin n → Fin n → ℝ)
    (hCb : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel gb gib a b c y))
    (hgPull : g = expPullbackMetric gb gib hCb 0)
    (hsymmb : ∀ y a b, gb y a b = gb y b a)
    (hinvb : ∀ y a b, (∑ σ, gb y a σ * gib y σ b) = if a = b then 1 else 0)
    (hgb : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gb y a b))
    (hgaugeb : ∀ a b, gb 0 a b = if a = b then 1 else 0) :
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
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- ── consume the banked existential: obtain the gate radii + the three package carries from geometry.
  obtain ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ₀pos, hbound, hmem0, hopen0, hS1⟩ :=
    constRadius_package_and_S1 (n := n) hn g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchrMeas
  -- ── extract the ∀-over-gates carriers AT the obtained (admissible) gate triple.
  obtain ⟨P₀, P₁, hP₀, hP₁, hgate'⟩ := hgate a b c ha hab hbc
  -- ── assemble the ∃-quantified conclusion and re-export the CONDITIONAL two-jet from `v2`.
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  exact a1_R6_from_data_v2 hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hC0
    P₀ P₁ hP₀ hP₁ hgate'
    (hKSmeas c) (hcarTau a b c ha hab hbc) (hcarField a b c ha hab hbc) (hcarField2 a b c ha hab hbc)
    hgiMeas hchrMeas
    hbound hmem0 hopen0
    (slots a b c ha hab hbc)
    gb gib hCb hgPull hsymmb hinvb hgb hgaugeb

end QIQTH.ConstRadiusAbsorb

/-! ###############################################################################
    ### THE AUDIT — `#print axioms` for the capstone (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.ConstRadiusAbsorb
#print axioms a1_R6_from_data_v3
end AxiomChecks
