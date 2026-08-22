/-
  HCompNearCarryKPrimeGateRestrictedCoVNbhd — J4-1031: the LOCALIZED (`∀ y ∈ S z`, not `∀ y : Point n`)
  jet-bundle port of `HCompNearCarryKPrimeGateRestrictedCoV` (J4-1029) — discharging the interface-over-
  strength mismatch cp985 diagnosed as the deeper problem behind residual (r2).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  hypothesis-WEAKENING port: every conclusion is IDENTICAL in shape to J4-1029's, only the antecedent
  jet-bundle hypotheses are relaxed from a GLOBAL (`∀ y : Point n`) quantifier to a LOCAL (`∀ y ∈ S z`,
  the actual open gate) one, for the ONE jet family the underlying calculus genuinely uses at points other
  than the fixed field point `x`. No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited (NEW FILE).  Does NOT discharge
  residual (r2) (the jet bundle itself is still an unproven antecedent) — it PROVES THE ANTECEDENT CAN BE
  WEAKENED, materially shrinking what a future r2 discharge must supply.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FINDING (cp985 diagnostic, this dispatch's audit).  Every downstream consumer in the `nb` term1/r2
  chain (`ChartJetHessianMixed.witnessMixed_gate_eq`, `HCompNearCarryChartSurfaceWired.
  kPrime_apply_single_on_gate_eq_mixedNormalForm`, `HCompNearCarryKPrimeBaseFieldCoV.
  kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`, `HCompNearCarryKPrimeGateRestrictedCoV.
  kPrime_baseField_CoV_of_jetBundle_gateRestricted`) states its two first-jet hypotheses `hJetVi`/`hJetVj`
  as `∀ y : Point n` GLOBAL, even though `pd` (`Curvature.pd f i x := deriv (fun t => f (update x i t))
  (x i)`) is a GERM-local operator: `JacobianRadial.pd_congr_of_eventuallyEq` (ALREADY BANKED, std-3)
  proves `f =ᶠ[𝓝 x] h → pd f i x = pd h i x`.  Tracing `ChartJetHessianMixed.gaussComp_pd_pd_mixed`'s
  proof term literally: of its two `∀ x k`-typed jet hypotheses (`hVi`, `hVj`), `hVj` (the INNER
  differentiation direction, used to build the S1a normal form `hinner` as a genuine function EQUALITY
  `∀ y`, via `funext`) is the ONLY one ever applied at a point `≠ x₀`; `hVi` (the OUTER direction) and `hQ`
  (the mixed second jet) are applied ONLY at `x₀` throughout — despite `hVi`'s stronger `∀ x k` TYPE.  This
  is a genuine interface-over-strength gap, not a math gap: the SAME proof, with `hinner`'s `funext`
  (global function equality) replaced by an `EventuallyEq` built via `filter_upwards` on an open set and
  closed through `pd_congr_of_eventuallyEq`, proves the IDENTICAL conclusion from a hypothesis on `hVj`
  weakened to `∀ x ∈ U`, `hVi` weakened all the way to a single point.

  ── THIS WAS ALREADY DONE ONCE, for a DIFFERENT (older, `GatedRepSFix`-era) consumer chain: J4-237
  (`Field2NbhdReshape.lean`) built `gaussComp_pd_pd_mixed_nbhd`, `gaussComp_amp_pd_pd_mixed_nbhd`, and
  `witnessMixed_gate_eq_nbhd` — the EXACT localized port of `ChartJetHessianMixed`'s three mixed-normal-
  form lemmas, with the inner jet family weakened to `∀ y ∈ S z` (the natural open gate) — and used it to
  discharge the OLD `GatedRepSFix`/measurability track.  It was consulted via gpt-5.6-sol high BEFORE
  writing any Lean below (question: is the localization sound / any Mathlib pitfall / worth building /
  any structural blocker — answer: sound, no pitfall, worth building, no blocker).

  ── WHAT THIS FILE DOES.  The NEWER `nb`/`HCompNearCarry*` consumer chain (J4-882/1010/1029, driving
  `kPrime`'s literal jet bundle for `HCompNearCarryKPrimeGateRestrictedCoV`) was built calling
  `ChartJetHessianMixed.witnessMixed_gate_eq` DIRECTLY (the GLOBAL form), never reusing J4-237's already-
  banked localized port.  This file re-derives the SAME three-step composition
  (`kPrime_apply_single_eq_mixedPd` → mixed normal form → base-slot CoV) using
  `Field2NbhdReshape.witnessMixed_gate_eq_nbhd` in place of `ChartJetHessianMixed.witnessMixed_gate_eq`,
  producing LOCALIZED analogues of all three J4-882/1010/1029 theorems:
    • `kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd` — the J4-882 wiring, `hJetVi` (direction `j`,
      the outer-in-composition role) weakened to a SINGLE POINT `x` (dropped `∀ y` entirely — the campaign's
      own proof term never used it elsewhere), `hJetVj` (direction `i`, inner-in-composition) weakened to
      `∀ y ∈ S z` (the ACTUAL geometric open gate, replacing `∀ y : Point n`).
    • `kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd` — the BRICK-1 analogue (pure `ring`
      identity port, same weakened hypotheses).
    • `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd` — the FULL J4-1029 wrapper, with the on-gate
      jet bundle now `∀ z ∈ K, ∀ y ∈ S z, ∀ k, HasDerivAt …` (direction `i`) instead of `∀ z ∈ K, ∀ y :
      Point n, ∀ k`, and the direction-`j` jet needed only `∀ z ∈ K, ∀ k`, AT `x`.  Identical conclusion
      shape to J4-1029's theorem — the CoV identity, `S'' ⊆ K` proved, `hfac` discharged pointwise.

  ## WHY THIS MATTERS FOR r2.  `GeneralBaseJetsMixed.lean` (J4-1030)'s natural output shape is
  `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt …` — LOCAL, not global.  `∀ᶠ x in 𝓝 0` trivially implies `∀ y ∈ U` for
  SOME open `U ∋ 0` (`Filter.eventually_iff_exists_mem`/`eventually_nhds_iff`), which is the SAME shape
  this file's `hJetVj : ∀ z ∈ K, ∀ y ∈ S z, ∀ k, …` wants — MODULO the remaining geometric gap that `S z`
  (the flow-image gate) and the `𝓝 0`-neighbourhood J4-1030 supplies are not literally the same set (J4-
  1030 is honest that it does not establish chart-coverage across `K`).  This file does NOT close that
  remaining gap (still open, still the honest r2 residue) — it PROVES the interface no longer demands
  MORE than the neighbourhood shape J4-1030-style bricks can plausibly supply, correcting the earlier
  "every consumer wants the global fact" diagnosis to "every consumer's TYPE says global, but the MATH
  wants only local — and the local port composes cleanly with the existing machinery."

  `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryKPrimeGateRestrictedCoV
import QIQTH.Field2NbhdReshape

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FderivBulkConcrete QIQTH.FlatHeatEquation QIQTH.InnerKernelJointMeas
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Step 1 — the LOCALIZED J4-882 wiring (`hJetVj` only `∀ y ∈ S z`, `hJetVi` only at `x`).
    ############################################################################### -/

/-- **★★★ `kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd`.**  Nbhd port of
    `HCompNearCarryChartSurfaceWired.kPrime_apply_single_on_gate_eq_mixedNormalForm`: the CONCRETE
    `kPrime` component wired through the MIXED Leibniz–Gaussian normal form, on the gate, with `hJetVi`
    (direction `j`) needed only AT `x` and `hJetVj` (direction `i`) needed only `∀ y ∈ S z` (the actual
    open gate, NOT `∀ y : Point n`).  Route: `KPrimeMixedPdBridge.kPrime_apply_single_eq_mixedPd`
    composed with `Field2NbhdReshape.witnessMixed_gate_eq_nbhd` (in place of `ChartJetHessianMixed.
    witnessMixed_gate_eq`).  IDENTICAL conclusion shape to the global version.  NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) (x z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (hx : x ∈ S z) (hτ : 0 < t - s)
    (hd : DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k) (PI x k) (x j))
    (hJetVj : ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ y k) (y i))
    (hJetQ : ∀ k, HasDerivAt
      (fun σ : ℝ => PJ (Function.update x j σ) k) (Q k) (x j))
    (hAmpj1 : ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
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
      QIQTH.Field2NbhdReshape.witnessMixed_gate_eq_nbhd
        g gi hC hK S a b j i (t - s) hτ z hz hSopen x hx PI PJ Q
        hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]

/-! ###############################################################################
    ### Step 2 — the LOCALIZED BRICK-1 analogue.
    ############################################################################### -/

/-- **`kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd`.**  Nbhd port of
    `HCompNearCarryKPrimeBaseFieldCoV.kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp` (BRICK 1):
    the same pure `ring`-identity repackaging of `kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd`
    factoring out `gaussDdim (t - s) (uniformInverseChart g gi hC hK z x)`.  Same weakened hypotheses.
    NOT `a₁ = R/6`. -/
theorem kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) (x z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (hx : x ∈ S z) (hτ : 0 < t - s)
    (hd : DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (PI PJ : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hJetVi : ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k) (PI x k) (x j))
    (hJetVj : ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ y k) (y i))
    (hJetQ : ∀ k, HasDerivAt
      (fun σ : ℝ => PJ (Function.update x j σ) k) (Q k) (x j))
    (hAmpj1 : ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
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
  rw [kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd
        g gi hC hK S a b i j t s x z hz hSopen hx hτ hd PI PJ Q
        hJetVi hJetVj hJetQ hAmpj1 hAmpi1 hAmp2]
  ring

/-! ###############################################################################
    ### Step 3 — the FULL LOCALIZED J4-1029 wrapper.
    ############################################################################### -/

/-- **★★★★ `kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd`.**  Nbhd port of
    `HCompNearCarryKPrimeGateRestrictedCoV.kPrime_baseField_CoV_of_jetBundle_gateRestricted`: same
    genuinely gate-restricted CoV domain `S'' := S' ∩ interior K ⊆ K` and the same literal `kPrime`
    change-of-variables identity, `hfac` discharged pointwise via
    `kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd` — but the jet bundle is now
    `hJetVi : ∀ z ∈ K, ∀ k, … AT x` (direction `j`, dropped `∀ y` entirely — never used elsewhere in the
    proof) and `hJetVj : ∀ z ∈ K, ∀ y ∈ S z, ∀ k, …` (direction `i`, weakened from `∀ y : Point n` to the
    ACTUAL open gate `S z`).  Residual r2 (supplying this weakened bundle) remains OPEN, but strictly
    SMALLER than the global-quantifier version's r2 — see file firewall.  NOT `a₁ = R/6`. -/
theorem kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i j : Fin n) (t s : ℝ) {x : Point n} (hxint : x ∈ interior K)
    (PI PJ : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z ∈ K, IsOpen (S z)) (hxmem : ∀ z ∈ K, x ∈ S z) (hτ : 0 < t - s)
    (hd : ∀ z ∈ K, DifferentiableAt ℝ
        (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (hJetVi : ∀ z ∈ K, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update x j σ) k) (PI z x k) (x j))
    (hJetVj : ∀ z ∈ K, ∀ y ∈ S z, ∀ k, HasDerivAt
      (fun σ : ℝ => uniformInverseChart g gi hC hK z (Function.update y i σ) k) (PJ z y k) (y i))
    (hJetQ : ∀ z ∈ K, ∀ k, HasDerivAt
      (fun σ : ℝ => PJ z (Function.update x j σ) k) (Q z k) (x j))
    (hAmpj1 : ∀ z ∈ K, ∀ y ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i y)
    (hAmpi1 : ∀ z ∈ K, PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) j x)
    (hAmp2 : ∀ z ∈ K, PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) :
    ∃ (S'' : Set (Point n)) (V : Point n → Point n),
      IsOpen S'' ∧ x ∈ S'' ∧ S'' ⊆ K ∧
      (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
        = ∫ w in (fun p => uniformInverseChart g gi hC hK p x) '' S'',
            gaussDdim (t - s) w
              * ((fun z =>
                    leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
                      * (((∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                              * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                              / (4 * (t - s) ^ 2)
                            - ((∑ k, PI z x k * PJ z x k)
                                + (∑ k, uniformInverseChart g gi hC hK z x k * Q z k))
                              / (2 * (t - s)))
                            * chartFieldAmp g gi hC hK a b (t - s) z x
                          + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                                / (2 * (t - s)))
                              * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
                          + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                                / (2 * (t - s)))
                              * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
                          + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x))
                  (V w)
                  / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p x) (V w)).det|) := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p x with hWdef
  set Bfac : Point n → ℝ := fun z =>
      leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        * (((∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                * (∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                / (4 * (t - s) ^ 2)
              - ((∑ k, PI z x k * PJ z x k)
                  + (∑ k, uniformInverseChart g gi hC hK z x k * Q z k))
                / (2 * (t - s)))
              * chartFieldAmp g gi hC hK a b (t - s) z x
            + (-(∑ k, uniformInverseChart g gi hC hK z x k * PJ z x k)
                  / (2 * (t - s)))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) j x
            + (-(∑ k, uniformInverseChart g gi hC hK z x k * PI z x k)
                  / (2 * (t - s)))
                * pd (chartFieldAmp g gi hC hK a b (t - s) z) i x
            + pd (fun y => pd (chartFieldAmp g gi hC hK a b (t - s) z) i y) j x) with hBfacdef
  -- Step A: the raw M1–M4 data on the IFT set `S'` (Bfac/τ-independent).
  obtain ⟨S', V, hS'open, hxS', hinj, hVeq, hfd, hJpos⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint
  -- Step B: gate-restrict to `S'' := S' ∩ interior K ⊆ K`.
  set S'' : Set (Point n) := S' ∩ interior K with hS''def
  have hS''open : IsOpen S'' := hS'open.inter isOpen_interior
  have hxS'' : x ∈ S'' := ⟨hxS', hxint⟩
  have hS''subK : S'' ⊆ K := fun z hz => interior_subset hz.2
  have hS''subS' : S'' ⊆ S' := Set.inter_subset_left
  -- Step C: restrict M1–M4 from `S'` to `S''`.
  have hinj'' : Set.InjOn W S'' := hinj.mono hS''subS'
  have hVeq'' : ∀ p ∈ S'', V (W p) = p := fun p hp => hVeq p (hS''subS' hp)
  have hfd'' : ∀ z ∈ S'', HasFDerivWithinAt W (fderiv ℝ W z) S'' z :=
    fun z hz => (hfd z (hS''subS' hz)).mono hS''subS'
  have hJpos'' : ∀ z ∈ S'', 0 < |(fderiv ℝ W z).det| := fun z hz => hJpos z (hS''subS' hz)
  have hS''meas : MeasurableSet S'' := hS''open.measurableSet
  -- Step D: invoke the abstract CoV corollary directly on `S''`.
  have hCoV :=
    QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables (t - s) S'' W V
      (fun z => fderiv ℝ W z) (fun z => |(fderiv ℝ W z).det|) Bfac hS''meas hfd'' hinj'' hVeq''
      (fun z _ => rfl) hJpos''
  -- Step E: discharge the factorization pointwise across `S''` via the LOCALIZED BRICK 1.
  have hfac : ∀ z ∈ S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1)
      = gaussDdim (t - s) (W z) * Bfac z := by
    intro z hz
    have hzK : z ∈ K := hS''subK hz
    have := kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd
      g gi hC hK S a b i j t s x z hzK (hSopen z hzK) (hxmem z hzK) hτ (hd z hzK)
      (PI z) (PJ z) (Q z) (hJetVi z hzK) (hJetVj z hzK) (hJetQ z hzK)
      (hAmpj1 z hzK) (hAmpi1 z hzK) (hAmp2 z hzK)
    simpa [hWdef, hBfacdef] using this
  have hcong : (∫ z in S'', (kPrime g gi hC hK S a b i t s x z) (Pi.single j 1))
      = ∫ z in S'', gaussDdim (t - s) (W z) * Bfac z :=
    setIntegral_congr_fun hS''meas hfac
  refine ⟨S'', V, hS''open, hxS'', hS''subK, ?_⟩
  rw [hcong]
  simpa [hWdef, hBfacdef] using hCoV

end QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryKPrimeGateRestrictedCoVNbhd
#print axioms kPrime_apply_single_on_gate_eq_mixedNormalForm_nbhd
#print axioms kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp_nbhd
#print axioms kPrime_baseField_CoV_of_jetBundle_gateRestricted_nbhd
end AxiomChecks
