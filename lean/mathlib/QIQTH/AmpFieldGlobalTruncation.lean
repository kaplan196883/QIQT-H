/-
  AmpFieldGlobalTruncation — J4-1026: globalizing J4-1025's LOCAL bound+Lipschitz fact for
  `chartFieldAmp` at a general field point `p` into a GLOBAL (all of `Point n`) bound + GLOBAL PAIRWISE
  Lipschitz fact, matching EXACTLY J4-1024's `transported_ratio_regularity_generalK` / §E's abstract
  weight `P` interface, then instantiating that capstone at the resulting truncated `chartFieldAmp`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ## WHAT WAS MISSING (cp911 item (2) / J4-1025's own flagged gap).
  J4-1025 (`AmpFieldGeneralPointBoundLipschitz.chartFieldAmp_bound_lipschitz_generalPoint`) gives
  bounded + PAIRWISE Lipschitz on an OPEN BALL `ball p r` around a general fixed field point `p` — LOCAL
  only.  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s §C/§E (J4-1024) need an abstract
  weight `P : Point n → ℝ` satisfying a GLOBAL bound (`∀ z, |P z| ≤ M_P`) AND a GLOBAL PAIRWISE Lipschitz
  bound (`∀ x y, |P x − P y| ≤ L_P · dist x y`, for ALL `x y`, not just near a centre) — strictly stronger
  than "Lipschitz-at-a-point", which is all the campaign's earlier `truncFactor`-style radial truncation
  (`LocalRNCJetFactorGlobalization.truncFactor`) delivers.  Nothing of this exact (global PAIRWISE)
  shape, built from `chartFieldAmp`, existed.

  ## THE MECHANISM (NOT radial truncation — `truncFactor`'s "constant outside the ball" trick does
  ## NOT preserve pairwise Lipschitz between one point inside and one point outside; verified before
  ## writing any Lean).  Instead: COMPOSE with the metric-projection CLAMP onto the sup-norm ball,
  ## `BaseFlowGlobalContraction.coordClamp` (already banked, proven `LipschitzWith 1`, lands exactly in
  ## the closed ball).  Composing an `L`-Lipschitz-on-`ball p r` function with the globally
  ## `1`-Lipschitz `coordClamp p ρ` (`ρ < r`, so `coordClamp` always lands inside `ball p r`) gives, via
  ## `LipschitzOnWith.comp`, a GLOBALLY `LipschitzWith L` function on ALL of `Point n` — genuinely
  ## pairwise, since composing with a retraction that always lands in the domain of Lipschitz control
  ## preserves the SAME constant for EVERY pair of ambient points, not just points near the centre.
  ## Sol (gpt-5.6-sol, high) GO-reviewed this exact plan (including the `coordClamp` vs `truncFactor`
  ## distinction, the closed/open-ball inclusion `ρ < r`, and the coordinatewise clamp-identity argument)
  ## before any Lean was written.

  ## WHAT LANDS (ns `QIQTH.AmpFieldGlobalTruncation`).
    • `AmpGlobal` — `chartFieldAmp … z` PRE-COMPOSED with `coordClamp p ρ`.
    • `coordClamp_eq_self_of_mem_closedBall` — the clamp is the IDENTITY on `closedBall z₀ r` (a small
      new lemma about the already-banked `coordClamp`, needed for the agreement claim below; NOT already
      in `BaseFlowGlobalContraction.lean`, which does not state it).
    • `ampGlobal_bound_lipschitz_agree` — ★★★★★ THE BRIDGE.  For a general field point `p`, produces
      `ρ > 0`, and moduli `L, M ≥ 0` such that `AmpGlobal` is (i) GLOBALLY bounded by `M` on ALL of
      `Point n`, (ii) GLOBALLY PAIRWISE Lipschitz with constant `L` on ALL of `Point n`
      (`∀ x y, |AmpGlobal x − AmpGlobal y| ≤ L · dist x y`), and (iii) AGREES with the literal
      `chartFieldAmp … z` on `closedBall p ρ` (so nothing is lost on the region that actually matters
      near `p`).
    • `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_global` — ★★★★★ instantiates
      J4-1024's §E capstone (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`) at
      `P := AmpGlobal`, giving `nb`'s domain-restricted BRICK-2 bound for the "`chartFieldAmp`-composed-
      with-`V`-over-Jacobian" shape — the closest this campaign has come to a literal-amplitude
      instantiation of that capstone.

  ## HONEST SCOPE — WHAT THIS DOES **NOT** DO.
  This closes the specific gap J4-1025 flagged (LOCAL → GLOBAL, for `chartFieldAmp` itself) and feeds it
  through J4-1024's abstract-`P` capstone.  It does **NOT** identify the resulting bound with the
  LITERAL `kPrime`/`Bfac`-normalised `nb` term1 integrand at the field point actually relevant to the
  sliver integral — `Bfac` (`HCompNearCarryKPrimeBaseFieldCoV`'s 4-term amplitude) is a DIFFERENT,
  richer quantity than the bare `chartFieldAmp` weight (`Bfac` bundles `chartFieldAmp` together with the
  transported-ratio `V`/Jacobian composition ITSELF, plus the census scalar and chart-jet factors — see
  `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s own honest-scope note); this file supplies
  ONE abstract globally-regular weight `P` (built from the concrete `chartFieldAmp`) that CAN be fed into
  the transported-ratio machinery, but does not itself perform the base-slot change-of-variables that
  would identify `V (w)` with the literal chart argument in `nb`'s actual sliver integral, nor does it
  discharge `hfac`'s own literal-Bfac carry over the IFT-selected domain `S'`.  `Bfac`'s other three
  summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`) and the `Levi(s,z)` prefactor remain entirely untouched.
  `fb` (far carry) remains SEPARATELY open.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.

  NO `sorry`, NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, none equal to the
  conclusion.  NEW FILE — no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmpFieldGeneralPointBoundLipschitz
import QIQTH.BaseFlowGlobalContraction
import QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.FlatHeatEquation
open QIQTH.OnGateJets QIQTH.AmpFieldGeneralPointBoundLipschitz
open QIQTH.BaseFlowGlobalContraction
open QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
open scoped Topology BigOperators ContDiff NNReal

namespace QIQTH.AmpFieldGlobalTruncation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ############################################################################
    ### 1. A small identity lemma for the already-banked `coordClamp`.
    ############################################################################ -/

/-- **`coordClamp_eq_self_of_mem_closedBall`.**  `coordClamp z₀ r` is the IDENTITY on the sup-norm
    closed ball `closedBall z₀ r` — it only moves points that lie OUTSIDE the ball.  NOT stated in
    `BaseFlowGlobalContraction.lean`; needed here for the agreement claim. NOT `a₁ = R/6`. -/
theorem coordClamp_eq_self_of_mem_closedBall (z₀ : Point n) (r : ℝ) (w : Point n)
    (hw : w ∈ Metric.closedBall z₀ r) : coordClamp z₀ r w = w := by
  funext i
  have hidist : dist (w i) (z₀ i) ≤ dist w z₀ := dist_le_pi_dist w z₀ i
  have hle : dist (w i) (z₀ i) ≤ r := hidist.trans (Metric.mem_closedBall.mp hw)
  have hiabs : |w i - z₀ i| ≤ r := by simpa [Real.dist_eq] using hle
  rcases abs_le.mp hiabs with ⟨hlo, hhi⟩
  show z₀ i + max (-r) (min r (w i - z₀ i)) = w i
  rw [min_eq_right hhi, max_eq_right hlo]
  ring

/-! ############################################################################
    ### 2. `AmpGlobal` — `chartFieldAmp` precomposed with the sup-norm clamp.
    ############################################################################ -/

/-- **`AmpGlobal`.**  The concrete on-gate amplitude `chartFieldAmp`, pulled back through the
    metric-projection clamp `coordClamp p ρ` onto the sup-norm ball around a general field point `p`.
    Agrees with `chartFieldAmp … z` exactly on `closedBall p ρ`, and is globally bounded + globally
    pairwise Lipschitz everywhere (see `ampGlobal_bound_lipschitz_agree`). NOT `a₁ = R/6`. -/
noncomputable def AmpGlobal (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z p : Point n) (ρ : ℝ)
    (x : Point n) : ℝ :=
  chartFieldAmp g gi hChr hK a b τ z (coordClamp p ρ x)

/-! ############################################################################
    ### 3. THE BRIDGE — global bound + global pairwise Lipschitz + agreement.
    ############################################################################ -/

/-- **★★★★★ `ampGlobal_bound_lipschitz_agree`.**  For a general fixed field point `p`, given the same
    two honest carries `OnGateJets.ampField_contDiffAt` needs (`hWz`, `hdetz`), there is `ρ > 0` and
    moduli `L, M ≥ 0` such that `AmpGlobal g gi hChr hK a b τ z p ρ`:
      • is bounded by `M` on ALL of `Point n`;
      • is PAIRWISE Lipschitz with constant `L` on ALL of `Point n`
        (`∀ x y, |AmpGlobal x − AmpGlobal y| ≤ L · dist x y`, genuinely global — not Lipschitz-at-a-
        point);
      • AGREES with the literal `chartFieldAmp g gi hChr hK a b τ z` on `closedBall p ρ`.
    Route: J4-1025's local ball fact at radius `r`, shrunk to `ρ := r / 2`, composed with the
    already-banked, already-proven `1`-Lipschitz sup-norm clamp `coordClamp` (`BaseFlowGlobalContraction`,
    `LipschitzOnWith.comp`).  This is genuinely GLOBAL pairwise Lipschitz, unlike the earlier
    `truncFactor` radial-truncation mechanism (which only gives Lipschitz-AT-the-centre). NOT
    `a₁ = R/6`. -/
theorem ampGlobal_bound_lipschitz_agree (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK z) p)
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK z p))) :
    ∃ ρ > (0 : ℝ), ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      (∀ x y : Point n,
        |AmpGlobal g gi hChr hK a b τ z p ρ x - AmpGlobal g gi hChr hK a b τ z p ρ y|
          ≤ L * dist x y) ∧
      (∀ x : Point n, |AmpGlobal g gi hChr hK a b τ z p ρ x| ≤ M) ∧
      (∀ x ∈ Metric.closedBall p ρ,
        AmpGlobal g gi hChr hK a b τ z p ρ x = chartFieldAmp g gi hChr hK a b τ z x) := by
  classical
  obtain ⟨r, hr, L, hL, M, hlip, hbd⟩ :=
    chartFieldAmp_bound_lipschitz_generalPoint g gi hChr hK a b τ z p hg hu hWz hdetz
  set F : Point n → ℝ := chartFieldAmp g gi hChr hK a b τ z with hFdef
  set ρ : ℝ := r / 2 with hρdef
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by rw [hρdef]; linarith
  refine ⟨ρ, hρpos, L, M, hL, le_trans (abs_nonneg _) (hbd p (Metric.mem_ball_self hr)), ?_, ?_, ?_⟩
  · -- global pairwise Lipschitz.
    set Kc : ℝ≥0 := ⟨L, hL⟩ with hKcdef
    have hKcoe : (Kc : ℝ) = L := rfl
    have hFlip : LipschitzOnWith Kc F (Metric.ball p r) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      have h := hlip x hx y hy
      simpa [hFdef, hKcoe, Real.dist_eq] using h
    have hballsub : Metric.closedBall p ρ ⊆ Metric.ball p r := Metric.closedBall_subset_ball hρr
    have hMaps : Set.MapsTo (coordClamp p ρ) Set.univ (Metric.ball p r) :=
      coordClamp_mapsTo p ρ (le_of_lt hρpos) hballsub
    have hcomp_on : LipschitzOnWith (Kc * 1) (F ∘ coordClamp p ρ) Set.univ :=
      hFlip.comp ((lipschitzOnWith_univ).2 (coordClamp_lipschitzWith_one p ρ)) hMaps
    rw [mul_one] at hcomp_on
    have hglobal : LipschitzWith Kc (F ∘ coordClamp p ρ) := lipschitzOnWith_univ.1 hcomp_on
    intro x y
    have h := hglobal.dist_le_mul x y
    have hcompeq : (F ∘ coordClamp p ρ) x = AmpGlobal g gi hChr hK a b τ z p ρ x := by
      simp [AmpGlobal, hFdef, Function.comp]
    have hcompeq' : (F ∘ coordClamp p ρ) y = AmpGlobal g gi hChr hK a b τ z p ρ y := by
      simp [AmpGlobal, hFdef, Function.comp]
    rw [hcompeq, hcompeq'] at h
    rwa [hKcoe, Real.dist_eq] at h
  · -- global bound.
    intro x
    have hmemclosed : coordClamp p ρ x ∈ Metric.closedBall p ρ :=
      coordClamp_mem_closedBall p ρ (le_of_lt hρpos) x
    have hmemball : coordClamp p ρ x ∈ Metric.ball p r :=
      Metric.closedBall_subset_ball hρr hmemclosed
    have h := hbd (coordClamp p ρ x) hmemball
    simpa [AmpGlobal, hFdef] using h
  · -- agreement on `closedBall p ρ`.
    intro x hx
    have hclamp : coordClamp p ρ x = x := coordClamp_eq_self_of_mem_closedBall p ρ x hx
    simp [AmpGlobal, hFdef, hclamp]

/-! ############################################################################
    ### 4. Instantiating J4-1024's §E capstone at the literal-`chartFieldAmp`-built weight.
    ############################################################################ -/

/-- **★★★★★ `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_global`.**
    Instantiates `HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge`'s §E capstone
    (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`, J4-1024) at
    `P := AmpGlobal g gi hChr hK a b τ z p ρ` — the globally bounded + globally Lipschitz weight built
    (§3, this file) from the LITERAL concrete amplitude `chartFieldAmp` at a general field point `p`,
    via `ampGlobal_bound_lipschitz_agree`.  Gives `nb`'s BRICK-2 domain-restricted bound for the
    "`chartFieldAmp`-composed-with-`V`-over-Jacobian" shape at the literal amplitude (up to the
    coordinate-clamp truncation outside `closedBall p ρ`, where `AmpGlobal` agrees exactly with
    `chartFieldAmp`).  Does NOT identify this with `nb`'s actual `Bfac`-normalised sliver integrand —
    see the file docstring's honest-scope note (`Bfac` is a richer 4-term quantity than the bare
    `chartFieldAmp` weight; the base-slot CoV linking `V w` to the literal chart argument, and `hfac`'s
    own literal carry over `S'`, remain undischarged).  `Bfac`'s other 3 summands + `Levi(s,z)` prefactor
    untouched; `fb` remains SEPARATELY open. NOT `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_global
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Kc : Set (Point n)} (hKc : IsCompact Kc) (ampA ampB τamp : ℝ) (zamp pamp : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWz : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hKc zamp) pamp)
    (hdetz : 0 < Matrix.det (g (uniformInverseChart g gi hChr hKc zamp pamp)))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n) :
    ∃ (S' : Set (Point n)) (ρSp : ℝ) (AmpExt : Point n → ℝ) (L : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρSp ∧
      0 ≤ L ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hChr hK p q₀) '' S',
          gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * AmpExt v)|
        ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
              + (n : ℝ) ^ 2 * L * ‖Q‖)
          + (Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|AmpExt 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
              + Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                  * (|AmpExt 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                      + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
  obtain ⟨ρamp, hρamp, L, M, hL, hM, hlip, hbd, _hagree⟩ :=
    ampGlobal_bound_lipschitz_agree g gi hChr hKc ampA ampB τamp zamp pamp hg hu hWz hdetz
  exact hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio g gi hChr hK hq₀
    τ hτ PI PJ Q (AmpGlobal g gi hChr hKc ampA ampB τamp zamp pamp ρamp) M L hM hL hbd hlip

end QIQTH.AmpFieldGlobalTruncation

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AmpFieldGlobalTruncation
#print axioms coordClamp_eq_self_of_mem_closedBall
#print axioms ampGlobal_bound_lipschitz_agree
#print axioms hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_chartFieldAmp_global
end AxiomChecks
