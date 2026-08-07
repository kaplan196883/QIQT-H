/-
  QIQTH / HeatResidualBound — AmplitudeDataOnCollar.lean   (J4-352)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It builds the COLLAR-RESTRICTED
  corrected amplitude bundle (Sol consult #12, bricks 1 + 3) that repairs the exact-vs-approximate
  crux isolated in J4-351 (`HrepGermFactorization`): the center chart-image Gaussian identity
  `hV0 : gaussDdim τ (W z 0) = gaussDdim τ z` is FALSE off-flat, so the exact-shape `hD2Hexpand`
  with UNIFORMLY-bounded amplitudes cannot hold globally.  The fix (Sol #12, option (c)) is to
  RESTRICT the hard fields to a regime predicate `Regime : ℝ → Point n → Prop` and absorb the exact
  ratio `ρ = exp((rz − r_{W0})/(4τ))` into the amplitudes, bounding it by `K = exp(Lc³√τ₀/4)` on
  the collar `‖z‖ ≤ c√τ`.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE DESIGN (Sol #12, verbatim).

  • THE CORRECTED BUNDLE `AmplitudeDerivativeDataOn Regime` mirrors `AmplitudeDerivativeData`
    (J4-126, `AmplitudePackage.lean`: 3 amplitudes + 5 moduli + 5 nonnegs + hD2Hexpand + 3 bounds
    + hFdom + 4 measurabilities + hqLip), but with `hD2Hexpand` AND the three amplitude bounds
    made conditional on the `Regime` premise (a PREDICATE premise, NOT a subtype — Sol).  The
    conclusion of `hD2Hexpand` is the SAME exact z-Gaussian 3-term shape; the ρ-scaling lives in the
    (regime-restricted) amplitudes.  The other fields (`hFdom`, measurabilities, `hqLip`) are
    unchanged.

  • THE RATIO MACHINERY.  `rhoRatio τ z := exp((rncRadialSq z − rncRadialSq (W z 0))/(4τ))`;
    `chartImageGauss_ratio` (J4-351) gives EXACTLY `gaussDdim τ (W z 0) = rhoRatio · gaussDdim τ z`
    (`gauss_ratio_rho`).  On the collar `collarRegime`, the near-isometry error
    `chartW0_rncRadialSq_error` (`|rncRadialSq(W z 0) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`) plus
    `rncRadialSq z ≤ n·‖z‖²` and `‖z‖ ≤ c√τ ≤ c√τ₀` give the K-BOUND
    `rhoRatio ≤ collarK = exp(L·n·c³·√τ₀/4)` (`rhoRatio_le_collarK`).

  • THE TRUE-CHART DISCHARGE (brick 3).  `witnessSecondXDeriv_expand_bridge_rho` is the corrected
    bridge: the concrete witness obeys the z-Gaussian 3-term shape with the ρ-SCALED amplitudes,
    with `hV0` REPLACED by the (unconditional) ratio `hV0ρ : gaussDdim τ (V 0) = ρval·gaussDdim τ z`.
    `hD2HexpandOn_concrete` instantiates it at the TRUE chart (`V = uniformInverseChart`,
    `A = chartAmp`, `ρval = rhoRatio`, `hrep` from `vanVleckGatedWitness_germ_factor`, `hV0ρ` from
    `chartImageGauss_ratio`).  NO product-rule corrections — ρ is x'-free (Sol).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE K-CONSTANT BOOKKEEPING (explicit, per the honesty firewall).
    `collarK L c τ₀ = exp(L·n·c³·√τ₀/4)` — the uniform ratio bound on the collar `‖z‖ ≤ c√τ`,
    `τ ≤ τ₀`.  In the concrete bundle the amplitude moduli become `K·M_j` (`M₀ = collarK · M₀chart`,
    etc.), with `M_jchart` the chart-amplitude sup-bounds (CARRIED — see B3 hypotheses).

  THE CARRIES (enumerated, per the honesty firewall).
    • `hD2HexpandOn_concrete` CARRIES: the chart first/second `i`-jets `hV1`/`hP1`, the amplitude
      jets `hA1`/`hA2`, and the three chart-jet center identities `hVP`/`hPsq`/`hVQ` (satisfiable —
      `residueJets_satisfiable`, J4-350).  It does NOT carry `hV0` (replaced by the ratio) and does
      NOT need the near-isometry (that feeds only the ρ≤K bound).
    • `amplitudeDataOn_concrete` (B3) additionally CARRIES: the near-isometry lower bound `hiso`,
      the chart-amplitude sup-bounds `hM·chart`, the regime-uniform jet supply `hjets`, and the
      unchanged Levi/measurability/Lipschitz feeds `hFdom`/`hmeas…`/`hqLip` (the J4-350 census
      banked feeds), all as explicit hypotheses.

  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HrepGermFactorization

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.AmplitudeDataOnCollar

open QIQTH.HeatResidualBound QIQTH.D2HExpandRecon QIQTH.HrepGermFactorization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    S0 — a local `rncRadialSq ≤ n·‖·‖²` bound (inlined to avoid import coupling).
    ############################################################################### -/

/-- **`rncRadialSq_le_nsq`.**  `rncRadialSq v ≤ n·‖v‖²` — each coordinate obeys `|vₖ| ≤ ‖v‖` in the
    sup norm on `Point n = Fin n → ℝ`.  (Elementary; inlined so this brick does not depend on the
    chart-comparison files.)  NOT `a₁ = R/6`. -/
theorem rncRadialSq_le_nsq (v : Point n) : rncRadialSq v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  rw [rncRadialSq]
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
        have hsq : (v i) ^ 2 = |v i| ^ 2 := (sq_abs (v i)).symm
        rw [hsq]; exact pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (n : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-! ###############################################################################
    S1 — the collar regime predicate + the ratio / K definitions.
    ############################################################################### -/

/-- **`collarRegime`** — the intrinsic (ε-free) √ε collar predicate on `(τ, z)`:
      `0 < τ ∧ τ ≤ τ₀ ∧ z ∈ K ∧ ‖z‖ < r₀ ∧ ‖z‖ ≤ c·√τ`.
    The chart-domain conjuncts `z ∈ K`, `‖z‖ < r₀` are the honest hypotheses the near-isometry
    `chartW0_rncRadialSq_error` demands; `‖z‖ ≤ c·√τ` is the collar proper.  This is the `Regime`
    predicate the corrected bundle's hard fields are conditioned on.  NOT `a₁ = R/6`. -/
def collarRegime {K : Set (Point n)} (r₀ c τ₀ : ℝ) (τ : ℝ) (z : Point n) : Prop :=
  0 < τ ∧ τ ≤ τ₀ ∧ z ∈ K ∧ ‖z‖ < r₀ ∧ ‖z‖ ≤ c * Real.sqrt τ

/-- **`rhoRatio`** — the exact chart-image Gaussian ratio exponent
      `ρ(τ,z) = exp((rncRadialSq z − rncRadialSq (W z 0))/(4τ))`,
    `W = uniformInverseChart g gi hC hK`.  By `chartImageGauss_ratio` (J4-351),
    `gaussDdim τ (W z 0) = ρ · gaussDdim τ z` EXACTLY (`gauss_ratio_rho`).  NOT `a₁ = R/6`. -/
noncomputable def rhoRatio (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (z : Point n) : ℝ :=
  Real.exp ((rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ))

/-- **`collarK`** — the uniform ratio bound on the collar: `K = exp(L·n·c³·√τ₀/4)`.  `L` is the
    near-isometry error constant (`chartW0_rncRadialSq_error`), `c` the collar slope, `τ₀` the time
    cap.  This is the explicit K-constant of the bookkeeping.  NOT `a₁ = R/6`. -/
noncomputable def collarK (L c τ₀ : ℝ) : ℝ :=
  Real.exp (L * (n : ℝ) * c ^ 3 * Real.sqrt τ₀ / 4)

/-- **`collarK_pos`** — the collar K-constant is strictly positive (`exp`).  ⚠ NOT `a₁ = R/6`. -/
theorem collarK_pos (L c τ₀ : ℝ) : 0 < collarK (n := n) L c τ₀ := by
  rw [collarK]; exact Real.exp_pos _

/-! ###############################################################################
    S2 — the ratio identity, positivity, and the collar K-bound (B1 core).
    ############################################################################### -/

/-- **`gauss_ratio_rho`** — re-export of `chartImageGauss_ratio` in the `rhoRatio` notation:
      `gaussDdim τ (W z 0) = rhoRatio τ z · gaussDdim τ z`.  Unconditional (needs only `τ > 0`).
    ⚠ NOT `a₁ = R/6`. -/
theorem gauss_ratio_rho (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      = rhoRatio g gi hC hK τ z * gaussDdim τ z := by
  rw [rhoRatio]
  exact chartImageGauss_ratio g gi hC hK τ hτ z

/-- **`rhoRatio_pos`** — the ratio is strictly positive (`exp` is positive).  ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_pos (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (z : Point n) :
    0 < rhoRatio g gi hC hK τ z := by
  rw [rhoRatio]; exact Real.exp_pos _

/-- **★ B1 — `rhoRatio_le_collarK`.**  On the collar regime, the exact Gaussian ratio is uniformly
    bounded: `rhoRatio τ z ≤ collarK L c τ₀`.  Route (Sol #12): the near-isometry LOWER bound
    `hiso` gives `rncRadialSq z − rncRadialSq (W z 0) ≤ L·‖z‖·rncRadialSq z`; then
    `rncRadialSq z ≤ n·‖z‖²` and `‖z‖ ≤ c√τ` give numerator `≤ L·n·c³·τ·√τ`; dividing by `4τ` and
    `√τ ≤ √τ₀` gives exponent `≤ L·n·c³·√τ₀/4`; `exp` monotone closes.  The near-isometry `hiso` is
    the sole geometric carry (satisfied by `chartW0_rncRadialSq_error` on `z ∈ K`, `‖z‖ < r₀`).
    ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_le_collarK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (L c τ₀ r₀ : ℝ) (hL : 0 ≤ L)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - L * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (τ : ℝ) (z : Point n) (hreg : collarRegime (K := K) r₀ c τ₀ τ z) :
    rhoRatio g gi hC hK τ z ≤ collarK (n := n) L c τ₀ := by
  obtain ⟨hτ, hττ₀, hzK, hzr, hzc⟩ := hreg
  have hlow := hiso z hzK hzr
  have hsqrtτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  -- collar slope is nonnegative
  have hc0 : 0 ≤ c := by
    nlinarith [le_trans (norm_nonneg z) hzc, hsqrtτ]
  -- numerator ≤ L·‖z‖·rncRadialSq z
  have hnum : rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)
      ≤ L * ‖z‖ * rncRadialSq z := by linarith
  -- rncRadialSq z ≤ n·‖z‖²
  have hrz : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
  -- ‖z‖³ ≤ c³·τ·√τ
  have h3a : ‖z‖ ^ 3 ≤ (c * Real.sqrt τ) ^ 3 := pow_le_pow_left₀ (norm_nonneg z) hzc 3
  have h3b : (c * Real.sqrt τ) ^ 3 = c ^ 3 * (τ * Real.sqrt τ) := by
    have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
    have hcube : (c * Real.sqrt τ) ^ 3 = c ^ 3 * (Real.sqrt τ ^ 2 * Real.sqrt τ) := by ring
    rw [hcube, hsq]
  have h3 : ‖z‖ ^ 3 ≤ c ^ 3 * (τ * Real.sqrt τ) := h3b ▸ h3a
  -- assemble numerator bound
  have hLz : 0 ≤ L * ‖z‖ := mul_nonneg hL (norm_nonneg z)
  have hLn : 0 ≤ L * (n : ℝ) := mul_nonneg hL (Nat.cast_nonneg n)
  have hNumFull : rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)
      ≤ L * (n : ℝ) * (c ^ 3 * (τ * Real.sqrt τ)) := by
    calc rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)
          ≤ L * ‖z‖ * rncRadialSq z := hnum
      _ ≤ L * ‖z‖ * ((n : ℝ) * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left hrz hLz
      _ = L * (n : ℝ) * ‖z‖ ^ 3 := by ring
      _ ≤ L * (n : ℝ) * (c ^ 3 * (τ * Real.sqrt τ)) := mul_le_mul_of_nonneg_left h3 hLn
  -- exponent bound
  have hsqrtmono : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  have hcoef : 0 ≤ L * (n : ℝ) * c ^ 3 * τ := by
    apply mul_nonneg (mul_nonneg (mul_nonneg hL (Nat.cast_nonneg n)) (pow_nonneg hc0 3)) hτ.le
  have hexp : (rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ)
      ≤ L * (n : ℝ) * c ^ 3 * Real.sqrt τ₀ / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * τ)]
    calc rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)
          ≤ L * (n : ℝ) * (c ^ 3 * (τ * Real.sqrt τ)) := hNumFull
      _ = L * (n : ℝ) * c ^ 3 * τ * Real.sqrt τ := by ring
      _ ≤ L * (n : ℝ) * c ^ 3 * τ * Real.sqrt τ₀ := mul_le_mul_of_nonneg_left hsqrtmono hcoef
      _ = L * (n : ℝ) * c ^ 3 * Real.sqrt τ₀ / 4 * (4 * τ) := by ring
  rw [rhoRatio, collarK]
  exact Real.exp_le_exp.mpr hexp

/-! ###############################################################################
    S3 — B2: the corrected bridge (ρ-scaled amplitudes, hV0 replaced by the ratio).
    ############################################################################### -/

/-- **★ B2 — `witnessSecondXDeriv_expand_bridge_rho`.**  The corrected D2 bridge.  Exactly
    `witnessSecondXDeriv_expand_bridge` (J4-350) but with `hV0` REPLACED by the exact ratio identity
      `hV0ρ : gaussDdim τ (V 0) = ρval · gaussDdim τ z`,
    yielding the z-Gaussian 3-term shape with ρ-SCALED amplitudes
      `= (z i²−2τ)/(4τ²)·gaussDdim τ z·(ρval·A 0)
         + z i/(2τ)·gaussDdim τ z·(ρval·(−2·∂ᵢA 0))
         + gaussDdim τ z·(ρval·∂ᵢ²A 0)`.
    The `gaussDdim τ (V 0)` factor is UNIFORM across the three Leibniz terms, so the ratio rewrite is
    a single multiplication — NO product-rule corrections (ρval is `x'`-free).  ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_expand_bridge_rho
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (V : Point n → Point n) (A : Point n → ℝ) (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (ρval : ℝ)
    (hrep : (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
              =ᶠ[nhds (0 : Point n)] (fun x' => gaussDdim τ (V x') * A x'))
    (hV1 : ∀ x k, HasDerivAt (fun s : ℝ => V (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt A i x)
    (hA2 : PdiffAt (fun y => pd A i y) i (0 : Point n))
    (hV0ρ : gaussDdim τ (V 0) = ρval * gaussDdim τ z)
    (hVP : ∑ k, V 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, V 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (ρval * A 0)
        + z i / (2 * τ) * gaussDdim τ z * (ρval * (-2 * pd A i 0))
        + gaussDdim τ z * (ρval * pd (fun y => pd A i y) i 0) := by
  unfold witnessSecondXDeriv
  rw [pd_pd_congr_of_eventuallyEq
        (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
        (fun x' => gaussDdim τ (V x') * A x') i (0 : Point n) hrep,
      gaussComp_amp_center_decomp V A P Q τ hτ i hV1 hP1 hA1 hA2,
      hV0ρ, hVP, hPsq, hVQ]
  have hτ' : τ ≠ 0 := hτ.ne'
  have h2τ : (2 : ℝ) * τ ≠ 0 := by positivity
  have h4τ : (4 : ℝ) * τ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **★ B2 — `hD2HexpandOn_concrete`.**  The corrected bridge at the TRUE chart.  For a base
    `z ∈ K` with open gate `0 ∈ S z`, the concrete `witnessSecondXDeriv` obeys the z-Gaussian 3-term
    shape with the ρ-scaled chart amplitudes (`ρval = rhoRatio τ z`), given ONLY the chart jets
    `hV1`/`hP1`, the amplitude jets `hA1`/`hA2`, and the three center identities `hVP`/`hPsq`/`hVQ`.
    Crucially `hV0` is ELIMINATED — supplied by the UNCONDITIONAL ratio `gauss_ratio_rho`
    (`chartImageGauss_ratio`).  This is the corrected `hD2Hexpand` field at the true chart.
    ⚠ NOT `a₁ = R/6`. -/
theorem hD2HexpandOn_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z
            * (rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0)
        + z i / (2 * τ) * gaussDdim τ z
            * (rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0))
        + gaussDdim τ z
            * (rhoRatio g gi hC hK τ z
                * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) :=
  witnessSecondXDeriv_expand_bridge_rho g gi hC hK S a b i τ hτ z
    (uniformInverseChart g gi hC hK z) (chartAmp g gi hC hK a b τ z) P Q
    (rhoRatio g gi hC hK τ z)
    (vanVleckGatedWitness_germ_factor g gi hC hK S a b τ z hz hSopen h0)
    hV1 hP1 hA1 hA2
    (gauss_ratio_rho g gi hC hK τ hτ z)
    hVP hPsq hVQ

/-! ###############################################################################
    S4 — B1: the corrected collar-restricted amplitude bundle.
    ############################################################################### -/

/-- **★★ B1 — THE CORRECTED BUNDLE `AmplitudeDerivativeDataOn`.**  Mirrors `AmplitudeDerivativeData`
    (J4-126) but with `hD2Hexpand` AND the three amplitude bounds conditioned on the PREDICATE
    premise `Regime : ℝ → Point n → Prop` (Sol #12 — predicate premises, NOT subtypes).  The
    conclusion of `hD2Hexpand` is the SAME exact z-Gaussian 3-term shape; the ρ-scaling lives in the
    (regime-restricted) amplitudes `Aamp/A1amp/A2amp`.  The other fields (`hFdom`, the four
    measurabilities, `hqLip`) are UNCHANGED from `AmplitudeDerivativeData`.  A term of this type is
    the collar-restricted derivative-layer deliverable.  ⚠ NOT `a₁ = R/6`. -/
structure AmplitudeDerivativeDataOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (Regime : ℝ → Point n → Prop) where
  /-- The zeroth (Hessian-weighted) amplitude component (ρ-scaled at the true chart). -/
  Aamp : ℝ → Point n → ℝ
  /-- The first (gradient-weighted) amplitude component (ρ-scaled at the true chart). -/
  A1amp : ℝ → Point n → ℝ
  /-- The second (mass-weighted) amplitude component (ρ-scaled at the true chart). -/
  A2amp : ℝ → Point n → ℝ
  /-- Sup-bound constant for `Aamp` (the corrected `K·M₀chart`). -/
  M₀ : ℝ
  /-- Sup-bound constant for `A1amp` (the corrected `K·M₁chart`). -/
  M₁ : ℝ
  /-- Sup-bound constant for `A2amp` (the corrected `K·M₂chart`). -/
  M₂ : ℝ
  /-- Lipschitz constant of the term-1 product `Aamp·F`. -/
  L : ℝ
  /-- Width-2 domination constant for the Levi kernel `F`. -/
  C_L : ℝ
  hM₀ : 0 ≤ M₀
  hM₁ : 0 ≤ M₁
  hM₂ : 0 ≤ M₂
  hL : 0 ≤ L
  hC_L : 0 ≤ C_L
  /-- ★ The Leibniz-Gaussian 3-term identity, RESTRICTED to the regime (Sol #12): the ρ-scaling is
      absorbed into the amplitudes, the conclusion is the exact z-Gaussian shape. -/
  hD2Hexpand : ∀ {τ : ℝ} {z : Point n}, Regime τ z →
      witnessSecondXDeriv g gi hC hK S a b i τ z
        = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * Aamp τ z
          + z i / (2 * τ) * gaussDdim τ z * A1amp τ z
          + gaussDdim τ z * A2amp τ z
  /-- Sup-bound for `Aamp`, RESTRICTED to the regime (the ratio is bounded only on the collar). -/
  hAampBdd : ∀ {τ : ℝ} {z : Point n}, Regime τ z → |Aamp τ z| ≤ M₀
  hA1ampBdd : ∀ {τ : ℝ} {z : Point n}, Regime τ z → |A1amp τ z| ≤ M₁
  hA2ampBdd : ∀ {τ : ℝ} {z : Point n}, Regime τ z → |A2amp τ z| ≤ M₂
  hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)
  hAampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Aamp τ z) volume
  hA1ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A1amp τ z) volume
  hA2ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A2amp τ z) volume
  hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume
  hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T →
      ∀ z w : Point n, |Aamp τ z * F s z 0 - Aamp τ w * F s w 0| ≤ L * dist z w

/-! ###############################################################################
    S5 — B3: the concrete collar bundle at the true chart (assembly).
    ############################################################################### -/

/-- **★★★ B3 — `amplitudeDataOn_concrete`.**  The corrected collar-restricted bundle
    `AmplitudeDerivativeDataOn` INSTANTIATED at the true van-Vleck chart, over the regime
    `collarRegime (K := K) r₀ c τ₀`.  The concrete amplitudes are the ρ-scaled chart amplitudes
      `Aamp  τ z = rhoRatio τ z · chartAmp 0`,
      `A1amp τ z = rhoRatio τ z · (−2·∂ᵢ chartAmp 0)`,
      `A2amp τ z = rhoRatio τ z · ∂ᵢ² chartAmp 0`,
    and the corrected moduli `M_j = collarK · M_jchart`.

    THE CARRIES (honest, per the firewall — the bank the assembly consumes):
      • `hiso` — the near-isometry LOWER bound (`chartW0_rncRadialSq_error`), feeding `ρ ≤ collarK`;
      • `hM·chart`/`hM·chart_nn` — the regime-restricted chart-amplitude sup-bounds + nonnegs;
      • `hjets` — the regime-uniform chart-jet supply (open gate + first/second `i`-jets + amplitude
        jets + the three center identities), feeding `hD2HexpandOn_concrete`;
      • `hFdom`/`hAampmeas`/`hA1ampmeas`/`hA2ampmeas`/`hFmeas`/`hqLip` — the UNCHANGED Levi /
        measurability / Lipschitz feeds (the J4-350 census banked feeds), about the concrete
        ρ-scaled amplitudes.
    The ONE hard field `hD2Hexpand` is DISCHARGED (`hD2HexpandOn_concrete`), with `hV0` eliminated by
    the ratio; the three bounds are DISCHARGED on the collar via `rhoRatio_le_collarK`.
    ⚠ NOT `a₁ = R/6`. -/
noncomputable def amplitudeDataOn_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ : ℝ)
    (Liso c r₀ : ℝ) (hLiso : 0 ≤ Liso)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (M₀chart M₁chart M₂chart Lq C_L : ℝ)
    (hM₀chart_nn : 0 ≤ M₀chart) (hM₁chart_nn : 0 ≤ M₁chart) (hM₂chart_nn : 0 ≤ M₂chart)
    (hLq : 0 ≤ Lq) (hC_L : 0 ≤ C_L)
    (hM₀chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |chartAmp g gi hC hK a b τ z 0| ≤ M₀chart)
    (hM₁chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁chart)
    (hM₂chart : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂chart)
    (hjets : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      IsOpen (S z) ∧ (0 : Point n) ∈ S z ∧
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ x k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i)) ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i)) ∧
        (∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x) ∧
        PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n) ∧
        (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i) ∧
        (∑ k, P 0 k ^ 2 = 1) ∧
        (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n => rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n =>
        rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable
      (fun z : Point n =>
        rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T → ∀ z w : Point n,
      |(rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) * F s z 0
          - (rhoRatio g gi hC hK τ w * chartAmp g gi hC hK a b τ w 0) * F s w 0|
        ≤ Lq * dist z w) :
    AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀) where
  Aamp := fun τ z => rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0
  A1amp := fun τ z => rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)
  A2amp := fun τ z =>
    rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0
  M₀ := collarK (n := n) Liso c τ₀ * M₀chart
  M₁ := collarK (n := n) Liso c τ₀ * M₁chart
  M₂ := collarK (n := n) Liso c τ₀ * M₂chart
  L := Lq
  C_L := C_L
  hM₀ := mul_nonneg (collarK_pos Liso c τ₀).le hM₀chart_nn
  hM₁ := mul_nonneg (collarK_pos Liso c τ₀).le hM₁chart_nn
  hM₂ := mul_nonneg (collarK_pos Liso c τ₀).le hM₂chart_nn
  hL := hLq
  hC_L := hC_L
  hD2Hexpand := by
    intro τ z hreg
    obtain ⟨hSopen, h0, P, Q, hV1, hP1, hA1, hA2, hVP, hPsq, hVQ⟩ := hjets τ z hreg
    exact hD2HexpandOn_concrete g gi hC hK S a b i τ hreg.1 z hreg.2.2.1 hSopen h0
      P Q hV1 hP1 hA1 hA2 hVP hPsq hVQ
  hAampBdd := by
    intro τ z hreg
    show |rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0|
      ≤ collarK (n := n) Liso c τ₀ * M₀chart
    rw [abs_mul, abs_of_pos (rhoRatio_pos g gi hC hK τ z)]
    exact mul_le_mul (rhoRatio_le_collarK g gi hC hK Liso c τ₀ r₀ hLiso hiso τ z hreg)
      (hM₀chart τ z hreg) (abs_nonneg _) (collarK_pos Liso c τ₀).le
  hA1ampBdd := by
    intro τ z hreg
    show |rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)|
      ≤ collarK (n := n) Liso c τ₀ * M₁chart
    rw [abs_mul, abs_of_pos (rhoRatio_pos g gi hC hK τ z)]
    exact mul_le_mul (rhoRatio_le_collarK g gi hC hK Liso c τ₀ r₀ hLiso hiso τ z hreg)
      (hM₁chart τ z hreg) (abs_nonneg _) (collarK_pos Liso c τ₀).le
  hA2ampBdd := by
    intro τ z hreg
    show |rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0|
      ≤ collarK (n := n) Liso c τ₀ * M₂chart
    rw [abs_mul, abs_of_pos (rhoRatio_pos g gi hC hK τ z)]
    exact mul_le_mul (rhoRatio_le_collarK g gi hC hK Liso c τ₀ r₀ hLiso hiso τ z hreg)
      (hM₂chart τ z hreg) (abs_nonneg _) (collarK_pos Liso c τ₀).le
  hFdom := hFdom
  hAampmeas := hAampmeas
  hA1ampmeas := hA1ampmeas
  hA2ampmeas := hA2ampmeas
  hFmeas := hFmeas
  hqLip := hqLip

end QIQTH.AmplitudeDataOnCollar

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AmplitudeDataOnCollar.rncRadialSq_le_nsq
#print axioms QIQTH.AmplitudeDataOnCollar.gauss_ratio_rho
#print axioms QIQTH.AmplitudeDataOnCollar.rhoRatio_pos
#print axioms QIQTH.AmplitudeDataOnCollar.rhoRatio_le_collarK
#print axioms QIQTH.AmplitudeDataOnCollar.witnessSecondXDeriv_expand_bridge_rho
#print axioms QIQTH.AmplitudeDataOnCollar.hD2HexpandOn_concrete
#print axioms QIQTH.AmplitudeDataOnCollar.collarK_pos
#print axioms QIQTH.AmplitudeDataOnCollar.amplitudeDataOn_concrete
