/-
  ErrorKernelFactorization — J4-187 (Sol endgame plan step 9): the EXACT factorized normal form of
  the heat-kernel error kernel `E`, split into (i) the Leibniz/cutoff-annulus decomposition and
  (ii) the Gaussian × amplitude factorization `E_uncut = G_τ · A` of the ungated residual.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a
  structural REPACKAGING of already-banked residual/cutoff algebra into the explicit normal form the
  F1 (joint-measurability) and hEgrad (residual-gradient) walls both consume.  No new heat-kernel
  content, no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What `E` actually is (from the capstone chain).

  The per-base error kernel the Levi/Neumann engine bounds/needs measurable is
    `E τ p q = heatOp g gi (gatedKernel K S H_G) τ p q`,
  where the gated witness `H_G τ p q = radialCutoff a b (W q p) · heatParametrix N Θ u τ (W q p)`.
  On the gate the hard `q`-set-gate is transparent (`GlobalHunifAssembly.gatedKernel_heatOp_eq_of_mem_nhds`),
  so the LIVE object is the DIAGONAL-CHART cutoff-parametrix residual (verbatim the `hEboundW` slot,
  `HeatResidualBound.cutoffResidual_diag_hEboundW`):
    `E v = χ(v)·∂_τH(τ,v) − Δ_g(χ·H)(v)`,   `χ = radialCutoff a b`,  `H = heatParametrix N Θ u τ`.
  Because `χ` is `τ`-independent, `∂_τ(χH) = χ·∂_τH`, so `E = heatOp g gi (fun τ p _ => χ p · H τ p)`.

  ## What this file delivers (ns `QIQTH.ErrorKernelFactorization`).

    * (1) `heatOp_gated_split` — THE LEIBNIZ / CUTOFF-ANNULUS SPLIT.  Applying the banked smooth
      Laplace–Beltrami product rule `HeatResidualBound.laplaceBeltrami_mul_inf`,
        `E = χ·(∂_τH − Δ_gH) − annulusTerms`,
      the first factor being `χ · (uncut residual)` and `annulusTerms = H·Δ_gχ + 2gⁱʲ∂ᵢχ∂ⱼH` the two
      Leibniz cross terms — the EXACT identity the global-bound engine uses internally, here isolated.

    * (2) `residual_eq_gauss_mul_A` — THE CORE FACTORIZATION `E_uncut = G_τ · A`.  The ungated order-`N`
      residual `parametrixResidualN N g gi Θ u τ v = gaussDdim τ v · residualCoeffA …`, with the
      amplitude `residualCoeffA` the explicit Seeley–DeWitt polynomial in `{1/τ, 1/τ², jets, transport
      coefficients}` obtained by factoring the common Gaussian out of the banked assembled residual
      `HeatResidualBound.parametrixResidual_offdiag_O1_total`.  Pure repackaging (`rw` + `ring`).

    * (2′) `cutoffError_eq_cutoff_gauss_A_sub_annulus` — the FULL assembled normal form: combining (1)
      and (2) at the concrete parametrix,  `E = χ·G_τ·A − annulusTerms`.

    * (3) `annulusTerms_eq_zero_near` / `annulusTerms_eq_zero_far` — THE ANNULUS-SUPPORT LEMMAS.  Both
      cross terms vanish off the cutoff annulus `a ≤ ‖v‖ ≤ b` (`rncRadialSq v < a²` or `b² < rncRadialSq v`),
      from the banked cutoff-derivative support facts `HeatResidualBound.{laplaceBeltrami_radialCutoff_zero_near,
      pd_radialCutoff_eq_zero_of_near}` (and `…_far`).

    * (4) `residualCoeffA_measurable_of_factors` — THE F1 FEED.  The amplitude `A` is jointly
      `(τ,v)`-measurable once the finitely many scalar FACTOR fields (`gi`, `christoffel`, `foldedCoeff`,
      its `Δ_g`, and the poly-gradient `pd P`) are jointly measurable — a genuine measurable-algebra
      reduction with the derivative-field carries stated honestly (the SAME factor carries as J4-185).

    * (5) `annulusTerms_measurable_of_factors` — the companion measurable-algebra reduction for the
      cross terms, feeding the same F1 slot.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  Diagonal-chart, single base point.  The factorization is EXACT algebra;
  the measurability lemmas CARRY the derivative-field joint measurabilities (the genuine F1 residue —
  they are the joint `q`-regularity wall, not discharged here).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParametrixResidualO1Total
import QIQTH.CutoffResidualGlobalBound
import QIQTH.CutoffAnnulusSupport

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound
open scoped BigOperators ContDiff

namespace QIQTH.ErrorKernelFactorization

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ## 1.  The Leibniz / cutoff-annulus split of `E`. -/

/-- **The diagonal-chart cutoff error kernel** `E v = χ(v)·dtH(v) − Δ_g(χ·H)(v)`, `χ = radialCutoff a b`.
    Here `H : Point n → ℝ` is the (time-frozen) spatial parametrix section and `dtH : Point n → ℝ` its
    time-derivative field `∂_τH(τ,·)`.  Since `χ` is `τ`-independent this is exactly `heatOp g gi (χ·H)`
    on the diagonal — the verbatim `hEboundW` object (`HeatResidualBound.cutoffResidual_diag_hEboundW`). -/
noncomputable def cutoffErrorKernel (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (H dtH : Point n → ℝ) (v : Point n) : ℝ :=
  radialCutoff a b v * dtH v - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v

/-- **The two Leibniz cross terms** `annulusTerms = H·Δ_gχ + 2·gⁱʲ(∂ᵢχ)(∂ⱼH)`.  These are supported on
    the cutoff annulus `a ≤ ‖v‖ ≤ b` (see `annulusTerms_eq_zero_near`/`_far`). -/
noncomputable def annulusTerms (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (H : Point n → ℝ) (v : Point n) : ℝ :=
  H v * laplaceBeltrami g gi (radialCutoff a b) v
    + 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v

/-- **(1) THE LEIBNIZ / CUTOFF-ANNULUS SPLIT.**  For a smooth spatial section `H` and symmetric inverse
    metric at `v`, the cutoff error kernel factorizes as
      `E v = χ(v)·(dtH v − Δ_gH v) − annulusTerms`,
    i.e. `χ · (uncut residual) −` the two cross terms.  Direct from the banked smooth Laplace–Beltrami
    product rule `laplaceBeltrami_mul_inf`; no cancellation, no heat-kernel data. -/
theorem heatOp_gated_split (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (H dtH : Point n → ℝ) (v : Point n) (hH : ContDiff ℝ ∞ H)
    (hgisymm : ∀ i j, gi v i j = gi v j i) :
    cutoffErrorKernel g gi a b H dtH v
      = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
        - annulusTerms g gi a b H v := by
  have hlbmul := laplaceBeltrami_mul_inf g gi (radialCutoff a b) H v
    (radialCutoff_contDiff a b) hH hgisymm
  simp only [cutoffErrorKernel, annulusTerms, hlbmul]
  ring

/-! ## 2.  The core Gaussian × amplitude factorization `E_uncut = G_τ · A`. -/

/-- **The Seeley–DeWitt residual amplitude `A`** — the ungated order-`N` residual with the common
    Gaussian `gaussDdim τ v` factored out.  This is exactly the RHS of the banked assembled residual
    `parametrixResidual_offdiag_O1_total` divided by `G_τ = gaussDdim τ v`: an explicit polynomial in
    `{1/τ, 1/τ², the inverse-metric/Christoffel deviation brackets, the folded DeWitt coefficients and
    their radial/Laplacian jets}`.  (`P = Σ_{k≤N} w_k·τ^k`, `w_k = foldedCoeff Θ u k`.) -/
noncomputable def residualCoeffA (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (v : Point n) : ℝ :=
  ((1 / t)
        * ((1 / 2) * (∑ i, (gi v i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
      + (1 / t ^ 2)
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
      * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
    + (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
    + ((1 / t) * radialDeriv (foldedCoeff Θ u 0) v
        + ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k)
    - (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
    - (1 / t)
        * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
                + v j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v))

/-- **(2) THE CORE FACTORIZATION `E_uncut = G_τ · A`.**  The ungated order-`N` heat-operator residual
    equals the flat Gaussian times the amplitude `A`:
      `parametrixResidualN N g gi Θ u τ v = gaussDdim τ v · residualCoeffA N g gi Θ u τ v`.
    Pure repackaging of `parametrixResidual_offdiag_O1_total`: every summand there carries the common
    factor `gaussDdim τ v`, and `ring` performs the extraction.  Only coefficient smoothness `hw` is
    used; the metric is arbitrary.  NOT the cancellation to `0`. -/
theorem residual_eq_gauss_mul_A (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN N g gi Θ u t v
      = gaussDdim t v * residualCoeffA N g gi Θ u t v := by
  rw [parametrixResidual_offdiag_O1_total N g gi Θ u t ht v hw]
  simp only [residualCoeffA]
  ring

/-- **(2′) THE FULL ASSEMBLED NORMAL FORM `E = χ·G_τ·A − annulusTerms`.**  At the concrete parametrix
    `H = heatParametrix N Θ u τ`, `dtH = ∂_τH`, combining the Leibniz split (1) with the core
    factorization (2) (the uncut residual `∂_τH − Δ_gH` is literally `parametrixResidualN`):
      `E v = χ(v)·(gaussDdim τ v · residualCoeffA …) − annulusTerms`.
    This is the exact residual normal form F1 (measurability) and hEgrad (gradient) both consume:
    a cutoff × Gaussian × explicit amplitude, minus annulus-supported cross terms. -/
theorem cutoffError_eq_cutoff_gauss_A_sub_annulus (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hgisymm : ∀ i j, gi v i j = gi v j i) :
    cutoffErrorKernel g gi a b (heatParametrix N Θ u t)
        (fun w => deriv (fun s => heatParametrix N Θ u s w) t) v
      = radialCutoff a b v * (gaussDdim t v * residualCoeffA N g gi Θ u t v)
        - annulusTerms g gi a b (heatParametrix N Θ u t) v := by
  -- `H = heatParametrix N Θ u t = gaussDdim t · Σ w_k t^k` is smooth (folded form).
  have hH : ContDiff ℝ ∞ (heatParametrix N Θ u t) := by
    have hHeq : heatParametrix N Θ u t
        = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
      funext (fun y => heatParametrix_folded N Θ u t y)
    rw [hHeq]
    exact ((gaussDdim_contDiff t).mul
      (ContDiff.sum fun k _ => (hw k).mul contDiff_const)).of_le le_top
  rw [heatOp_gated_split g gi a b (heatParametrix N Θ u t)
      (fun w => deriv (fun s => heatParametrix N Θ u s w) t) v hH hgisymm]
  -- the uncut residual `∂_τH − Δ_gH` is definitionally `parametrixResidualN`, then apply (2).
  have huncut : (deriv (fun s => heatParametrix N Θ u s v) t
        - laplaceBeltrami g gi (heatParametrix N Θ u t) v)
      = parametrixResidualN N g gi Θ u t v := rfl
  rw [huncut, residual_eq_gauss_mul_A N g gi Θ u t ht v hw]

/-! ## 3.  The cutoff-annulus support of the cross terms. -/

/-- **(3a) ANNULUS SUPPORT — NEAR.**  Inside the cutoff-constant ball `rncRadialSq v < a²`, both Leibniz
    cross terms vanish: `Δ_gχ = 0` and every `∂ᵢχ = 0` there.  Hence `annulusTerms = 0`. -/
theorem annulusTerms_eq_zero_near (g gi : Point n → Fin n → Fin n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (H : Point n → ℝ) {v : Point n} (hv : rncRadialSq v < a ^ 2) :
    annulusTerms g gi a b H v = 0 := by
  have hlap : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
    laplaceBeltrami_radialCutoff_zero_near g gi ha hab hv
  have hpd : ∀ i, pd (radialCutoff a b) i v = 0 :=
    fun i => pd_radialCutoff_eq_zero_of_near ha hab hv i
  simp only [annulusTerms, hlap, mul_zero, zero_add]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [hpd i]; ring

/-- **(3b) ANNULUS SUPPORT — FAR.**  Outside the cutoff support `b² < rncRadialSq v`, both Leibniz cross
    terms vanish (`χ ≡ 0` there, so all its derivatives are `0`).  Hence `annulusTerms = 0`. -/
theorem annulusTerms_eq_zero_far (g gi : Point n → Fin n → Fin n → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (H : Point n → ℝ) {v : Point n} (hv : b ^ 2 < rncRadialSq v) :
    annulusTerms g gi a b H v = 0 := by
  have hlap : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
    laplaceBeltrami_radialCutoff_zero_far g gi ha hab hv
  have hpd : ∀ i, pd (radialCutoff a b) i v = 0 :=
    fun i => pd_radialCutoff_eq_zero_of_far ha hab hv i
  simp only [annulusTerms, hlap, mul_zero, zero_add]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [hpd i]; ring

/-! ## 4.  The F1 feed — joint measurability of the amplitude and cross terms from factor carries. -/

/-- **(4) THE F1 FEED — joint measurability of the amplitude `A`.**  The amplitude `residualCoeffA`,
    viewed as a joint field `(τ,v) ↦ A`, is measurable once the finitely many scalar FACTOR fields it is
    built from are jointly measurable:
      • `hgi`   — the inverse-metric components `(τ,v) ↦ gⁱʲ(v)`;
      • `hchr`  — the Christoffel components `(τ,v) ↦ Γᵏᵢⱼ(v)`;
      • `hfold` — the folded DeWitt coefficients `(τ,v) ↦ w_k(v)`;
      • `hlap`  — their Laplace–Beltramis `(τ,v) ↦ Δ_g w_k(v)`;
      • `hrad`  — their radial derivatives `(τ,v) ↦ (r∂_r w_k)(v)`;
      • `hpdP`  — the parametrix-polynomial gradient `(τ,v) ↦ ∂ⱼ(Σ_k w_k·τ^k)(v)`  (the genuine
        derivative-field carry — the joint `q`-regularity residue, NOT discharged here).
    These are EXACTLY the unified factor carries of the J4-185 gated-`D` representative.  The proof is
    pure measurable algebra (`fun_prop`): `1/τ, τ^k` are continuous, `vⁱ = πᵢ∘snd`, and every atom is a
    carry.  This turns F1-for-`A` into "the factor fields are jointly measurable". -/
theorem residualCoeffA_measurable_of_factors (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hgi : ∀ i j, Measurable (fun w : ℝ × Point n => gi w.2 i j))
    (hchr : ∀ k i j, Measurable (fun w : ℝ × Point n => christoffel g gi k i j w.2))
    (hfold : ∀ k, Measurable (fun w : ℝ × Point n => foldedCoeff Θ u k w.2))
    (hlap : ∀ k, Measurable (fun w : ℝ × Point n => laplaceBeltrami g gi (foldedCoeff Θ u k) w.2))
    (hrad : ∀ k, Measurable (fun w : ℝ × Point n => radialDeriv (foldedCoeff Θ u k) w.2))
    (hpdP : ∀ j, Measurable (fun w : ℝ × Point n =>
      pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * w.1 ^ k) j w.2)) :
    Measurable (fun w : ℝ × Point n => residualCoeffA N g gi Θ u w.1 w.2) := by
  have mv : ∀ i, Measurable (fun w : ℝ × Point n => w.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  have minvt : Measurable (fun w : ℝ × Point n => 1 / w.1) :=
    measurable_const.div measurable_fst
  have minvt2 : Measurable (fun w : ℝ × Point n => 1 / w.1 ^ 2) :=
    measurable_const.div (measurable_fst.pow_const 2)
  have mtk : ∀ k : ℕ, Measurable (fun w : ℝ × Point n => w.1 ^ k) :=
    fun k => measurable_fst.pow_const k
  simp only [residualCoeffA]
  -- the leading `(1/t)`/`(1/t²)` metric-deviation brackets `b1`, `b2`
  have hb1 : Measurable (fun w : ℝ × Point n =>
      (1 / 2 : ℝ) * (∑ i, (gi w.2 i i - 1))
        - (1 / 2 : ℝ) * (∑ i, ∑ j, ∑ k, gi w.2 i j * christoffel g gi k i j w.2 * w.2 k)) :=
    ((Finset.measurable_sum _ (fun i _ => (hgi i i).sub_const 1)).const_mul _).sub
      ((Finset.measurable_sum _ (fun i _ =>
        Finset.measurable_sum _ (fun j _ =>
          Finset.measurable_sum _ (fun k _ =>
            ((hgi i j).mul (hchr k i j)).mul (mv k))))).const_mul _)
  have hb2 : Measurable (fun w : ℝ × Point n =>
      (-1 / 4 : ℝ) * (∑ i, ∑ j, (gi w.2 i j - (if i = j then (1 : ℝ) else 0)) * (w.2 i * w.2 j))) :=
    (Finset.measurable_sum _ (fun i _ =>
      Finset.measurable_sum _ (fun j _ =>
        ((hgi i j).sub_const (if i = j then (1 : ℝ) else 0)).mul ((mv i).mul (mv j))))).const_mul _
  have hpoly : Measurable (fun w : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k w.2 * w.1 ^ k) :=
    Finset.measurable_sum _ (fun k _ => (hfold k).mul (mtk k))
  have hT1 := ((minvt.mul hb1).add (minvt2.mul hb2)).mul hpoly
  have hterm2 : Measurable (fun w : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k w.2 * ((k : ℝ) * w.1 ^ (k - 1))) :=
    Finset.measurable_sum _ (fun k _ => (hfold k).mul (measurable_const.mul (mtk (k - 1))))
  have hterm3 := (minvt.mul (hrad 0)).add
    (Finset.measurable_sum (Finset.range N) (fun k _ => (hrad (k + 1)).mul (mtk k)))
  have hterm4 : Measurable (fun w : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) w.2 * w.1 ^ k) :=
    Finset.measurable_sum _ (fun k _ => (hlap k).mul (mtk k))
  have hdev : Measurable (fun w : ℝ × Point n =>
      (-1 / 2 : ℝ) * ∑ i, ∑ j, (gi w.2 i j - (if i = j then (1 : ℝ) else 0))
          * (w.2 i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * w.1 ^ k) j w.2
              + w.2 j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * w.1 ^ k) i w.2)) :=
    (Finset.measurable_sum _ (fun i _ =>
      Finset.measurable_sum _ (fun j _ =>
        ((hgi i j).sub_const (if i = j then (1 : ℝ) else 0)).mul
          (((mv i).mul (hpdP j)).add ((mv j).mul (hpdP i)))))).const_mul _
  have hterm5 := minvt.mul hdev
  exact (((hT1.add hterm2).add hterm3).sub hterm4).sub hterm5

/-- **(5) THE COMPANION CROSS-TERM MEASURABILITY.**  The Leibniz cross terms `annulusTerms`, viewed as a
    joint field, are measurable once the field `H`, the cutoff's `Δ_gχ` and `∂ᵢχ`, the metric, and the
    field-gradient `∂ⱼH` are jointly measurable (`∂χ`/`Δ_gχ` are even continuous — `χ ∈ C^∞`; carried
    abstractly for base-point uniformity).  Feeds the SAME F1 slot as (4). -/
theorem annulusTerms_measurable_of_factors (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (Hj : ℝ × Point n → ℝ) (H : ℝ × Point n → Point n → ℝ)
    (hHj : Measurable Hj)
    (hgi : ∀ i j, Measurable (fun w : ℝ × Point n => gi w.2 i j))
    (hLapChi : Measurable (fun w : ℝ × Point n => laplaceBeltrami g gi (radialCutoff a b) w.2))
    (hDchi : ∀ i, Measurable (fun w : ℝ × Point n => pd (radialCutoff a b) i w.2))
    (hDH : ∀ j, Measurable (fun w : ℝ × Point n => pd (H w) j w.2)) :
    Measurable (fun w : ℝ × Point n =>
      Hj w * laplaceBeltrami g gi (radialCutoff a b) w.2
        + 2 * ∑ i, ∑ j, gi w.2 i j * pd (radialCutoff a b) i w.2 * pd (H w) j w.2) := by
  refine (hHj.mul hLapChi).add ?_
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => ((hgi i j).mul (hDchi i)).mul (hDH j)))

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms heatOp_gated_split
#print axioms residual_eq_gauss_mul_A
#print axioms cutoffError_eq_cutoff_gauss_A_sub_annulus
#print axioms annulusTerms_eq_zero_near
#print axioms annulusTerms_eq_zero_far
#print axioms residualCoeffA_measurable_of_factors
#print axioms annulusTerms_measurable_of_factors

end AxiomChecks

end QIQTH.ErrorKernelFactorization
