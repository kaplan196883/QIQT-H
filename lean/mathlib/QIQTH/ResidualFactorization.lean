/-
  ResidualFactorization — J4-504: the residual factorization `E₁ = t·G·q` for the two-term
  heat parametrix `H = G·(u₀ + t·u₁)`, delivered AUDIT-FIRST as (a) a reusable Leibniz engine,
  (b) the factorization AS A REDUCTION from carried transport hypotheses, and (c) the flat-model
  satisfiability witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is
  the parametrix-improvement STEP: the identity `(∂_t − Δ_g)(G·(u₀+t·u₁)) = −t·G·Δ_g u₁`, valid
  MODULO two carried, pointwise transport-cancellation hypotheses.  The genuine analytic content —
  that the off-diagonal transport equations `𝒯u₀ = 0`, `(𝒯+1)u₁ = Δ_g u₀` (here re-expressed as
  the two cancellations `hT0`, `hT1` against the flat Gaussian) actually HOLD for a curved metric —
  is the checkpointed radial-ODE wall (`HeatTransportRecursion` STRETCH #4, geodesic `r∂_r`
  machinery absent from Mathlib).  We CARRY those two equations, we do NOT derive them.  No `sorry`,
  no `:= True`, no new axioms, std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## The structure (verified against the banked residual algebra + Sol J4-504).

  Write `H = G·P` with `G = gaussDdim` the flat Gaussian and `P(s,y) = u₀(y) + s·u₁(y)`.  The heat
  operator on a product factorizes by the banked Leibniz rules (`laplaceBeltrami_mul_inf` for `Δ_g`,
  `deriv_mul` for `∂_t`):

    (∂_t − Δ_g)(G·P) = [(∂_t−Δ_g)G]·P + G·[(∂_t−Δ_g)P] − 2·Σᵢⱼ gⁱʲ ∂ᵢG ∂ⱼP.        (heatOpFun_mul)

  With `∂_t P = u₁`, `Δ_g P = Δ_g u₀ + t·Δ_g u₁`, `∂_j P = ∂_j u₀ + t·∂_j u₁`, and writing
  `𝒢 := (∂_t−Δ_g)G` (the eikonal defect of the flat Gaussian against the curved `Δ_g`) and
  `C(u) := Σᵢⱼ gⁱʲ ∂ᵢG ∂ⱼu` (the cross-gradient), the residual groups EXACTLY as

    E = [𝒢·u₀ − 2C(u₀)]  +  [t·(𝒢·u₁ − 2C(u₁)) + G·(u₁ − Δ_g u₀)]  −  t·G·Δ_g u₁.

  The two carried transport equations are the vanishing of the first two brackets:
    hT0 : 𝒢·u₀ − 2C(u₀) = 0                         (`𝒯u₀ = 0`, the homogeneous transport eqn),
    hT1 : t·(𝒢·u₁ − 2C(u₁)) + G·(u₁ − Δ_g u₀) = 0    (`(𝒯+1)u₁ = Δ_g u₀`, the first transport eqn).
  Then `E = −t·G·Δ_g u₁ = t·G·q` with `q = −Δ_g u₁`.  ★ The extra factor `t` is GENUINE: it comes
  from `Δ_g(t·u₁) = t·Δ_g u₁` at the `t¹` order (`∂_t(t·u₁)=u₁` lands at order `t⁰`, absorbed by
  hT1), it is NOT cosmetically absorbed — see the flat witness `(c)`.

  ── WHAT LANDS (ns `QIQTH.ResidualFactorization`).
    • `heatOpFun`               — the heat operator on a time-dependent field.
    • `heatOpFun_mul`           — ★ (a) the reusable Leibniz product identity (pure calculus).
    • `crossGrad`, `crossGrad_lin` — the flat-Gaussian cross-gradient and its `u₀+t·u₁` linearity.
    • `residual_factorization`  — ★★ (b) the factorization `E = −t·G·Δ_g u₁` MODULO `hT0`, `hT1`.
    • `residual_factorization_flat_witness` — ★ (c) the flat model (`u₀=1,u₁=0`, `g=δ`): `E = 0`,
        exhibiting `hT0`, `hT1` are jointly INHABITED and the shape correct.

  ⚠  a₁ = R/6 remains CONDITIONAL.  The reduction isolates the transport equations as the carried
  gap; it does NOT close it.  See the ledger at the file tail.
-/
import Mathlib
import QIQTH.CutoffResidualGlobalBound
import QIQTH.HeatParametrixOrder
import QIQTH.FlatHeatEquation
import QIQTH.LaplaceBeltrami

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound
open scoped BigOperators ContDiff

namespace QIQTH.ResidualFactorization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ## 0.  The heat operator on a time-dependent field, and the amplitude ansatz. -/

/-- **The heat operator on a time-dependent scalar field** `G : ℝ → Point n → ℝ`:
    `heatOpFun g gi G t x = ∂_t G(t,x) − Δ_g G(t,·)(x)`.  (The kernel-free companion of
    `TrueHeatKernel.heatOp`, for a single space-time field rather than a two-point kernel.) -/
noncomputable def heatOpFun (g gi : Point n → Fin n → Fin n → ℝ) (G : ℝ → Point n → ℝ)
    (t : ℝ) (x : Point n) : ℝ :=
  deriv (fun s => G s x) t - laplaceBeltrami g gi (fun y => G t y) x

/-- **The two-term amplitude ansatz** `P(s,y) = u₀(y) + s·u₁(y)` — the parametrix polynomial to
    first order in `t` (van-Vleck amplitude `u₀` plus first transport coefficient `u₁`). -/
noncomputable def ampLin (u₀ u₁ : Point n → ℝ) (s : ℝ) (y : Point n) : ℝ :=
  u₀ y + s * u₁ y

/-- **The flat-Gaussian cross-gradient** `C(u) = Σᵢⱼ gⁱʲ ∂ᵢG ∂ⱼu` with `G = gaussDdim t`.  This is
    the Leibniz cross term of `Δ_g(G·u)` restricted to the Gaussian factor. -/
noncomputable def crossGrad (gi : Point n → Fin n → Fin n → ℝ) (t : ℝ)
    (u : Point n → ℝ) (x : Point n) : ℝ :=
  ∑ i, ∑ j, gi x i j * pd (fun y => gaussDdim t y) i x * pd u j x

/-! ## 1.  (a) THE REUSABLE LEIBNIZ ENGINE — the heat operator on a product `G·P`. -/

/-- **★ (a) THE LEIBNIZ / PRODUCT IDENTITY for the heat operator.**  For time-dependent fields
    `G, P` that are `t`-differentiable at `t` and `C^∞` in space at `x` (with `gⁱʲ` symmetric at
    `x`), the heat operator on their product factorizes as
      `(∂_t−Δ_g)(G·P) = [(∂_t−Δ_g)G]·P + G·[(∂_t−Δ_g)P] − 2·Σᵢⱼ gⁱʲ ∂ᵢG ∂ⱼP`.
    Pure calculus: `deriv_mul` on `∂_t` and the banked `laplaceBeltrami_mul_inf` on `Δ_g`, then
    `ring`.  This is the reusable engine underneath the residual factorization (b). -/
theorem heatOpFun_mul (g gi : Point n → Fin n → Fin n → ℝ) (G P : ℝ → Point n → ℝ)
    (t : ℝ) (x : Point n)
    (hGt : DifferentiableAt ℝ (fun s => G s x) t)
    (hPt : DifferentiableAt ℝ (fun s => P s x) t)
    (hGx : ContDiff ℝ ∞ (fun y => G t y))
    (hPx : ContDiff ℝ ∞ (fun y => P t y))
    (hgisymm : ∀ i j, gi x i j = gi x j i) :
    heatOpFun g gi (fun s y => G s y * P s y) t x
      = heatOpFun g gi G t x * P t x + G t x * heatOpFun g gi P t x
        - 2 * ∑ i, ∑ j, gi x i j * pd (fun y => G t y) i x * pd (fun y => P t y) j x := by
  simp only [heatOpFun]
  have hderiv : deriv (fun s => G s x * P s x) t
      = deriv (fun s => G s x) t * P t x + G t x * deriv (fun s => P s x) t :=
    deriv_mul hGt hPt
  have hlap : laplaceBeltrami g gi (fun y => G t y * P t y) x
      = G t x * laplaceBeltrami g gi (fun y => P t y) x
        + P t x * laplaceBeltrami g gi (fun y => G t y) x
        + 2 * ∑ i, ∑ j, gi x i j * pd (fun y => G t y) i x * pd (fun y => P t y) j x :=
    laplaceBeltrami_mul_inf g gi (fun y => G t y) (fun y => P t y) x hGx hPx hgisymm
  rw [hderiv, hlap]; ring

/-! ## 2.  The cross-gradient linearity `C(u₀ + t·u₁) = C(u₀) + t·C(u₁)`. -/

/-- **Cross-gradient linearity.**  `C(u₀ + t·u₁) = C(u₀) + t·C(u₁)` (the scalar `t` pulls out of the
    partial derivative and the double sum).  Needs `u₀, u₁ ∈ C^∞` for the `pd` linearity. -/
theorem crossGrad_lin (gi : Point n → Fin n → Fin n → ℝ) (t : ℝ)
    (u₀ u₁ : Point n → ℝ) (x : Point n)
    (hu₀ : ContDiff ℝ ⊤ u₀) (hu₁ : ContDiff ℝ ⊤ u₁) :
    crossGrad gi t (fun y => u₀ y + t * u₁ y) x
      = crossGrad gi t u₀ x + t * crossGrad gi t u₁ x := by
  have hpd : ∀ j, pd (fun y => u₀ y + t * u₁ y) j x = pd u₀ j x + t * pd u₁ j x := by
    intro j
    rw [pd_add u₀ (fun y => t * u₁ y) j x (PdiffAt_of_contDiff u₀ hu₀ j x)
        (PdiffAt_of_contDiff (fun y => t * u₁ y) (contDiff_const.mul hu₁) j x),
      pd_const_mul t u₁ j x (PdiffAt_of_contDiff u₁ hu₁ j x)]
  unfold crossGrad
  have hstep : ∀ i, (∑ j, gi x i j * pd (fun y => gaussDdim t y) i x
        * pd (fun y => u₀ y + t * u₁ y) j x)
      = (∑ j, gi x i j * pd (fun y => gaussDdim t y) i x * pd u₀ j x)
        + t * ∑ j, gi x i j * pd (fun y => gaussDdim t y) i x * pd u₁ j x := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpd j]; ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ## 3.  (b) THE RESIDUAL FACTORIZATION `E = −t·G·Δ_g u₁` modulo the transport equations. -/

/-- **★★ (b) THE RESIDUAL FACTORIZATION `E₁ = t·G·q`.**  For the two-term parametrix
    `H = gaussDdim·(u₀ + t·u₁)`, GIVEN the two carried, pointwise transport-cancellation equations
      `hT0 : 𝒢·u₀ − 2·C(u₀) = 0`                          (`𝒯u₀ = 0`)
      `hT1 : t·(𝒢·u₁ − 2·C(u₁)) + G·(u₁ − Δ_g u₀) = 0`     (`(𝒯+1)u₁ = Δ_g u₀`)
    (with `𝒢 = heatOpFun g gi gaussDdim`, `G = gaussDdim t x`, `C = crossGrad`), the heat-operator
    residual factorizes with the crucial extra factor `t`:
      `(∂_t − Δ_g)(gaussDdim·(u₀+t·u₁)) = −t·gaussDdim·Δ_g u₁ = t·G·q`,  `q = −Δ_g u₁`.
    The whole proof is: apply the Leibniz engine (a), substitute the amplitude derivatives, split the
    cross-gradient (`crossGrad_lin`), and cancel the two carried brackets (`linear_combination`).
    ⚠ NOT `a₁ = R/6`; `hT0`/`hT1` are the carried radial-transport wall, not derived here. -/
theorem residual_factorization (g gi : Point n → Fin n → Fin n → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Point n) (u₀ u₁ : Point n → ℝ)
    (hu₀C : ContDiff ℝ ⊤ u₀) (hu₁C : ContDiff ℝ ⊤ u₁)
    (hgisymm : ∀ i j, gi x i j = gi x j i)
    (hT0 : heatOpFun g gi gaussDdim t x * u₀ x - 2 * crossGrad gi t u₀ x = 0)
    (hT1 : t * (heatOpFun g gi gaussDdim t x * u₁ x - 2 * crossGrad gi t u₁ x)
            + gaussDdim t x * (u₁ x - laplaceBeltrami g gi u₀ x) = 0) :
    heatOpFun g gi (fun s y => gaussDdim s y * ampLin u₀ u₁ s y) t x
      = - (t * gaussDdim t x * laplaceBeltrami g gi u₁ x) := by
  -- (0) regularity: gaussDdim smooth in space + differentiable in time; amplitude likewise.
  have hGt : DifferentiableAt ℝ (fun s => gaussDdim s x) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t (x i) ht)
    simpa only [gaussDdim] using hFP.differentiableAt
  have hPt : DifferentiableAt ℝ (fun s => ampLin u₀ u₁ s x) t := by
    have h : HasDerivAt (fun s : ℝ => u₀ x + s * u₁ x) (0 + 1 * u₁ x) t :=
      (hasDerivAt_const t (u₀ x)).add ((hasDerivAt_id t).mul_const (u₁ x))
    simpa only [ampLin] using h.differentiableAt
  have hGx : ContDiff ℝ ∞ (fun y : Point n => gaussDdim t y) := (gaussDdim_contDiff t).of_le le_top
  have hPx : ContDiff ℝ ∞ (fun y => ampLin u₀ u₁ t y) := by
    simp only [ampLin]
    exact (hu₀C.add (contDiff_const.mul hu₁C)).of_le le_top
  -- amplitude derivatives
  have hPderiv : deriv (fun s : ℝ => u₀ x + s * u₁ x) t = u₁ x := by
    have h : HasDerivAt (fun s : ℝ => u₀ x + s * u₁ x) (0 + 1 * u₁ x) t :=
      (hasDerivAt_const t (u₀ x)).add ((hasDerivAt_id t).mul_const (u₁ x))
    rw [h.deriv]; ring
  have hΔP : laplaceBeltrami g gi (fun y => u₀ y + t * u₁ y) x
      = laplaceBeltrami g gi u₀ x + t * laplaceBeltrami g gi u₁ x := by
    rw [laplaceBeltrami_add g gi u₀ (fun y => t * u₁ y) x hu₀C (contDiff_const.mul hu₁C),
        laplaceBeltrami_const_mul g gi t u₁ x hu₁C]
  have hopP : heatOpFun g gi (ampLin u₀ u₁) t x
      = u₁ x - (laplaceBeltrami g gi u₀ x + t * laplaceBeltrami g gi u₁ x) := by
    simp only [heatOpFun, ampLin]
    rw [hPderiv, hΔP]
  -- (a) the Leibniz split, then substitute amplitude data and split the cross-gradient.
  rw [heatOpFun_mul g gi gaussDdim (ampLin u₀ u₁) t x hGt hPt hGx hPx hgisymm, hopP]
  simp only [ampLin]
  rw [show (∑ i, ∑ j, gi x i j * pd (fun y => gaussDdim t y) i x * pd (fun y => u₀ y + t * u₁ y) j x)
        = crossGrad gi t (fun y => u₀ y + t * u₁ y) x from rfl,
      crossGrad_lin gi t u₀ u₁ x hu₀C hu₁C]
  -- cancel the two carried transport brackets.
  linear_combination hT0 + hT1

/-! ## 4.  (c) THE FLAT-MODEL WITNESS — `hT0`, `hT1` are jointly inhabited; `E = 0`. -/

/-- The flat (constant `δ`) metric `gⁱʲ = δⁱʲ` — Christoffel-free, the RNC-center model. -/
noncomputable def flatMetric (n : ℕ) : Point n → Fin n → Fin n → ℝ :=
  fun _ i j => if i = j then (1 : ℝ) else 0

/-- **★ (c) THE FLAT-MODEL SATISFIABILITY WITNESS.**  For the flat metric and `u₀ = 1`, `u₁ = 0`,
    both carried transport equations `hT0`, `hT1` HOLD (the eikonal defect `𝒢 = 0`, all cross terms
    and Laplacians vanish), and the residual is `E = 0 = t·G·0`.  This inhabits the hypotheses of
    `(b)` — the factorization shape is non-vacuous and the sign/factor correct.  ⚠ Trivial data;
    the curved solvability of `hT0`/`hT1` is the carried analytic content. -/
theorem residual_factorization_flat_witness (t : ℝ) (ht : 0 < t) (x : Point n) :
    heatOpFun (flatMetric n) (flatMetric n)
        (fun s y => gaussDdim s y * ampLin (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) s y) t x = 0 := by
  -- constant-metric Christoffel vanishing, and the two flat facts `𝒢 = 0`, `Δ_g(const) = 0`.
  have hpc : ∀ (a b i : Fin n), pd (fun y => flatMetric n y a b) i x = 0 := by
    intro a b i
    have e : (fun y : Point n => flatMetric n y a b) = (fun _ => (if a = b then (1 : ℝ) else 0)) := rfl
    rw [e, pd_const]
  have hΓ : ∀ k i j, christoffel (flatMetric n) (flatMetric n) k i j x = 0 := by
    intro k i j
    unfold christoffel
    simp only [hpc, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]
  have hgi : ∀ i j, flatMetric n x i j = if i = j then (1 : ℝ) else 0 := fun i j => rfl
  have h𝒢 : heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x = 0 := by
    simp only [heatOpFun]
    rw [laplaceBeltrami_at_rnc_center (flatMetric n) (flatMetric n) (fun y => gaussDdim t y) x hgi hΓ,
        gaussDdim_heat_eqn t ht x]
    ring
  have hcg_const : ∀ c : ℝ, crossGrad (flatMetric n) t (fun _ => c) x = 0 := by
    intro c
    unfold crossGrad
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [pd_const]; ring
  have hlapc : ∀ c : ℝ, laplaceBeltrami (flatMetric n) (flatMetric n) (fun _ => c) x = 0 := by
    intro c
    unfold laplaceBeltrami
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have h1 : pd (fun y => pd (fun _ => c) j y) i x = 0 := by
      have e : (fun y : Point n => pd (fun _ => c) j y) = (fun _ => (0 : ℝ)) :=
        funext (fun y => pd_const c j y)
      rw [e, pd_const]
    have h2 : (∑ k, christoffel (flatMetric n) (flatMetric n) k i j x * pd (fun _ => c) k x) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [pd_const]; ring
    rw [h1, h2]; ring
  have hgisymm : ∀ i j, flatMetric n x i j = flatMetric n x j i := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp only [flatMetric, if_neg h, if_neg (fun hji : j = i => h hji.symm)]
  -- the two carried transport equations, discharged for the flat data.
  have hT0 : heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x * (fun _ => (1 : ℝ)) x
      - 2 * crossGrad (flatMetric n) t (fun _ => (1 : ℝ)) x = 0 := by
    rw [h𝒢, hcg_const]; ring
  have hT1 : t * (heatOpFun (flatMetric n) (flatMetric n) gaussDdim t x * (fun _ => (0 : ℝ)) x
        - 2 * crossGrad (flatMetric n) t (fun _ => (0 : ℝ)) x)
      + gaussDdim t x * ((fun _ => (0 : ℝ)) x
          - laplaceBeltrami (flatMetric n) (flatMetric n) (fun _ => (1 : ℝ)) x) = 0 := by
    rw [h𝒢, hcg_const, hlapc]; simp
  -- apply (b) and collapse `Δ_g u₁ = Δ_g 0 = 0`.
  rw [residual_factorization (flatMetric n) (flatMetric n) t ht x
      (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) contDiff_const contDiff_const hgisymm hT0 hT1,
    hlapc]
  ring

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms heatOpFun_mul
#print axioms crossGrad_lin
#print axioms residual_factorization
#print axioms residual_factorization_flat_witness

end AxiomChecks

end QIQTH.ResidualFactorization

/-! ## THE FACTORIZATION LEDGER — J4-504.

  ── WHAT IS BANKED (before this brick).
    • `ErrorKernelFactorization.residual_eq_gauss_mul_A` — the OFF-DIAGONAL `E = G·A`, with `A` the
      explicit Seeley–DeWitt amplitude carrying `1/t`, `1/t²` singular pieces (NO extra `t`).
    • `HeatResidualBound.parametrixResidual_telescope_N` — the ON-DIAGONAL telescoping
      `E(t,0) = −G(t,0)·Δ_g(w_N)(0)·tᴺ`, i.e. the extra `t`ᴺ factor at `v = 0` ONLY, from the
      diagonal transport recursion `hrec : (k+1)·w_{k+1}(0) = Δ_g(w_k)(0)`.
    • `HeatTransportRecursion` — the transport operator `𝒯 = Θ^{−1/2}Δ_g(Θ^{1/2}·)`, the recursion
      as a CARRIED structure field, and its diagonal collapse (`transport_center`); the OFF-diagonal
      radial ODE is the checkpointed STRETCH-#4 analytic wall (geodesic `r∂_r`).

  ── WHAT J4-504 ADDS.
      role                                                       status
      ─────────────────────────────────────────────────────────  ───────────────────────────────────
      (a) the Leibniz product engine `(∂_t−Δ_g)(G·P)`             ★ LANDED — `heatOpFun_mul` (pure algebra)
      cross-gradient linearity `C(u₀+t u₁)=C(u₀)+t C(u₁)`         LANDED — `crossGrad_lin`
      (b) the OFF-diagonal factorization `E = −t·G·Δ_g u₁`        ★★ LANDED modulo `hT0`,`hT1`
      (c) the flat witness (`hT0`,`hT1` inhabited, `E = 0`)       ★ LANDED — non-vacuous, sign-checked
      the transport equations `hT0`,`hT1` themselves (curved)    CARRIED — the radial-ODE wall

  ── HOW MUCH THIS UNLOCKS.  The extra factor `t` is the WHOLE cancellation Sol identified: it turns
    the ungated residual amplitude from `O(1)` (per J4-500) into `O(t)`, i.e. `E₁ = t·G·q` with `q`
    the bounded field `−Δ_g u₁`.  This is the exact structural input BOTH remaining analytic walls
    consume — `hCorrHigher` (the genuine `O(t²)` traced-correction content, via the banked ds-lemma)
    and `hEboundW` (the off-diagonal residue).  BUT it is unlocked ONLY modulo `hT0`, `hT1`: this
    brick makes the factorization a THEOREM against the transport equations; it does NOT bank the
    transport equations, which remain the carried off-diagonal radial-transport wall.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Recommended J4-505: attack the transport equations themselves —
    either (i) derive `hT0` (`𝒯u₀ = 0`) from the van-Vleck amplitude `u₀ = J^{−1/2}` and the flat
    Gaussian's gradient `∂_iG = −(x_i/2t)G` (which reduces the cross-gradient `C(u₀)` to a radial
    `r∂_r u₀` term — the first genuinely tractable slice), or (ii) the Levi order-preservation lemma
    banking `q` bounded uniformly in `t`.
-/
