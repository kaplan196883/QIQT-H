/-
  THE RESOLVENT CAMPAIGN — R2 (THE_RESOLVENT_PLAN.md) — **order and spectral bounds of
  the resolvent: self-adjoint, `0 ≤ R ≤ 1`, `σ(R) ⊆ [0,1]`, `RΩ = ½Ω`.**

  R1 delivered `towerResolvent = (1+Δ)⁻¹` as an everywhere-defined CLM contraction with
  the exact identities `Rh + Δ(Rh) = h`, `R(x+Δx) = x`, `Δ∘R = 1−R`. This increment turns
  the SYMMETRY and POSITIVITY of the unbounded Δ (M5) into the ORDER data of the bounded R
  that the spectral tower (R4: `PVM_of_selfAdjoint`/`borelFC`) consumes:

  * SELF-ADJOINTNESS: `⟪Rh, k⟫ = ⟪Rh, Rk + Δ(Rk)⟫ = ⟪Rh, Rk⟫ + ⟪Δ(Rh), Rk⟫ = ⟪h, Rk⟫`
    (one application of `towerModularOp_isFormalAdjoint` in the middle), packaged as
    `IsSelfAdjoint (towerResolvent)` through `isSelfAdjoint_iff_isSymmetric`.
  * `0 ≤ R`: `re ⟪Rh, h⟫ = ‖Rh‖² + ‖S̄(Rh)‖² ≥ 0` (M5.1's `towerModularOp_inner_self` at
    `x := Rh`), packaged as `IsPositive` and as `0 ≤ R` in the Loewner order.
  * `R ≤ 1`: `re ⟪h − Rh, h⟫ = ‖S̄(Rh)‖² + ‖Δ(Rh)‖² ≥ 0` (`h − Rh = Δ(Rh)`), giving
    `0 ≤ 1 − R`; plus the operator-norm bound `‖R‖ ≤ 1` from R1's pointwise contraction.
  * SPECTRUM: `σ(R) ⊆ [0,1]` — the verbatim `rvdRC_spectrum_mem_Icc` port
    (`StarOrderedRing.nonneg_iff_spectrum_nonneg` on `R` and on `1 − R`, with
    `spectrum.singleton_sub_eq` relocating the spectrum of `1 − R`).
  * THE CYCLIC EIGENVECTOR: `RΩ = ½Ω` — `½Ω + Δ(½Ω) = Ω` (from `ΔΩ = Ω`, M5.3), so the
    left-inverse equation R1 evaluates `R(Ω)`. The spectral input for R5's `U_tΩ = Ω`
    (the eigenvalue `½` carries `δ = 1`).

  NOT here (deliberately): the Borel functional calculus and `Δ^{it}` (R4–R6), the PVM
  eigen/atom calculus (R3), Δ^{1/2}, J, KMS, any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.Resolvent

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### R2.1 — symmetry and self-adjointness of the resolvent

    `⟪Rh, k⟫ = ⟪h, Rk⟫`: expand `k = Rk + Δ(Rk)` and `h = Rh + Δ(Rh)` (R1's defining
    equation) and swap Δ across the inner product once (M5.2's formal self-adjointness). -/

/-- **SYMMETRY of the resolvent**: `⟪R h, k⟫ = ⟪h, R k⟫` — expand `k` by the defining
equation, move `Δ` from the `k`-side to the `h`-side (`towerModularOp_isFormalAdjoint` at
the domain elements `⟨Rh, _⟩`, `⟨Rk, _⟩`), and reassemble the defining equation of `h`. -/
theorem towerResolvent_isSymmetric (h k : TowerGNS L ω β) :
    ⟪towerResolvent L ω β h, k⟫_ℂ = ⟪h, towerResolvent L ω β k⟫_ℂ := by
  have h1 : ⟪towerResolvent L ω β h, k⟫_ℂ
      = ⟪towerResolvent L ω β h, towerResolvent L ω β k⟫_ℂ
        + ⟪towerResolvent L ω β h,
            towerModularOp L ω β
              ⟨towerResolvent L ω β k, towerResolvent_mem L ω β k⟩⟫_ℂ := by
    rw [← inner_add_right, towerResolvent_add_modularOp L ω β k]
  have h2 : ⟪towerResolvent L ω β h,
        towerModularOp L ω β
          ⟨towerResolvent L ω β k, towerResolvent_mem L ω β k⟩⟫_ℂ
      = ⟪towerModularOp L ω β
            ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
          towerResolvent L ω β k⟫_ℂ :=
    (towerModularOp_isFormalAdjoint L ω β
      ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩
      ⟨towerResolvent L ω β k, towerResolvent_mem L ω β k⟩).symm
  have h3 : ⟪h, towerResolvent L ω β k⟫_ℂ
      = ⟪towerResolvent L ω β h, towerResolvent L ω β k⟫_ℂ
        + ⟪towerModularOp L ω β
              ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
            towerResolvent L ω β k⟫_ℂ := by
    rw [← inner_add_left, towerResolvent_add_modularOp L ω β h]
  rw [h1, h2, ← h3]

/-- **★ THE RESOLVENT IS SELF-ADJOINT ★** — `star R = R` as a continuous linear map
(the `IsSelfAdjoint` the spectral tower's `PVM_of_selfAdjoint` consumes in R4), from the
symmetry through `isSelfAdjoint_iff_isSymmetric`. -/
theorem towerResolvent_isSelfAdjoint : IsSelfAdjoint (towerResolvent L ω β) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun h k =>
    towerResolvent_isSymmetric L ω β h k

/-! ### R2.2 — positivity: `0 ≤ R`

    `⟪Rh, h⟫ = ⟪Rh, Rh + Δ(Rh)⟫ = ‖Rh‖² + ⟪Rh, Δ(Rh)⟫`, and `⟪Rh, Δ(Rh)⟫` is the
    conjugate of M5.1's `⟪Δx, x⟫ = ‖S̄x‖²` — real, so the real part is a sum of squares. -/

/-- **POSITIVITY of the resolvent, exact form**: `re ⟪R h, h⟫ = ‖Rh‖² + ‖S̄(Rh)‖² ≥ 0` —
expand `h` by the defining equation and evaluate the Δ-term through M5.1's positivity
(`⟪Δx, x⟫ = ‖S̄x‖²`, conjugated to the `⟪x, Δx⟫` orientation; real, so conjugation-free). -/
theorem towerResolvent_inner_self_nonneg (h : TowerGNS L ω β) :
    0 ≤ RCLike.re ⟪towerResolvent L ω β h, h⟫_ℂ := by
  have hx := mem_bar_of_mem_towerModularDom L ω β (towerResolvent_mem L ω β h)
  have hF := barF_of_mem_towerModularDom L ω β (towerResolvent_mem L ω β h) hx
  have hDelta : ⟪towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
      towerResolvent L ω β h⟫_ℂ
      = (‖towerTomitaBar L ω β ⟨towerResolvent L ω β h, hx⟩‖ : ℂ) ^ 2 :=
    towerModularOp_inner_self L ω β hx hF
  have hswap : ⟪towerResolvent L ω β h,
      towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩⟫_ℂ
      = (‖towerTomitaBar L ω β ⟨towerResolvent L ω β h, hx⟩‖ : ℂ) ^ 2 := by
    rw [← inner_conj_symm, hDelta, map_pow, Complex.conj_ofReal]
  have hRR : ⟪towerResolvent L ω β h, towerResolvent L ω β h⟫_ℂ
      = (‖towerResolvent L ω β h‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have hsplit : ⟪towerResolvent L ω β h, h⟫_ℂ
      = ⟪towerResolvent L ω β h, towerResolvent L ω β h⟫_ℂ
        + ⟪towerResolvent L ω β h,
            towerModularOp L ω β
              ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩⟫_ℂ := by
    rw [← inner_add_right, towerResolvent_add_modularOp L ω β h]
  rw [hsplit, hRR, hswap, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, RCLike.re_to_complex, Complex.ofReal_re]
  positivity

/-- **`R` IS POSITIVE** (Mathlib packaging): symmetric with `0 ≤ re ⟪Rh, h⟫` — the form
the Loewner order and `StarOrderedRing.nonneg_iff_spectrum_nonneg` consume. -/
theorem towerResolvent_isPositive : (towerResolvent L ω β).IsPositive :=
  ⟨(towerResolvent_isSelfAdjoint L ω β).isSymmetric, fun h => by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact towerResolvent_inner_self_nonneg L ω β h⟩

/-- **`0 ≤ R` in the Loewner order** — the exact hypothesis of the lower spectral bound. -/
theorem towerResolvent_nonneg : 0 ≤ towerResolvent L ω β :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (towerResolvent_isPositive L ω β)

/-! ### R2.3 — the upper bound: `R ≤ 1`

    `h − Rh = Δ(Rh)` (R1's `Δ∘R = 1−R`), so
    `⟪h − Rh, h⟫ = ⟪Δ(Rh), Rh + Δ(Rh)⟫ = ‖S̄(Rh)‖² + ‖Δ(Rh)‖²` — again a sum of squares. -/

/-- **THE UPPER BOUND, exact form**: `re ⟪h − Rh, h⟫ = ‖S̄(Rh)‖² + ‖Δ(Rh)‖² ≥ 0` —
`h − Rh = Δ(Rh)` and the defining equation split `⟪Δ(Rh), h⟫` into M5.1's positivity term
and a norm square. -/
theorem one_sub_towerResolvent_inner_self_nonneg (h : TowerGNS L ω β) :
    0 ≤ RCLike.re ⟪h - towerResolvent L ω β h, h⟫_ℂ := by
  have hx := mem_bar_of_mem_towerModularDom L ω β (towerResolvent_mem L ω β h)
  have hF := barF_of_mem_towerModularDom L ω β (towerResolvent_mem L ω β h) hx
  have hDelta : ⟪towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
      towerResolvent L ω β h⟫_ℂ
      = (‖towerTomitaBar L ω β ⟨towerResolvent L ω β h, hx⟩‖ : ℂ) ^ 2 :=
    towerModularOp_inner_self L ω β hx hF
  have hDD : ⟪towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
      towerModularOp L ω β
        ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩⟫_ℂ
      = (‖towerModularOp L ω β
          ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K _
  have hsplit : ⟪h - towerResolvent L ω β h, h⟫_ℂ
      = ⟪towerModularOp L ω β
            ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
          towerResolvent L ω β h⟫_ℂ
        + ⟪towerModularOp L ω β
              ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩,
            towerModularOp L ω β
              ⟨towerResolvent L ω β h, towerResolvent_mem L ω β h⟩⟫_ℂ := by
    rw [← inner_add_right, towerResolvent_add_modularOp L ω β h,
      modularOp_towerResolvent L ω β h]
  rw [hsplit, hDelta, hDD, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_add, RCLike.re_to_complex, Complex.ofReal_re]
  positivity

/-- `1 − R` is self-adjoint (`1` and `R` both are). -/
theorem one_sub_towerResolvent_isSelfAdjoint :
    IsSelfAdjoint
      ((1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β) :=
  (IsSelfAdjoint.one (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)).sub
    (towerResolvent_isSelfAdjoint L ω β)

/-- **`1 − R` IS POSITIVE** — the upper-bound half in Mathlib packaging. -/
theorem one_sub_towerResolvent_isPositive :
    ((1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β).IsPositive :=
  ⟨(one_sub_towerResolvent_isSelfAdjoint L ω β).isSymmetric, fun h => by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
    exact one_sub_towerResolvent_inner_self_nonneg L ω β h⟩

/-- **`R ≤ 1` in the Loewner order**, stated as `0 ≤ 1 − R` — the exact hypothesis of the
upper spectral bound. -/
theorem one_sub_towerResolvent_nonneg :
    0 ≤ (1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (one_sub_towerResolvent_isPositive L ω β)

/-! ### R2.4 — the operator norm: `‖R‖ ≤ 1` -/

/-- **THE OPERATOR-NORM BOUND**: `‖R‖ ≤ 1` — R1's pointwise contraction
`‖Rh‖ ≤ ‖h‖` through `opNorm_le_bound`. -/
theorem norm_towerResolvent_le_one : ‖towerResolvent L ω β‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
    rw [one_mul]
    exact norm_towerResolvent_apply_le L ω β h

/-! ### R2.5 — the spectrum: `σ(R) ⊆ [0,1]`

    The verbatim `rvdRC_spectrum_mem_Icc` port: lower bound from `0 ≤ R` via
    `StarOrderedRing.nonneg_iff_spectrum_nonneg`; upper bound by relocating —
    `1 − r ∈ {1} − σ(R) = σ(1·1 − R) = σ(1 − R)` (`spectrum.singleton_sub_eq`) and
    `0 ≤ 1 − R` gives `0 ≤ 1 − r`. -/

/-- **★ THE SPECTRUM OF THE RESOLVENT LIES IN `[0,1]` ★** — the spectral location the R4
`borelFC` symbol calculus consumes (the modular symbol `((1−r)/r)^{it}` is defined and
unimodular exactly on `(0,1)`; the junk endpoints are killed in R3/R5). Verbatim port of
`rvdRC_spectrum_mem_Icc` with `1 − R` in place of `2 − R`. -/
theorem towerResolvent_spectrum_mem_Icc (r : spectrum ℝ (towerResolvent L ω β)) :
    (r : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (towerResolvent L ω β)
      (towerResolvent_isSelfAdjoint L ω β)).mp (towerResolvent_nonneg L ω β) r r.2, ?_⟩
  have halg : (algebraMap ℝ (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)) 1
      - towerResolvent L ω β
      = (1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β := by
    rw [map_one]
  have hmem : (1 : ℝ) - (r : ℝ)
      ∈ spectrum ℝ
          ((1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β) := by
    rw [← halg, ← spectrum.singleton_sub_eq]
    exact Set.sub_mem_sub rfl r.2
  have hnn := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ)
      ((1 : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) - towerResolvent L ω β)
      (one_sub_towerResolvent_isSelfAdjoint L ω β)).mp
      (one_sub_towerResolvent_nonneg L ω β) _ hmem
  linarith

/-! ### R2.6 — the cyclic eigenvector: `RΩ = ½Ω`

    `ΔΩ = Ω` (M5.3), so `½Ω + Δ(½Ω) = ½Ω + ½Ω = Ω`; the left-inverse equation R1 then
    evaluates `R(Ω) = ½Ω` — the eigenvalue `½` at which the modular symbol equals
    `((1−½)/½)^{it} = 1` (R5's `U_tΩ = Ω`). -/

/-- **★ `RΩ = ½Ω` ★** — the cyclic vector is an eigenvector of the resolvent with
eigenvalue `½`: apply the left-inverse equation at `x := ½·⟨Ω, _⟩`, whose `(1+Δ)`-image is
`½Ω + ½ΔΩ = Ω` by `LinearPMap.map_smul` and `ΔΩ = Ω`. -/
theorem towerResolvent_cyclicVec :
    towerResolvent L ω β (towerCyclicVec L ω β)
      = (2⁻¹ : ℂ) • towerCyclicVec L ω β := by
  have hsum : (((2⁻¹ : ℂ)
          • (⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩
            : (towerModularOp L ω β).domain) : (towerModularOp L ω β).domain)
          : TowerGNS L ω β)
        + towerModularOp L ω β
            ((2⁻¹ : ℂ)
              • ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩)
      = towerCyclicVec L ω β := by
    rw [LinearPMap.map_smul, towerModularOp_cyclicVec L ω β]
    show (2⁻¹ : ℂ) • towerCyclicVec L ω β + (2⁻¹ : ℂ) • towerCyclicVec L ω β
      = towerCyclicVec L ω β
    rw [← add_smul]
    norm_num
  have hkey := towerResolvent_one_add L ω β
    ((2⁻¹ : ℂ) • ⟨towerCyclicVec L ω β, cyclicVec_mem_towerModularDom L ω β⟩)
  rw [hsum] at hkey
  rw [hkey]
  exact Submodule.coe_smul _ _

end QIQTH.TowerGNS
