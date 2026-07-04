/-
  THE SEPARATION S1–S2 (THE_SEPARATION_PLAN.md) — the RIGHT-multiplication GNS bound.

  S1 — the √ρ-conjugation factorization (binding verdict A1): the WEIGHT EXCHANGE
  `w_K(m)·w_C(n̂) = w_K(n)·w_C(m̂)` for configurations agreeing off the sub-corner (dropped
  out of T7's `kappaOf_gibbsWeight_of_sameOffSub`), its √-version, the diagonal square root
  `sqrtGibbs` of the Gibbs density (`S·S = ρ`, `Sᴴ = S`), its inverse `sqrtInvGibbs`, the
  conjugated element `rightConj a = S₀⁻¹·a·S₀`, and the weighted Frobenius constant
  `rightFrobBound a := frobNormSq((rightConj a)ᴴ)`.

  S2 — THE ENGINE E1 `ι(a)·S_K = S_K·ι(rightConj a)` (the one new entrywise lemma — the
  sameOffSub case is exactly the √-weight-exchange), the Loewner gap
  `c(a)•ρ_K − ι(a)·ρ_K·ι(a)ᴴ = S·ι(c•1 − â·âᴴ)·S ⪰ 0` (frobBound at `(rightConj a)ᴴ` +
  `cornerEmbed_posSemidef` + the PSD sandwich), and the scalar CAPSTONE
  `gnsInner_rightMul_le`: RIGHT multiplication by the embedded corner element is BOUNDED on
  the stage-K GNS form with the weighted Frobenius constant.

  HONEST SCOPE: the constant is a WEIGHTED Frobenius (Hilbert–Schmidt) constant
  `Σ ‖a n m‖²·(w_m/w_n)`, NOT the C*-norm — the right action is proved BOUNDED, never
  claimed contractive; no ⋆-anti-representation law is stated.
-/
import Mathlib
import QIQTH.TowerGNS.StageBound
import QIQTH.TowerGNS.Germ

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### S1 — the weight exchange -/

/-- **THE WEIGHT EXCHANGE** (ℝ-level): for big-corner configurations `m, n` agreeing off the
    sub-corner `C`, the Gibbs weights satisfy `w_K(m)·w_C(n̂) = w_K(n)·w_C(m̂)` — rearrange
    T7's kappaOf eigen-law `log w_K(m) − log w_K(n) = log w_C(m̂) − log w_C(n̂)` and cancel
    the logarithms on the positive reals. -/
theorem gibbsWeight_exchange {C K : Finset M} (h : C ⊆ K) {m n : Micro L K}
    (hs : sameOffSub L C K m n) :
    gibbsWeight L K ω β m * gibbsWeight L C ω β (restrictMicro L K C h n)
      = gibbsWeight L K ω β n * gibbsWeight L C ω β (restrictMicro L K C h m) := by
  have hk := kappaOf_gibbsWeight_of_sameOffSub L C K h ω β hs
  rw [QIQTH.TypeIITrace.kappaOf, QIQTH.TypeIITrace.kappaOf] at hk
  have hlog : Real.log (gibbsWeight L K ω β m
        * gibbsWeight L C ω β (restrictMicro L K C h n))
      = Real.log (gibbsWeight L K ω β n
        * gibbsWeight L C ω β (restrictMicro L K C h m)) := by
    rw [Real.log_mul (gibbsWeight_pos L K ω β m).ne' (gibbsWeight_pos L C ω β _).ne',
      Real.log_mul (gibbsWeight_pos L K ω β n).ne' (gibbsWeight_pos L C ω β _).ne']
    linarith [hk]
  exact Real.log_injOn_pos
    (Set.mem_Ioi.mpr (mul_pos (gibbsWeight_pos L K ω β m) (gibbsWeight_pos L C ω β _)))
    (Set.mem_Ioi.mpr (mul_pos (gibbsWeight_pos L K ω β n) (gibbsWeight_pos L C ω β _)))
    hlog

/-- The √-version of the weight exchange: `√w_K(m)·√w_C(n̂) = √w_K(n)·√w_C(m̂)`. -/
theorem sqrt_gibbsWeight_exchange {C K : Finset M} (h : C ⊆ K) {m n : Micro L K}
    (hs : sameOffSub L C K m n) :
    Real.sqrt (gibbsWeight L K ω β m)
        * Real.sqrt (gibbsWeight L C ω β (restrictMicro L K C h n))
      = Real.sqrt (gibbsWeight L K ω β n)
        * Real.sqrt (gibbsWeight L C ω β (restrictMicro L K C h m)) := by
  rw [← Real.sqrt_mul (gibbsWeight_pos L K ω β m).le,
    ← Real.sqrt_mul (gibbsWeight_pos L K ω β n).le,
    gibbsWeight_exchange L ω β h hs]

/-! ### S1 — the diagonal square root of the Gibbs density -/

/-- **The diagonal square root** `S_K := diag(√w_K)` of the Gibbs density: `S·S = ρ_K`,
    `Sᴴ = S`. -/
noncomputable def sqrtGibbs (K : Finset M) : DiamondAlg L K :=
  Matrix.diagonal fun m => ((Real.sqrt (gibbsWeight L K ω β m) : ℝ) : ℂ)

/-- `S_K · S_K = ρ_K` — the square root property. -/
theorem sqrtGibbs_mul_self (K : Finset M) :
    sqrtGibbs L ω β K * sqrtGibbs L ω β K = gibbsDensity L K ω β := by
  rw [sqrtGibbs, gibbsDensity, Matrix.diagonal_mul_diagonal]
  congr 1
  funext m
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (gibbsWeight_pos L K ω β m).le]

omit [DecidableEq M] in
/-- `S_Kᴴ = S_K` — the square root is self-adjoint (real diagonal). -/
theorem sqrtGibbs_conjTranspose (K : Finset M) :
    (sqrtGibbs L ω β K)ᴴ = sqrtGibbs L ω β K := by
  rw [sqrtGibbs, Matrix.diagonal_conjTranspose]
  congr 1
  funext m
  simp [Complex.conj_ofReal]

/-- The square roots of the Gibbs weights are nonzero. -/
theorem sqrt_gibbsWeight_ne_zero (K : Finset M) (m : Micro L K) :
    Real.sqrt (gibbsWeight L K ω β m) ≠ 0 :=
  (Real.sqrt_pos.mpr (gibbsWeight_pos L K ω β m)).ne'

/-- **The inverse square root** `S_K⁻¹ := diag((√w_K)⁻¹)` (explicit diagonal — no matrix
    inversion). -/
noncomputable def sqrtInvGibbs (K : Finset M) : DiamondAlg L K :=
  Matrix.diagonal fun m => (((Real.sqrt (gibbsWeight L K ω β m))⁻¹ : ℝ) : ℂ)

/-- `S_K⁻¹ · S_K = 1`. -/
theorem sqrtInvGibbs_mul_sqrtGibbs (K : Finset M) :
    sqrtInvGibbs L ω β K * sqrtGibbs L ω β K = 1 := by
  rw [sqrtInvGibbs, sqrtGibbs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext m
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sqrt_gibbsWeight_ne_zero L ω β K m),
    Complex.ofReal_one]

/-- `S_K · S_K⁻¹ = 1`. -/
theorem sqrtGibbs_mul_sqrtInvGibbs (K : Finset M) :
    sqrtGibbs L ω β K * sqrtInvGibbs L ω β K = 1 := by
  rw [sqrtInvGibbs, sqrtGibbs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext m
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sqrt_gibbsWeight_ne_zero L ω β K m),
    Complex.ofReal_one]

/-! ### S1 — the conjugated element and the weighted Frobenius constant -/

/-- **The √ρ-conjugation** `â := S₀⁻¹·a·S₀` — the corner element the right action factors
    through (binding verdict A1). -/
noncomputable def rightConj (C₀ : Finset M) (a : DiamondAlg L C₀) : DiamondAlg L C₀ :=
  sqrtInvGibbs L ω β C₀ * a * sqrtGibbs L ω β C₀

/-- Entrywise: `(rightConj a)(m,n) = (√w_m)⁻¹ · a(m,n) · √w_n`. -/
theorem rightConj_apply (C₀ : Finset M) (a : DiamondAlg L C₀) (m n : Micro L C₀) :
    rightConj L ω β C₀ a m n
      = (((Real.sqrt (gibbsWeight L C₀ ω β m))⁻¹ : ℝ) : ℂ) * a m n
        * ((Real.sqrt (gibbsWeight L C₀ ω β n) : ℝ) : ℂ) := by
  rw [rightConj, sqrtInvGibbs, sqrtGibbs, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **The weighted Frobenius constant** `c(a) := frobNormSq((rightConj a)ᴴ)`
    (`= Σ_{n,m} ‖a n m‖²·(w_m/w_n)`) — the boundedness constant of the RIGHT action
    (weighted Hilbert–Schmidt, NOT the C*-norm; never claimed contractive). -/
noncomputable def rightFrobBound (C₀ : Finset M) (a : DiamondAlg L C₀) : ℝ :=
  frobNormSq L C₀ ((rightConj L ω β C₀ a)ᴴ)

/-- The weighted Frobenius constant is nonnegative. -/
theorem rightFrobBound_nonneg (C₀ : Finset M) (a : DiamondAlg L C₀) :
    0 ≤ rightFrobBound L ω β C₀ a :=
  frobNormSq_nonneg L C₀ _

/-! ### S2 — THE ENGINE E1 -/

/-- **THE ENGINE E1**: `ι(a)·S_K = S_K·ι(rightConj a)` — the embedded corner element slides
    past the square-rooted Gibbs density at the price of the √ρ-conjugation. Entrywise the
    `sameOffSub` case is EXACTLY the √-weight-exchange. -/
theorem cornerEmbed_mul_sqrtGibbs {C₀ K : Finset M} (h : C₀ ⊆ K) (a : DiamondAlg L C₀) :
    cornerEmbed L C₀ K h a * sqrtGibbs L ω β K
      = sqrtGibbs L ω β K * cornerEmbed L C₀ K h (rightConj L ω β C₀ a) := by
  ext m n
  rw [sqrtGibbs, Matrix.mul_diagonal, Matrix.diagonal_mul, cornerEmbed_apply,
    cornerEmbed_apply]
  by_cases hs : sameOffSub L C₀ K m n
  · rw [if_pos hs, if_pos hs, rightConj_apply]
    -- the ℝ-scalar identity first (failure-mode-1 mitigation), then cast and ring
    have hreal : Real.sqrt (gibbsWeight L K ω β n)
        = Real.sqrt (gibbsWeight L K ω β m)
          * (Real.sqrt (gibbsWeight L C₀ ω β (restrictMicro L K C₀ h m)))⁻¹
          * Real.sqrt (gibbsWeight L C₀ ω β (restrictMicro L K C₀ h n)) := by
      have hex := sqrt_gibbsWeight_exchange L ω β h hs
      field_simp [sqrt_gibbsWeight_ne_zero L ω β C₀ (restrictMicro L K C₀ h m)]
      linear_combination hex.symm
    have hC : ((Real.sqrt (gibbsWeight L K ω β n) : ℝ) : ℂ)
        = ((Real.sqrt (gibbsWeight L K ω β m) : ℝ) : ℂ)
          * (((Real.sqrt (gibbsWeight L C₀ ω β (restrictMicro L K C₀ h m)))⁻¹ : ℝ) : ℂ)
          * ((Real.sqrt (gibbsWeight L C₀ ω β (restrictMicro L K C₀ h n)) : ℝ) : ℂ) := by
      exact_mod_cast congrArg Complex.ofReal hreal
    rw [hC]
    ring
  · rw [if_neg hs, if_neg hs, zero_mul, mul_zero]

/-! ### S2 — the Loewner gap -/

/-- **The PSD gap**: `c(a)•ρ_K − ι(a)·ρ_K·ι(a)ᴴ ⪰ 0` — factor `ρ_K = S·S`, slide `ι(a)`
    past `S` by E1, and the gap becomes the sandwich `S·ι(c•1 − â·âᴴ)·S` of the embedded
    Frobenius gap (frobBound applied to `(rightConj a)ᴴ`). -/
theorem rightMul_gap_posSemidef {C₀ K : Finset M} (h : C₀ ⊆ K) (a : DiamondAlg L C₀) :
    (((rightFrobBound L ω β C₀ a : ℝ) : ℂ) • gibbsDensity L K ω β
      - cornerEmbed L C₀ K h a * gibbsDensity L K ω β
        * (cornerEmbed L C₀ K h a)ᴴ).PosSemidef := by
  unfold rightFrobBound
  -- the inner gap `c•1 − â·âᴴ` is PSD — frobBound at `(rightConj a)ᴴ`
  have hinner := frobBound L C₀ ((rightConj L ω β C₀ a)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose] at hinner
  -- embed it
  have hembed := cornerEmbed_posSemidef L h hinner
  rw [cornerEmbed_sub, cornerEmbed_smul, cornerEmbed_one, cornerEmbed_mul,
    cornerEmbed_star] at hembed
  -- sandwich by S (self-adjoint)
  have hsand := hembed.mul_mul_conjTranspose_same (sqrtGibbs L ω β K)
  rw [sqrtGibbs_conjTranspose] at hsand
  -- the sandwich EQUALS the gap
  have hswap : sqrtGibbs L ω β K * cornerEmbed L C₀ K h (rightConj L ω β C₀ a)
      = cornerEmbed L C₀ K h a * sqrtGibbs L ω β K :=
    (cornerEmbed_mul_sqrtGibbs L ω β h a).symm
  have hswapH : (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ * sqrtGibbs L ω β K
      = sqrtGibbs L ω β K * (cornerEmbed L C₀ K h a)ᴴ := by
    calc (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ * sqrtGibbs L ω β K
        = (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ * (sqrtGibbs L ω β K)ᴴ := by
          rw [sqrtGibbs_conjTranspose]
      _ = (sqrtGibbs L ω β K * cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ :=
          (Matrix.conjTranspose_mul _ _).symm
      _ = (cornerEmbed L C₀ K h a * sqrtGibbs L ω β K)ᴴ := by rw [hswap]
      _ = (sqrtGibbs L ω β K)ᴴ * (cornerEmbed L C₀ K h a)ᴴ := Matrix.conjTranspose_mul _ _
      _ = sqrtGibbs L ω β K * (cornerEmbed L C₀ K h a)ᴴ := by rw [sqrtGibbs_conjTranspose]
  have hprod : sqrtGibbs L ω β K
        * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a)
            * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ)
        * sqrtGibbs L ω β K
      = cornerEmbed L C₀ K h a * gibbsDensity L K ω β * (cornerEmbed L C₀ K h a)ᴴ := by
    calc sqrtGibbs L ω β K
          * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a)
              * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ)
          * sqrtGibbs L ω β K
        = (sqrtGibbs L ω β K * cornerEmbed L C₀ K h (rightConj L ω β C₀ a))
            * ((cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ * sqrtGibbs L ω β K) := by
          simp only [Matrix.mul_assoc]
      _ = (cornerEmbed L C₀ K h a * sqrtGibbs L ω β K)
            * (sqrtGibbs L ω β K * (cornerEmbed L C₀ K h a)ᴴ) := by
          rw [hswap, hswapH]
      _ = cornerEmbed L C₀ K h a * (sqrtGibbs L ω β K * sqrtGibbs L ω β K)
            * (cornerEmbed L C₀ K h a)ᴴ := by simp only [Matrix.mul_assoc]
      _ = cornerEmbed L C₀ K h a * gibbsDensity L K ω β
            * (cornerEmbed L C₀ K h a)ᴴ := by rw [sqrtGibbs_mul_self]
  have hkey : sqrtGibbs L ω β K
        * (((frobNormSq L C₀ ((rightConj L ω β C₀ a)ᴴ) : ℝ) : ℂ) • (1 : DiamondAlg L K)
            - cornerEmbed L C₀ K h (rightConj L ω β C₀ a)
              * (cornerEmbed L C₀ K h (rightConj L ω β C₀ a))ᴴ)
        * sqrtGibbs L ω β K
      = ((frobNormSq L C₀ ((rightConj L ω β C₀ a)ᴴ) : ℝ) : ℂ) • gibbsDensity L K ω β
        - cornerEmbed L C₀ K h a * gibbsDensity L K ω β * (cornerEmbed L C₀ K h a)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm, smul_mul_assoc, Matrix.mul_one,
      sqrtGibbs_mul_self, hprod]
  rwa [hkey] at hsand

/-! ### S2 — the scalar capstone -/

/-- **S2 CAPSTONE — the GNS boundedness of the RIGHT action**: right multiplication by the
    embedded corner element `ι a` is bounded on the stage-`K` GNS form with the WEIGHTED
    Frobenius constant: `⟪x·ιa, x·ιa⟫_K ≤ rightFrobBound a · ⟪x, x⟫_K`. (Weighted
    Hilbert–Schmidt bound, NOT the C*-norm — never claimed contractive.) -/
theorem gnsInner_rightMul_le (C₀ K : Finset M) (h : C₀ ⊆ K) (a : DiamondAlg L C₀)
    (x : DiamondAlg L K) :
    RCLike.re (gnsInner L ω β K (x * cornerEmbed L C₀ K h a) (x * cornerEmbed L C₀ K h a))
      ≤ rightFrobBound L ω β C₀ a * RCLike.re (gnsInner L ω β K x x) := by
  -- the gap sandwiched by x is PSD, so its trace is nonnegative
  have hgap := rightMul_gap_posSemidef L ω β h a
  have h0 := (hgap.mul_mul_conjTranspose_same x).trace_nonneg
  -- rewrite the sandwich as `c•(xρxᴴ) − (x·ιa)ρ(x·ιa)ᴴ`
  have hexpand : x * (((rightFrobBound L ω β C₀ a : ℝ) : ℂ) • gibbsDensity L K ω β
        - cornerEmbed L C₀ K h a * gibbsDensity L K ω β * (cornerEmbed L C₀ K h a)ᴴ) * xᴴ
      = ((rightFrobBound L ω β C₀ a : ℝ) : ℂ) • (x * gibbsDensity L K ω β * xᴴ)
        - x * cornerEmbed L C₀ K h a * gibbsDensity L K ω β
          * (x * cornerEmbed L C₀ K h a)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, mul_smul_comm,
      smul_mul_assoc, Matrix.mul_assoc]
  rw [hexpand, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at h0
  -- both GNS values are the cycled traces
  have hcycle1 : gnsInner L ω β K x x
      = Matrix.trace (x * gibbsDensity L K ω β * xᴴ) := by
    rw [gnsInner_def, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have hcycle2 : gnsInner L ω β K (x * cornerEmbed L C₀ K h a)
        (x * cornerEmbed L C₀ K h a)
      = Matrix.trace (x * cornerEmbed L C₀ K h a * gibbsDensity L K ω β
          * (x * cornerEmbed L C₀ K h a)ᴴ) := by
    rw [gnsInner_def, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  -- pass to real parts
  have hre := (Complex.le_def.mp h0).1
  rw [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul] at hre
  rw [hcycle1, hcycle2, RCLike.re_to_complex, RCLike.re_to_complex]
  linarith

/-! ### S3 — the raw right pre-operator (the R6 mirror, product reversed) -/

/-- **The raw right-multiplication pre-operator**: the component at stage `C` is embedded into
    `C₀ ⊔ C` and multiplied on the RIGHT by the embedded `a` — the commutant-side action of the
    corner element `a`, at the raw direct sum. -/
noncomputable def rightMulRaw (C₀ : Finset M) (a : DiamondAlg L C₀) :
    (⨁ C : Finset M, DiamondAlg L C) →ₗ[ℂ] (⨁ C : Finset M, DiamondAlg L C) :=
  DirectSum.toModule ℂ (Finset M) (⨁ C : Finset M, DiamondAlg L C) fun C =>
    (DirectSum.lof ℂ (Finset M) (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)) ∘ₗ
      (LinearMap.mulRight ℂ (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a)) ∘ₗ
        (cornerEmbedₗ L C (C₀ ⊔ C) Finset.subset_union_right)

@[simp] theorem rightMulRaw_of (C₀ : Finset M) (a : DiamondAlg L C₀) (C : Finset M)
    (x : DiamondAlg L C) :
    rightMulRaw L C₀ a (DirectSum.of _ C x)
      = DirectSum.of (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)
          (cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right x
            * cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a) := by
  rw [← DirectSum.lof_eq_of ℂ, rightMulRaw]
  erw [DirectSum.toModule_lof]
  rfl

/-! ### S3 — collapse compatibility -/

/-- **The collapse of the image**: collapsing `rightMulRaw a x` at the stage `C₀ ⊔ K` is RIGHT
    multiplication by the embedded `a` after collapsing `x` there — the pre-operator is the
    honest right multiplication in every sufficiently large corner. -/
theorem collapse_rightMul (C₀ : Finset M) (a : DiamondAlg L C₀) (K : Finset M)
    (x : ⨁ C : Finset M, DiamondAlg L C) (hx : ∀ C, x C ≠ 0 → C ⊆ K) :
    collapseRaw L (C₀ ⊔ K) (rightMulRaw L C₀ a x)
      = collapseRaw L (C₀ ⊔ K) x
          * cornerEmbed L C₀ (C₀ ⊔ K) Finset.subset_union_left a := by
  classical
  have hxsum : x = ∑ C ∈ DFinsupp.support x, DirectSum.of _ C (x C) :=
    (DirectSum.sum_support_of x).symm
  rw [hxsum]
  rw [map_sum (rightMulRaw L C₀ a) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
  rw [map_sum (collapseRaw L (C₀ ⊔ K))
    (fun C => rightMulRaw L C₀ a (DirectSum.of _ C (x C))) (DFinsupp.support x)]
  rw [map_sum (collapseRaw L (C₀ ⊔ K)) (fun C => DirectSum.of _ C (x C))
    (DFinsupp.support x)]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCK : C ⊆ K := hx C (DFinsupp.mem_support_iff.mp hC)
  have hsub : C₀ ⊔ C ⊆ C₀ ⊔ K := Finset.union_subset_union_right hCK
  have hCsub : C ⊆ C₀ ⊔ K := hCK.trans Finset.subset_union_right
  rw [rightMulRaw_of, collapseRaw_of_le L hsub, collapseRaw_of_le L hCsub,
    cornerEmbed_mul, cornerEmbed_trans L C (C₀ ⊔ C) (C₀ ⊔ K),
    cornerEmbed_trans L C₀ (C₀ ⊔ C) (C₀ ⊔ K)]

/-! ### S3 — the re-inner inequality (S2 fed through the collapse — all raw) -/

/-- **S3 KEY (raw)**: the tower form of the right pre-operator image is dominated by the
    WEIGHTED Frobenius constant times the form of the argument — stage collapse at `C₀ ⊔ K`
    plus S2's GNS boundedness inequality. -/
theorem rightMulRaw_re_inner_le (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    RCLike.re (rawInner L ω β (rightMulRaw L C₀ a x) (rightMulRaw L C₀ a x))
      ≤ rightFrobBound L ω β C₀ a * RCLike.re (rawInner L ω β x x) := by
  classical
  set K : Finset M := (DFinsupp.support x).sup id with hK
  have hx : ∀ C, x C ≠ 0 → C ⊆ K := fun C hC =>
    Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hC)
  have hxK : ∀ C, x C ≠ 0 → C ⊆ C₀ ⊔ K := fun C hC =>
    (hx C hC).trans Finset.subset_union_right
  -- the image is supported under `C₀ ⊔ K`
  have hTx : rightMulRaw L C₀ a x
      = ∑ C ∈ DFinsupp.support x,
          DirectSum.of (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)
            (cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right (x C)
              * cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a) := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    rw [map_sum (rightMulRaw L C₀ a) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
    exact Finset.sum_congr rfl fun C _ => rightMulRaw_of L C₀ a C (x C)
  have hx' : ∀ C', (rightMulRaw L C₀ a x) C' ≠ 0 → C' ⊆ C₀ ⊔ K := by
    intro C' hC'
    by_contra hnot
    apply hC'
    rw [hTx]
    erw [DFinsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    refine DirectSum.of_eq_of_ne _ _ _ fun he => hnot ?_
    rw [he]
    exact Finset.union_subset_union_right (hx C (DFinsupp.mem_support_iff.mp hC))
  rw [rawInner_eq_collapse L ω β (C₀ ⊔ K) _ _ hx' hx',
    rawInner_eq_collapse L ω β (C₀ ⊔ K) x x hxK hxK,
    collapse_rightMul L C₀ a K x hx]
  exact gnsInner_rightMul_le L ω β C₀ (C₀ ⊔ K) Finset.subset_union_left a
    (collapseRaw L (C₀ ⊔ K) x)

/-! ### S3 — the synonym wrappers (application-position defeq only — the R3 lesson) -/

/-- The right pre-operator at the synonym, as a plain linear map (fields delegate to the raw
    map by definitional equality). -/
noncomputable def towerRightMulₗ (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerPre L ω β →ₗ[ℂ] TowerPre L ω β where
  toFun x := rightMulRaw L C₀ a x
  map_add' x y := (rightMulRaw L C₀ a).map_add x y
  map_smul' r x := (rightMulRaw L C₀ a).map_smul r x

@[simp] theorem towerRightMulₗ_apply (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : TowerPre L ω β) :
    towerRightMulₗ L ω β C₀ a x = rightMulRaw L C₀ a x := rfl

/-- **S3 — the norm bound**: the right pre-operator is bounded on the tower seminorm with the
    WEIGHTED Frobenius constant of S2 — `‖x · ι(a)‖ ≤ √(rightFrobBound a) · ‖x‖`. (Weighted
    Hilbert–Schmidt bound, NOT the C*-norm — bounded, never claimed contractive.) -/
theorem rightMulRaw_norm_le (C₀ : Finset M) (a : DiamondAlg L C₀) (x : TowerPre L ω β) :
    ‖towerRightMulₗ L ω β C₀ a x‖ ≤ Real.sqrt (rightFrobBound L ω β C₀ a) * ‖x‖ := by
  have key := rightMulRaw_re_inner_le L ω β C₀ a x
  have hsq : ‖towerRightMulₗ L ω β C₀ a x‖ ^ 2 ≤ rightFrobBound L ω β C₀ a * ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (towerRightMulₗ L ω β C₀ a x),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) x]
    exact key
  calc ‖towerRightMulₗ L ω β C₀ a x‖
      = Real.sqrt (‖towerRightMulₗ L ω β C₀ a x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (rightFrobBound L ω β C₀ a * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (rightFrobBound L ω β C₀ a) * Real.sqrt (‖x‖ ^ 2) :=
        Real.sqrt_mul (rightFrobBound_nonneg L ω β C₀ a) _
    _ = Real.sqrt (rightFrobBound L ω β C₀ a) * ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

/-- **S3 CAPSTONE — the bounded right pre-operator**: right multiplication by the corner
    element `a` as a CONTINUOUS linear map on the tower pre-space, with the weighted Frobenius
    constant `√(rightFrobBound a)` (bounded, never claimed contractive). S4 extends it to the
    completion. -/
noncomputable def towerRightMul (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerPre L ω β →L[ℂ] TowerPre L ω β :=
  LinearMap.mkContinuous (towerRightMulₗ L ω β C₀ a)
    (Real.sqrt (rightFrobBound L ω β C₀ a))
    fun x => rightMulRaw_norm_le L ω β C₀ a x

@[simp] theorem towerRightMul_apply (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : TowerPre L ω β) :
    towerRightMul L ω β C₀ a x = rightMulRaw L C₀ a x := rfl

/-! ### S4 — the completion operator and its action on the cyclic vector -/

/-- **S4 — the right-multiplication operator on the tower Hilbert space**: the bounded right
    pre-operator of S3, lifted to the completion by `ContinuousLinearMap.completion` — the
    R7 recipe, mirrored. -/
noncomputable def towerRightMulCLM (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  (towerRightMul L ω β C₀ a).completion

@[simp] theorem towerRightMulCLM_coe (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : TowerPre L ω β) :
    towerRightMulCLM L ω β C₀ a (x : TowerGNS L ω β)
      = ((towerRightMul L ω β C₀ a x : TowerPre L ω β) : TowerGNS L ω β) :=
  (towerRightMul L ω β C₀ a).completion_apply_coe x

/-- **S4 CAPSTONE — R_a Ω = ↑(of C a)**: the right action on the cyclic vector reproduces the
    pure tower component — the R8-head mirror. The pre-level image lands at stage `C ⊔ ∅`
    (propositionally `C`, NOT definitionally); `cornerEmbed_one` + `one_mul` reduce the matrix
    and the germ identity glues the stage — no type-cast across `Finset.union_empty` is ever
    taken. -/
theorem towerRightMul_cyclicVec (C : Finset M) (a : DiamondAlg L C) :
    towerRightMulCLM L ω β C a (towerCyclicVec L ω β)
      = ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β) := by
  rw [towerCyclicVec, towerRightMulCLM_coe]
  have h1 : towerRightMul L ω β C a (towerOf L ω β ∅ 1)
      = towerOf L ω β (C ⊔ ∅) (cornerEmbed L C (C ⊔ ∅) Finset.subset_union_left a) := by
    show rightMulRaw L C a (DirectSum.of (fun C : Finset M => DiamondAlg L C) ∅ 1)
        = DirectSum.of (fun C : Finset M => DiamondAlg L C) (C ⊔ ∅)
            (cornerEmbed L C (C ⊔ ∅) Finset.subset_union_left a)
    rw [rightMulRaw_of, cornerEmbed_one, one_mul]
  rw [h1]
  exact towerGerm L ω β Finset.subset_union_left a

end QIQTH.TowerGNS
