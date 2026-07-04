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

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix

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

end QIQTH.TowerGNS
