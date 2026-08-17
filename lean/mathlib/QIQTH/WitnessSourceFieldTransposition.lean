/-
  WitnessSourceFieldTransposition — J4-819: the ABSTRACT source↔field transposition mechanism
  for the second field-partial of a DISPLACEMENT kernel, isolating EXACTLY the obstruction the
  live `hCConv` wall (J4-818) requires.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE WALL (J4-818, verbatim).  The `kPrime`/`gderivInt` bridge differentiates the witness at a FIXED
  field point `x`, integrating over the SOURCE `z`: it needs `∂²_field H(τ; field=x; source=z)`.  The
  closed J4-817 sliver bounds differentiate at the INTEGRATION variable `z`, FIXED source `z₀`: they
  give `∂²_field H(τ; field=z; source=z₀)`.  Even at the center `x=0=z₀` these are TRANSPOSED:
      kPrime  needs   `∂²_firstslot H(τ, 0, z)`   (chart based at source `z`, field derivative at 0),
      sliver  gives   `∂²_firstslot H(τ, z, 0)`   (chart based at source 0, field derivative at `z`).

  ── THE STRUCTURAL FACT (established by grinding `vanVleckGatedWitness`'s definition).  The ENTIRE
  `(p,q)`-dependence of the live witness factors through ONE chart vector `V(q,p) := uniformInverseChart
  g gi hC hK q p`:
      `H(τ,p,q) = radialCutoff a b (V) · gaussDdim τ (V) · vanVleck g (V)^{−1/2} · (u₀(V)+u₁(V)τ)`.
  In the LEADING (flat) chart `V(q,p) = p − q`, `H` is a DISPLACEMENT kernel `H τ p q = F τ (p − q)`.

  ── THE MECHANISM (this file, proved abstractly; the sympy census `docs/qg_roadmap/` confirms it
  numerically).  For a displacement kernel `H p q = F (p − q)` with `F` EVEN (`F (−w) = F w`), the
  center-anchored transposition holds EXACTLY:
      `∂ⱼ∂ᵢ[ x' ↦ F (x' − z) ] |_{x'=0}  =  ∂ⱼ∂ᵢ[ x' ↦ F (x' − 0) ] |_{x'=z}`
  because BOTH sides equal `(∂ⱼ∂ᵢF)` evaluated at `∓z`, and the second partial of an even function is
  even.  This is `displacement_secondPartial_transposition_center` below.

  ── WHAT THIS ISOLATES (the honest ledger).  The sympy census (`transpose.py`) shows the transposition
  difference is carried ENTIRELY by the ODD part of the amplitude `A(w) = vanVleck(w)^{−1/2}(u₀+u₁τ)`:
  the linear odd term (coefficient `a₁`) and the cubic odd term (`a₃`).  In RNC the linear term VANISHES
  identically (`∂g(0)=0`, `Γ(0)=0`), so the sole residual obstruction is the CUBIC `a₃ = ∇R` term — a
  genuinely higher-order (`O(z³)` before differentiation) quantity, subleading under the √ε sliver.  The
  even factors `radialCutoff` and `gaussDdim` ARE exactly even (proved here:
  `radialCutoff_even`, `gaussDdim_even`), so the obstruction is confined to the amplitude's odd part.

  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and does NOT close `hCConv` on the live capstone.
  It proves the EXACT transposition for the EVEN-displacement idealization (the leading kernel) and
  proves the concrete even factors are even — pinning the residual obstruction to the cubic ∇R amplitude
  term.  The live witness's chart `V(q,p)` is the CURVED RNC log map (not `p − q`) and its amplitude is
  NOT exactly even, so this file does not by itself discharge the live `hCConv`.  No `sorry`, no new
  axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.SmoothCutoff
import QIQTH.RadialDistance
import QIQTH.HeatParametrixAnsatz

open QIQTH.Curvature
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ### 1 — the partial-derivative shift / reflection algebra on `Point n = Fin n → ℝ`. -/

/-- Coordinate identity: shifting the updated point by a constant `z` commutes with the update, up to
    a shift of the injected scalar. -/
theorem update_sub_eq (x z : Point n) (i : Fin n) (t : ℝ) :
    Function.update x i t - z = Function.update (x - z) i (t - z i) := by
  funext k
  by_cases hk : k = i <;> simp [Function.update, hk, Pi.sub_apply]

/-- Coordinate identity: negating the updated point commutes with the update, up to negating the
    injected scalar. -/
theorem neg_update_eq (x : Point n) (i : Fin n) (t : ℝ) :
    -(Function.update x i t) = Function.update (-x) i (-t) := by
  funext k
  by_cases hk : k = i <;> simp [Function.update, hk, Pi.neg_apply]

/-- **Domain-translation covariance of the partial derivative.**  `∂ᵢ[x' ↦ f(x' − z)](x) = (∂ᵢf)(x − z)`.
    The multivariate lift of `deriv_comp_sub_const`, via the `update`/`sub` commutation. -/
theorem pd_comp_sub_const_pt (f : Point n → ℝ) (i : Fin n) (z x : Point n) :
    pd (fun x' => f (x' - z)) i x = pd f i (x - z) := by
  unfold pd
  have hxi : (x - z) i = x i - z i := Pi.sub_apply x z i
  have hfun : (fun t => f (Function.update x i t - z))
      = (fun t => f (Function.update (x - z) i (t - z i))) := by
    funext t; rw [update_sub_eq]
  rw [hfun, hxi]
  exact deriv_comp_sub_const (fun s => f (Function.update (x - z) i s)) (z i) (x i)

/-- **Domain-reflection covariance of the partial derivative.**  `∂ᵢ[x' ↦ f(−x')](x) = −(∂ᵢf)(−x)`.
    The multivariate lift of `deriv_comp_neg`. -/
theorem pd_comp_neg_pt (f : Point n → ℝ) (i : Fin n) (x : Point n) :
    pd (fun x' => f (-x')) i x = - pd f i (-x) := by
  unfold pd
  have hxi : (-x) i = -(x i) := Pi.neg_apply x i
  have hfun : (fun t => f (-(Function.update x i t)))
      = (fun t => f (Function.update (-x) i (-t))) := by
    funext t; rw [neg_update_eq]
  rw [hfun, hxi]
  exact deriv_comp_neg (fun s => f (Function.update (-x) i s)) (x i)

/-- `∂ᵢ(−f) = −∂ᵢf`. -/
theorem pd_neg_pt (f : Point n → ℝ) (i : Fin n) (x : Point n) :
    pd (fun x' => - f x') i x = - pd f i x := by
  unfold pd
  exact deriv.neg

/-! ### 2 — even ⇒ odd ⇒ even under partial differentiation. -/

/-- **The partial derivative of an EVEN function is ODD.**  If `f(−w) = f(w)` for all `w`, then
    `(∂ᵢf)(−x) = −(∂ᵢf)(x)`. -/
theorem pd_odd_of_even (f : Point n → ℝ) (i : Fin n)
    (heven : ∀ w : Point n, f (-w) = f w) (x : Point n) :
    pd f i (-x) = - pd f i x := by
  have hfeq : (fun x' => f (-x')) = f := by funext x'; rw [heven]
  have h := pd_comp_neg_pt f i x
  rw [hfeq] at h
  linarith [h]

/-- **The partial derivative of an ODD function is EVEN.**  If `g(−w) = −g(w)` for all `w`, then
    `(∂ᵢg)(−x) = (∂ᵢg)(x)`. -/
theorem pd_even_of_odd (g : Point n → ℝ) (i : Fin n)
    (hodd : ∀ w : Point n, g (-w) = - g w) (x : Point n) :
    pd g i (-x) = pd g i x := by
  have hgeq : (fun x' => g (-x')) = (fun x' => - g x') := by funext x'; rw [hodd]
  have h := pd_comp_neg_pt g i x
  rw [hgeq, pd_neg_pt] at h
  linarith [h]

/-- **The SECOND partial derivative of an EVEN function is EVEN.**  If `f(−w) = f(w)` for all `w`, then
    `∂ⱼ∂ᵢf` is even: `(∂ⱼ∂ᵢf)(−x) = (∂ⱼ∂ᵢf)(x)`.  (Even ⟹ its `∂ᵢ` is odd ⟹ that's `∂ⱼ`-even.) -/
theorem secondPartial_even_of_even (f : Point n → ℝ) (i j : Fin n)
    (heven : ∀ w : Point n, f (-w) = f w) (x : Point n) :
    pd (fun y => pd f i y) j (-x) = pd (fun y => pd f i y) j x :=
  pd_even_of_odd (fun y => pd f i y) j (fun w => pd_odd_of_even f i heven w) x

/-! ### 3 — the CENTER-ANCHORED source↔field transposition for a displacement kernel. -/

/-- **★★★ J4-819 — THE SOURCE↔FIELD TRANSPOSITION (even displacement kernel).**  For a displacement
    kernel `H p q = F (p − q)` with `F` EVEN, the two orientations the live `hCConv` wall must
    reconcile — kPrime's `∂²_firstslot H(field=0, source=z)` and the sliver's
    `∂²_firstslot H(field=z, source=0)` — are EQUAL, for every `z` and every pair of coordinate
    directions `i j`:

        `∂ⱼ∂ᵢ[ x' ↦ F (x' − z) ] |_{x'=0}  =  ∂ⱼ∂ᵢ[ x' ↦ F (x' − 0) ] |_{x'=z}` .

    Both sides equal `(∂ⱼ∂ᵢF)(∓z)` and `∂ⱼ∂ᵢF` is even (`secondPartial_even_of_even`).  This is the
    EXACT identity the sliver→kPrime reorientation needs on the leading (even) kernel; the sympy census
    pins the residual to the ODD (∇R-cubic) amplitude part.  NOT `a₁ = R/6`. -/
theorem displacement_secondPartial_transposition_center (F : Point n → ℝ) (i j : Fin n)
    (heven : ∀ w : Point n, F (-w) = F w) (z : Point n) :
    pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      = pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z := by
  -- LHS inner: `∂ᵢ[x' ↦ F(x'−z)] = (∂ᵢF)(· − z)`, so the outer `∂ⱼ` at 0 lands at `0 − z = −z`.
  have hInnerL : (fun y => pd (fun x' => F (x' - z)) i y) = (fun y => pd F i (y - z)) := by
    funext y; exact pd_comp_sub_const_pt F i z y
  have hLHS : pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      = pd (fun y => pd F i y) j (0 - z) := by
    rw [hInnerL]; exact pd_comp_sub_const_pt (fun y => pd F i y) j z 0
  -- RHS inner: `x' − 0 = x'`, so the inner is just `∂ᵢF`; the outer `∂ⱼ` at `z` lands at `z`.
  have hInnerR : (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) = (fun y => pd F i y) := by
    funext y; simp
  rw [hLHS, hInnerR, zero_sub]
  -- `(∂ⱼ∂ᵢF)(−z) = (∂ⱼ∂ᵢF)(z)` by evenness of the second partial.
  exact secondPartial_even_of_even F i j heven z

/-! ### 4 — the concrete even factors of the live witness (obstruction confinement). -/

/-- **`gaussDdim` is EVEN.**  `gaussDdim τ (−v) = gaussDdim τ v` — the Gaussian factor of the witness
    depends on `v` only through `∑ (vⁱ)²`.  (One of the two exactly-even factors of the witness
    amplitude, confirming the transposition hypothesis is met by the leading kernel.) -/
theorem gaussDdim_even (τ : ℝ) (v : Point n) :
    QIQTH.FlatHeatEquation.gaussDdim τ (-v) = QIQTH.FlatHeatEquation.gaussDdim τ v := by
  unfold QIQTH.FlatHeatEquation.gaussDdim
  apply Finset.prod_congr rfl
  intro k _
  rw [Pi.neg_apply]
  unfold QIQTH.HeatKernelA1.heatKernel1D
  rw [neg_sq]

/-- **`radialCutoff` is EVEN.**  `radialCutoff a b (−v) = radialCutoff a b v` — the radial cutoff
    depends on `v` only through `rncRadialSq v = ∑ (vⁱ)²`.  (The second exactly-even factor.) -/
theorem rncRadialSq_neg (v : Point n) :
    QIQTH.RadialDistance.rncRadialSq (-v) = QIQTH.RadialDistance.rncRadialSq v := by
  unfold QIQTH.RadialDistance.rncRadialSq
  apply Finset.sum_congr rfl
  intro k _
  rw [Pi.neg_apply, neg_sq]

theorem radialCutoff_even (a b : ℝ) (v : Point n) :
    radialCutoff a b (-v) = radialCutoff a b v := by
  unfold radialCutoff
  rw [rncRadialSq_neg]

end QIQTH.HeatResidualBound
