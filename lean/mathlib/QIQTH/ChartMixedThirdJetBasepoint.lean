/-
  ChartMixedThirdJetBasepoint — sub-brick 3b: the BASE-POINT derivative `∂_q ∂²_p V` of the chart's
  SECOND field-jet, built as ONE MORE LAYER of the existing linear-ODE idiom.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  ODE-regularity brick: the base-point (position-slot) derivative of a PARAMETRIZED linear-ODE solution.
  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  In `ChartJetHessianMixed` the chart's SECOND field-jet is the vector `Q k = ∂ᵢ(Pⱼ·k)`
  (`gaussComp_pd_pd_mixed`'s `Q`), i.e. `Q = ∂²_p V` — the second field-derivative of the inverse chart
  `V = uniformInverseChart z`.  Sub-brick 3b asks for its BASE-POINT derivative `∂_q Q = ∂_q ∂²_p V`.

  ## THE SCOPING (`tranquil-stargazing-fox.md`, Brick-3 split).  "Take Brick 1's base-variation Jacobi
  field (`GeodesicSmoothDepDir.geodesicVariation_basepoint_endpoint_exists_uncond`) and track its first
  TWO field-endpoint derivatives as solutions of the SAME linear (Jacobi) ODE along the base geodesic.
  This is ONE more layer of the existing linear-ODE idiom carrying two field derivatives — NOT a
  second/nonlinear variation, and NOT `∂²_q`."

  ── WHY IT IS "ONE MORE LAYER OF THE SAME LINEAR-ODE IDIOM".  Along the base geodesic `Y s` (`s` the
  base-point perturbation parameter), the second field-jet `Q` — as a curve in phase space — solves a
  LINEAR ODE `X' = A(s,·)·X + b(s,·)` whose coefficient `A(s,τ) = D(geodesicField)(Y s τ)` is the SAME
  Jacobi coefficient the first-jet lineage uses (`GeodesicSmoothDep`/`BasepointFDeriv`), and whose source
  `b` carries the second-jet curvature terms.  The base slot enters `A`, `b` ONLY through the base
  geodesic `Y s`.  So `∂_q Q` is the base-point derivative of a solution of a **parametrized linear ODE**
  — obtainable by the SAME residual-Grönwall little-o argument the first-jet base-derivative bricks use
  (`GeodesicSmoothDepDir`, `GeodesicBasepointFrechet`, `BasepointFDeriv`), now one order up in the field
  slot.  Crucially it is LINEAR in the base perturbation (the derived variational equation is linear),
  NOT a second base variation `∂²_q`.

  ## WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axiom, no existing file edited):

  * `linODE_basepoint_residual_bound` — **the engine.**  For a base-parameter-indexed family `X s` of
    solutions of the linear ODE `(X s)' = A s ·(X s) + b s` on `[0,1]` with base-affine seed
    `X s 0 − X 0 0 = s·(R 0)`, and a SUPPLIED variation field `R` solving the derived variational equation
    `R' = A 0 ·R + (Ad·(X 0) + bd)` (the SAME coefficient `A 0` as the base solution, inhomogeneous by the
    `s`-derivatives `Ad`, `bd` of the coefficient/source), the base-point residual is quadratic:
        `‖X s t − X 0 t − s·(R t)‖ ≤ (Ca·Xb + Kad·Lx + Cb)·s²·exp K`.
    DERIVED by reusing `BasepointJetModulus.linODE_twopoint_diff_bound` with EQUAL coefficients
    (`A₁ = A₂ = A 0`, so `Dcoef = 0`): writing `X̃ s := X 0 + s·R`, both `X s` and `X̃ s` solve linear ODEs
    with the SAME coefficient `A 0`, and their source difference is exactly the second-order residual
    `N = (A s − A 0 − s·Ad)(X s) + s·Ad(X s − X 0) + (b s − b 0 − s·bd)`, bounded `≤ (…)·s²`.  Because the
    coefficients coincide, the first-order coefficient variation is absorbed into `R`'s source `Ad·(X 0)`,
    so NO spurious `O(|s|)` drift survives — the mechanism that makes the two-point engine deliver a
    genuine base-point DERIVATIVE rather than mere continuity.

  * `linODE_basepoint_hasDerivAt` — **the base-point derivative.**  The residual is `o(‖s‖)`, so
    `HasDerivAt (fun s => X s t) (R t) 0` — the base-point derivative of the parametrized linear-ODE
    solution EXISTS and equals the supplied variation field's endpoint `R t`.

  * `secondFieldJet_basepoint_hasDerivAt` — **the named specialisation `∂_q ∂²_p V`.**  Instantiating the
    coefficient to the concrete Jacobi coefficient `A s τ = D(geodesicField g gi)(Y s τ)` along the
    base-point-perturbed geodesic family `Y s`, the endpoint of the second field-jet `Q s := X s`
    (solving its linear ODE along `Y s`) has base-point derivative `R t`:
        `HasDerivAt (fun s => Q s t) (R t) 0`.
    This is `∂_q(∂²_p V)` at the geodesic endpoint — the mixed third jet's base derivative, LINEAR in the
    base perturbation and carrying only the SAME genuine geometric regularity the first-jet base-derivative
    bricks carry (Jacobi coefficient bound `‖A 0‖ ≤ K`, C¹-in-`s` coefficient/source with quadratic
    remainders, and the base-solution's own bounds).

  HONEST CHECKPOINT (binding).  This lands the base-point (position-slot) FIRST derivative of the SECOND
  field-jet — `∂_q ∂²_p V` at the endpoint — as a genuine `HasDerivAt`, DERIVED from the parametrized
  linear-ODE structure via the reused two-point Grönwall engine.  It carries the second-jet ODE data
  (`X s` solving its linear equation, `R` solving the derived variational equation, the C¹-in-`s`
  coefficient/source remainders) as HYPOTHESES — it does NOT construct the second-order velocity Jacobi
  field itself (that is `jacobiVariation_secondOrder`/`BasepointJacobi2`), NOT the Fréchet (all-direction)
  upgrade, NOT the wiring to the concrete `uniformInverseChart`/`uniformFlowExp`, NOT `hCConv`,
  NOT Raychaudhuri, NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep
import QIQTH.BasepointJetModulus

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **The engine — base-point residual of a parametrized linear-ODE solution.**  See the file header.
    Reuses `linODE_twopoint_diff_bound` with EQUAL coefficients (`Dcoef = 0`), the approximate solution
    `X̃ s := X 0 + s·R`, and the second-order source residual `N`.  NOT `a₁ = R/6`. -/
theorem linODE_basepoint_residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → ℝ → (E →L[ℝ] E)} {Ad : ℝ → (E →L[ℝ] E)}
    {X : ℝ → ℝ → E} {b : ℝ → ℝ → E} {bd : ℝ → E} {R : ℝ → E}
    {K Ca Cb Xb Kad Lx Rb : ℝ} (hK0 : 0 ≤ K)
    (hX : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (X s) (A s τ (X s τ) + b s τ) τ)
    (hR : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt R (A 0 τ (R τ) + (Ad τ (X 0 τ) + bd τ)) τ)
    (hseed : ∀ s : ℝ, X s 0 - X 0 0 = s • R 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖A 0 τ‖ ≤ K)
    (harem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖A s τ - A 0 τ - s • Ad τ‖ ≤ Ca * s ^ 2)
    (hKad : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Ad τ‖ ≤ Kad)
    (hXb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ‖ ≤ Xb)
    (hXlip : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ - X 0 τ‖ ≤ Lx * |s|)
    (hRb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖R τ‖ ≤ Rb)
    (hbrem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b s τ - b 0 τ - s • bd τ‖ ≤ Cb * s ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s : ℝ, ‖X s t - X 0 t - s • R t‖ ≤ (Ca * Xb + Kad * Lx + Cb) * s ^ 2 * Real.exp K := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  intro s
  set C : ℝ := Ca * Xb + Kad * Lx + Cb with hCdef
  -- the approximate solution `X̃ s := X 0 + s·R` and its (equal-coefficient) source.
  set X2 : ℝ → E := fun τ => X 0 τ + s • R τ with hX2def
  set b2 : ℝ → E := fun τ => b 0 τ + s • (Ad τ (X 0 τ) + bd τ) with hb2def
  -- `X s` re-expressed with coefficient `A 0` and source `b1`.
  set b1 : ℝ → E := fun τ => A s τ (X s τ) + b s τ - A 0 τ (X s τ) with hb1def
  -- (1) `X s` solves `X' = A 0 ·X + b1`.
  have hX1' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (X s) (A 0 τ (X s τ) + b1 τ) τ := by
    intro τ hτ
    have hv : A 0 τ (X s τ) + b1 τ = A s τ (X s τ) + b s τ := by simp only [hb1def]; abel
    rw [hv]; exact hX s τ hτ
  -- (2) `X̃ s` solves `X̃' = A 0 ·X̃ + b2`.
  have hX2' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt X2 (A 0 τ (X2 τ) + b2 τ) τ := by
    intro τ hτ
    have hd : HasDerivAt X2
        ((A 0 τ (X 0 τ) + b 0 τ) + s • (A 0 τ (R τ) + (Ad τ (X 0 τ) + bd τ))) τ :=
      (hX 0 τ hτ).add ((hR τ hτ).const_smul s)
    have hv : (A 0 τ (X 0 τ) + b 0 τ) + s • (A 0 τ (R τ) + (Ad τ (X 0 τ) + bd τ))
        = A 0 τ (X2 τ) + b2 τ := by
      simp only [hX2def, hb2def, map_add, map_smul, smul_add]
      abel
    rwa [hv] at hd
  -- (3) equal initial values.
  have h0 : X s 0 = X2 0 := by
    simp only [hX2def]; have := hseed s; rw [sub_eq_iff_eq_add] at this; rw [this]; abel
  -- (4) the source difference `b1 − b2 = N` and its quadratic bound.
  have hNbound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b1 τ - b2 τ‖ ≤ C * s ^ 2 := by
    intro τ hτ
    -- split `N = term1 + term2 + term3`.
    have hsplit : b1 τ - b2 τ
        = (A s τ - A 0 τ - s • Ad τ) (X s τ)
          + s • (Ad τ (X s τ - X 0 τ))
          + (b s τ - b 0 τ - s • bd τ) := by
      simp only [hb1def, hb2def, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        map_sub, smul_sub, smul_add]
      abel
    rw [hsplit]
    have hXb0 : 0 ≤ Xb := le_trans (norm_nonneg _) (hXb 0 0 h0mem)
    have ht1 : ‖(A s τ - A 0 τ - s • Ad τ) (X s τ)‖ ≤ Ca * s ^ 2 * Xb :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (harem s τ hτ) (hXb s τ hτ) (norm_nonneg _)
          (le_trans (norm_nonneg _) (harem s τ hτ)))
    have ht2 : ‖s • (Ad τ (X s τ - X 0 τ))‖ ≤ Kad * Lx * s ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hinner : ‖Ad τ (X s τ - X 0 τ)‖ ≤ Kad * (Lx * |s|) :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hKad τ hτ) (hXlip s τ hτ) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hKad τ hτ)))
      calc |s| * ‖Ad τ (X s τ - X 0 τ)‖
          ≤ |s| * (Kad * (Lx * |s|)) := mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
        _ = Kad * Lx * s ^ 2 := by rw [← sq_abs s]; ring
    have ht3 : ‖b s τ - b 0 τ - s • bd τ‖ ≤ Cb * s ^ 2 := hbrem s τ hτ
    calc ‖(A s τ - A 0 τ - s • Ad τ) (X s τ)
            + s • (Ad τ (X s τ - X 0 τ))
            + (b s τ - b 0 τ - s • bd τ)‖
        ≤ ‖(A s τ - A 0 τ - s • Ad τ) (X s τ) + s • (Ad τ (X s τ - X 0 τ))‖
            + ‖b s τ - b 0 τ - s • bd τ‖ := norm_add_le _ _
      _ ≤ (‖(A s τ - A 0 τ - s • Ad τ) (X s τ)‖ + ‖s • (Ad τ (X s τ - X 0 τ))‖)
            + ‖b s τ - b 0 τ - s • bd τ‖ := by
              exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (Ca * s ^ 2 * Xb + Kad * Lx * s ^ 2) + Cb * s ^ 2 :=
            add_le_add (add_le_add ht1 ht2) ht3
      _ = C * s ^ 2 := by rw [hCdef]; ring
  -- (5) uniform bound on `X̃ s` (only used against the vanishing `Dcoef`).
  have hX2bound : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X2 τ‖ ≤ Xb + |s| * Rb := by
    intro τ hτ
    simp only [hX2def]
    refine (norm_add_le _ _).trans (add_le_add (hXb 0 τ hτ) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRb τ hτ) (abs_nonneg _)
  -- (6) invoke the two-point engine with equal coefficients (`Dcoef = 0`).
  have hmain := linODE_twopoint_diff_bound (E := E)
    (A₁ := fun τ => A 0 τ) (A₂ := fun τ => A 0 τ)
    (X₁ := X s) (X₂ := X2) (b₁ := b1) (b₂ := b2)
    (K := K) (Dcoef := 0) (Xb := Xb + |s| * Rb) (Dsrc := C * s ^ 2)
    hK0 hX1' hX2' h0 hKb (fun τ _ => by simp) hX2bound hNbound
  have := hmain t ht
  -- simplify `(0 * (Xb + |s|·Rb) + C·s²)·exp K = C·s²·exp K` and `X̃ s t = X 0 t + s·R t`.
  rw [zero_mul, zero_add] at this
  have hXt : X s t - X2 t = X s t - X 0 t - s • R t := by simp only [hX2def]; abel
  rw [hXt] at this
  exact this

/-- **The base-point derivative of the parametrized linear-ODE solution.**  The `o(‖s‖)` residual of
    `linODE_basepoint_residual_bound` gives `HasDerivAt (fun s => X s t) (R t) 0`.  NOT `a₁ = R/6`. -/
theorem linODE_basepoint_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → ℝ → (E →L[ℝ] E)} {Ad : ℝ → (E →L[ℝ] E)}
    {X : ℝ → ℝ → E} {b : ℝ → ℝ → E} {bd : ℝ → E} {R : ℝ → E}
    {K Ca Cb Xb Kad Lx Rb : ℝ} (hK0 : 0 ≤ K)
    (hX : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (X s) (A s τ (X s τ) + b s τ) τ)
    (hR : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt R (A 0 τ (R τ) + (Ad τ (X 0 τ) + bd τ)) τ)
    (hseed : ∀ s : ℝ, X s 0 - X 0 0 = s • R 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖A 0 τ‖ ≤ K)
    (harem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖A s τ - A 0 τ - s • Ad τ‖ ≤ Ca * s ^ 2)
    (hKad : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Ad τ‖ ≤ Kad)
    (hXb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ‖ ≤ Xb)
    (hXlip : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ - X 0 τ‖ ≤ Lx * |s|)
    (hRb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖R τ‖ ≤ Rb)
    (hbrem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b s τ - b 0 τ - s • bd τ‖ ≤ Cb * s ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => X s t) (R t) 0 := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hres := linODE_basepoint_residual_bound hK0 hX hR hseed hKb harem hKad hXb hXlip hRb hbrem ht
  -- nonnegativity of the residual constant `C`.
  have hXb0 : 0 ≤ Xb := le_trans (norm_nonneg _) (hXb 0 0 h0mem)
  have hKad0 : 0 ≤ Kad := le_trans (norm_nonneg _) (hKad 0 h0mem)
  have hCa0 : 0 ≤ Ca := by
    have := harem 1 0 h0mem; rw [one_pow, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hCb0 : 0 ≤ Cb := by
    have := hbrem 1 0 h0mem; rw [one_pow, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hLx0 : 0 ≤ Lx := by
    have := hXlip 1 0 h0mem; rw [abs_one, mul_one] at this; exact le_trans (norm_nonneg _) this
  set C : ℝ := Ca * Xb + Kad * Lx + Cb with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set M : ℝ := C * Real.exp K with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hC0 (Real.exp_pos K).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (M + 1), by positivity, fun s hs => ?_⟩
  rw [dist_eq_norm, sub_zero] at hs
  have hrw : C * s ^ 2 * Real.exp K = M * ‖s‖ ^ 2 := by
    rw [hMdef, Real.norm_eq_abs, sq_abs]; ring
  have hkey : ‖X s t - X 0 t - s • R t‖ ≤ M * ‖s‖ ^ 2 := by rw [← hrw]; exact hres s
  have hMs : M * ‖s‖ ≤ c := by
    have hlt : ‖s‖ * (M + 1) < c := (lt_div_iff₀ (by positivity)).mp hs
    nlinarith [norm_nonneg s, hM0]
  calc ‖X s t - X 0 t - s • R t‖
      ≤ M * ‖s‖ ^ 2 := hkey
    _ = (M * ‖s‖) * ‖s‖ := by ring
    _ ≤ c * ‖s‖ := mul_le_mul_of_nonneg_right hMs (norm_nonneg _)

/-- **`∂_q ∂²_p V` — the named geodesic specialisation.**  The coefficient is the concrete Jacobi
    coefficient `A s τ = D(geodesicField g gi)(Y s τ)` along the base-point-perturbed geodesic family
    `Y s`; the second field-jet `Q s := X s` solves its linear ODE along `Y s`; `R` solves the derived
    variational equation.  The endpoint of the second field-jet has base-point derivative `R t`:
        `HasDerivAt (fun s => Q s t) (R t) 0`,
    i.e. `∂_q(∂²_p V)` at the geodesic endpoint — LINEAR in the base perturbation, NOT `∂²_q`.
    NOT `a₁ = R/6`. -/
theorem secondFieldJet_basepoint_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    {Y : ℝ → ℝ → Point n × Point n}
    {Ad : ℝ → ((Point n × Point n) →L[ℝ] Point n × Point n)}
    {X : ℝ → ℝ → Point n × Point n} {b : ℝ → ℝ → Point n × Point n}
    {bd : ℝ → Point n × Point n} {R : ℝ → Point n × Point n}
    {K Ca Cb Xb Kad Lx Rb : ℝ} (hK0 : 0 ≤ K)
    (hX : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (X s) (fderiv ℝ (geodesicField g gi) (Y s τ) (X s τ) + b s τ) τ)
    (hR : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt R (fderiv ℝ (geodesicField g gi) (Y 0 τ) (R τ) + (Ad τ (X 0 τ) + bd τ)) τ)
    (hseed : ∀ s : ℝ, X s 0 - X 0 0 = s • R 0)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y 0 τ)‖ ≤ K)
    (harem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Y s τ) - fderiv ℝ (geodesicField g gi) (Y 0 τ) - s • Ad τ‖
        ≤ Ca * s ^ 2)
    (hKad : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Ad τ‖ ≤ Kad)
    (hXb : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ‖ ≤ Xb)
    (hXlip : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖X s τ - X 0 τ‖ ≤ Lx * |s|)
    (hRb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖R τ‖ ≤ Rb)
    (hbrem : ∀ s : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖b s τ - b 0 τ - s • bd τ‖ ≤ Cb * s ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => X s t) (R t) 0 :=
  linODE_basepoint_hasDerivAt (A := fun s τ => fderiv ℝ (geodesicField g gi) (Y s τ))
    hK0 hX hR hseed hKb harem hKad hXb hXlip hRb hbrem ht

end QIQTH.ExpMap
