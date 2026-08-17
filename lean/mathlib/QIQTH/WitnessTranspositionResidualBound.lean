/-
  WitnessTranspositionResidualBound — J4-820: the QUANTITATIVE residual of the source↔field
  transposition, generalizing the J4-819 even-kernel mechanism to an ARBITRARY displacement kernel
  and reducing the live `hCConv` obstruction to a single satisfiable O(‖z‖) interface hypothesis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (J4-818/819).  The one genuine wall blocking `hCConv` on the live capstone is a source↔field
  TRANSPOSITION of the second field-partial of the witness `vanVleckGatedWitness`:
      kPrime  needs   `∂ⱼ∂ᵢ[ x' ↦ F (x' − z) ] |_{x'=0}`   (chart at source `z`, field ∂ at 0),
      sliver  gives   `∂ⱼ∂ᵢ[ x' ↦ F (x' − 0) ] |_{x'=z}`   (chart at source 0, field ∂ at `z`).
  J4-819 (`WitnessSourceFieldTransposition.lean`) proved these are EQUAL when the displacement kernel
  `F` is EVEN (the leading Gaussian·van-Vleck part), and pinned the obstruction to the ODD part of the
  amplitude — which in RNC is the CUBIC `a₃ = ∇R` term (`a₁` vanishes, `∂g(0)=0`, `Γ(0)=0`).

  ── WHAT THIS FILE ADDS (J4-820).  The EXACT quantitative residual for a GENERAL (non-even) kernel,
  and its reduction to a satisfiable O(‖z‖) sliver-window interface:

  1. `secondPartial_transposition_residual_eq` — the EXACT residual formula: the transposition
     difference equals `G(−z) − G(z)` where `G = ∂ⱼ∂ᵢF` is the kernel's second partial.  This is a
     strict generalization of J4-819: when `F` is even, `G` is even and the residual is `0` (recovered
     in `residual_zero_of_even`).

  2. `residual_eq_neg_two_oddPart` — the residual equals `−2 · oddPart(∂ⱼ∂ᵢF)(z)`, confining it
     EXACTLY to the ODD part of the second partial (the algebraic mirror of the sympy census's "carried
     entirely by odd amplitude coefficients `a₁`, `a₃`").

  3. `residual_abs_le_two_sup` — the crude uniform bound `|residual| ≤ 2·B` from any sup bound `B` on
     `|∂ⱼ∂ᵢF|` (always available; the residual can never exceed twice the second-partial's magnitude).

  4. `residual_sliver_bound` — ★ THE SLIVER-BUDGET REDUCTION.  Under the interface hypothesis
     `hodd : |G(−z) − G(z)| ≤ L·‖z‖` (the odd part of the second partial is O(‖z‖) — SATISFIED
     non-vacuously by the concrete van-Vleck amplitude, whose odd part starts at the cubic ∇R term so
     its second partial is LINEAR in `z`, verified in `docs/qg_roadmap/j4_820_cubic_residual_scaling.py`:
     residual = `−12·a₃·z + O(z³)`), and the sliver window `‖z‖ ≤ √ε`, the residual obeys
     `|residual| ≤ L·√ε` — EXACTLY the O(√ε) rate the closed J4-817 sliver bound already carries.
     The cubic ∇R residual is thus absorbed within the existing sliver budget.

  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and does NOT by itself close `hCConv` on the live
  capstone.  It proves the EXACT residual formula for a general displacement kernel and reduces the
  J4-819 obstruction to the single O(‖z‖) interface hypothesis `hodd`.  Wiring into the live capstone
  still requires (i) the curved-RNC-chart displacement reduction (the live `V(q,p)` is the log map, not
  `p−q`) and (ii) discharging `hodd` at the concrete curved-chart amplitude.  The sympy artifact
  justifies (ii)'s satisfiability; the Lean discharge on the curved chart is the residual work.
  No `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.WitnessSourceFieldTransposition

open QIQTH.Curvature
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ### 1 — the EXACT general residual formula. -/

/-- **★ J4-820 — THE EXACT TRANSPOSITION RESIDUAL (general displacement kernel).**  For an ARBITRARY
    displacement kernel `H p q = F (p − q)`, the transposition difference the `hCConv` wall must
    reconcile — kPrime's `∂ⱼ∂ᵢ[x'↦F(x'−z)]|₀` minus the sliver's `∂ⱼ∂ᵢ[x'↦F(x'−0)]|_z` — equals
    EXACTLY `G(−z) − G(z)`, where `G := ∂ⱼ∂ᵢF` is the kernel's second partial.  Strict generalization
    of J4-819's even case (`displacement_secondPartial_transposition_center`), whose zero residual is
    recovered when `G` is even. -/
theorem secondPartial_transposition_residual_eq (F : Point n → ℝ) (i j : Fin n) (z : Point n) :
    pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z
    = pd (fun y => pd F i y) j (-z) - pd (fun y => pd F i y) j z := by
  -- LHS inner: `∂ᵢ[x'↦F(x'−z)] = (∂ᵢF)(·−z)`, so the outer `∂ⱼ` at 0 lands at `0 − z = −z`.
  have hInnerL : (fun y => pd (fun x' => F (x' - z)) i y) = (fun y => pd F i (y - z)) := by
    funext y; exact pd_comp_sub_const_pt F i z y
  have hLHS : pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      = pd (fun y => pd F i y) j (0 - z) := by
    rw [hInnerL]; exact pd_comp_sub_const_pt (fun y => pd F i y) j z 0
  -- RHS inner: `x' − 0 = x'`, so the inner is just `∂ᵢF`; the outer `∂ⱼ` at `z` stays at `z`.
  have hInnerR : (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) = (fun y => pd F i y) := by
    funext y; simp
  rw [hLHS, hInnerR, zero_sub]

/-! ### 2 — the residual is exactly `−2 ·` the odd part of the second partial. -/

/-- The odd part of a scalar field on `Point n`. -/
noncomputable def oddPart (G : Point n → ℝ) (w : Point n) : ℝ := (G w - G (-w)) / 2

/-- **★ J4-820 — RESIDUAL = `−2 · oddPart(∂ⱼ∂ᵢF)`.**  The transposition residual is confined EXACTLY
    to the ODD part of the kernel's second partial — the algebraic statement of the sympy census's
    "the transposition difference is carried ENTIRELY by the odd amplitude coefficients (`a₁` linear,
    `a₃` cubic)".  In RNC `a₁ = 0`, so the residual reduces to the cubic ∇R (`a₃`) contribution. -/
theorem residual_eq_neg_two_oddPart (F : Point n → ℝ) (i j : Fin n) (z : Point n) :
    pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z
    = -2 * oddPart (fun w => pd (fun y => pd F i y) j w) z := by
  rw [secondPartial_transposition_residual_eq]
  unfold oddPart
  ring

/-- **Consistency with J4-819.**  When `F` is EVEN, its second partial is even
    (`secondPartial_even_of_even`), so the residual VANISHES — recovering
    `displacement_secondPartial_transposition_center`. -/
theorem residual_zero_of_even (F : Point n → ℝ) (i j : Fin n)
    (heven : ∀ w : Point n, F (-w) = F w) (z : Point n) :
    pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z = 0 := by
  rw [secondPartial_transposition_residual_eq, secondPartial_even_of_even F i j heven z, sub_self]

/-! ### 3 — quantitative bounds on the residual. -/

/-- **★ J4-820 — CRUDE UNIFORM BOUND.**  From any sup bound `B` on `|∂ⱼ∂ᵢF|`, the transposition
    residual obeys `|residual| ≤ 2·B`.  Always available; the residual can never exceed twice the
    second-partial's magnitude. -/
theorem residual_abs_le_two_sup (F : Point n → ℝ) (i j : Fin n) (z : Point n) {B : ℝ}
    (hB : ∀ w, |pd (fun y => pd F i y) j w| ≤ B) :
    |pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z| ≤ 2 * B := by
  rw [secondPartial_transposition_residual_eq]
  calc |pd (fun y => pd F i y) j (-z) - pd (fun y => pd F i y) j z|
      ≤ |pd (fun y => pd F i y) j (-z) - 0| + |0 - pd (fun y => pd F i y) j z| :=
        abs_sub_le _ 0 _
    _ = |pd (fun y => pd F i y) j (-z)| + |pd (fun y => pd F i y) j z| := by
        rw [sub_zero, zero_sub, abs_neg]
    _ ≤ B + B := add_le_add (hB _) (hB _)
    _ = 2 * B := by ring

/-- **★★★ J4-820 — THE SLIVER-BUDGET REDUCTION.**  This is the interface that discharges the J4-818/819
    transposition wall into the closed J4-817 sliver rate.  Under
      • `hodd` — the odd part of the second partial is O(‖z‖): `|G(−z) − G(z)| ≤ L·‖z‖`.  This is
        SATISFIED non-vacuously by the concrete van-Vleck amplitude: its odd part starts at the cubic
        `a₃ = ∇R` term, so the second partial `G = ∂ⱼ∂ᵢF` is LINEAR in `z` near the origin
        (sympy: `residual = −12·a₃·z + O(z³)`, `docs/qg_roadmap/j4_820_cubic_residual_scaling.py`);
      • `hwin` — the sliver window `‖z‖ ≤ √ε`,
    the transposition residual obeys `|residual| ≤ L·√ε` — EXACTLY the O(√ε) rate the closed J4-817
    sliver bound already carries.  Hence the cubic ∇R residual is absorbed within the existing sliver
    budget; it does not worsen the transposition-difference rate.  This reduces the J4-818 wall to
    discharging `hodd` at the concrete curved-RNC-chart amplitude. -/
theorem residual_sliver_bound (F : Point n → ℝ) (i j : Fin n) (z : Point n) {L ε : ℝ}
    (hL : 0 ≤ L)
    (hodd : |pd (fun y => pd F i y) j (-z) - pd (fun y => pd F i y) j z| ≤ L * ‖z‖)
    (hwin : ‖z‖ ≤ Real.sqrt ε) :
    |pd (fun y => pd (fun x' => F (x' - z)) i y) j (0 : Point n)
      - pd (fun y => pd (fun x' => F (x' - (0 : Point n))) i y) j z| ≤ L * Real.sqrt ε := by
  rw [secondPartial_transposition_residual_eq]
  exact hodd.trans (mul_le_mul_of_nonneg_left hwin hL)

end QIQTH.HeatResidualBound
