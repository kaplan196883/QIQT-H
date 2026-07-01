/-
  BRIDGE A2 — the emergence map: the (SUPPLIED) linearized area functional, wired to the screen code.

  ★ SCOPE (BRIDGE_PLAN.md, GPT-5.5-pro-verified). The linearized area variation of a surface `Σ` under a metric
    perturbation `h` is `δA_Σ(h) = ½∫_Σ √γ γ^{ab} e_a^μ e_b^ν h_{μν}`; here in finite/discretized form: a
    `ScreenSurface` is a finite set of area elements, each carrying a background weight `w_a ≥ 0` (the `√γ` area
    element) and a tangent frame `(e₁ᵃ, e₂ᵃ)`, and
        δA_Σ(h) = ½ ∑_a w_a (h(e₁ᵃ,e₁ᵃ) + h(e₂ᵃ,e₂ᵃ)).
    ⚠ THE MAP IS **SUPPLIED** — this module never derives the geometric area functional from the substrate
    (deriving it is bridge ingredient D, the open frontier). What IS proven:
  • `areaVar` is a LINEAR functional of `h` (`areaProbe` bundles it as a `→ₗ[ℝ]` — the G1-probe shape);
    `δA(0) = 0` (flat background).
  • **The screen-code wiring** (`screenArea_eq_bg_add_areaVar`): a `ScreenCut` whose independent area charge is
    the geometrically perturbed weight `w_a(1 + ½ tr_Σ h)` has `screenArea = (background area) + δA_Σ(h)` — the
    code's area charge and the geometric area variation become ONE object under the supplied identification.
  • **The separating witness** (`area_probes_separate`): area probes CAN reconstruct the perturbation — a
    symmetric `h` with vanishing area variation at every ray surface is zero. This makes the "separating family"
    hypothesis of the FGHMVR skeleton (G1 `Separating`) NON-VACUOUS with genuinely geometric (area) probes: area
    data at enough surfaces pins the metric perturbation. (A single surface does NOT determine `h` — separation
    genuinely needs the family, exactly as the verification demanded.)

  ⚠ Honest labels: the identification `areaWt ↔ perturbed geometric weight` is a carried hypothesis of the wiring
    theorem (a supplied map, never an axiom); linearized only; deriving `α_e`/the area functional from a substrate
    is ingredient D. Free-field bridge context.
-/
import Mathlib
import QIQTH.EmergentDynamics
import QIQTH.HolographicScreenCode

namespace QIQTH.AreaMap

open QIQTH.GravDyn QIQTH.ScreenCode

variable {ι : Type*}

/-- A **discretized screen surface**: finitely many area elements, each with a background area weight `w_a ≥ 0`
    (the `√γ` element) and a tangent frame `(e₁ᵃ, e₂ᵃ)` spanning the element. -/
structure ScreenSurface (ι : Type*) where
  /-- the area elements -/
  elems : Finset ι
  /-- background area weight (the `√γ` element) -/
  w : ι → ℝ
  /-- first tangent vector of the element -/
  e1 : ι → Fin 4 → ℝ
  /-- second tangent vector of the element -/
  e2 : ι → Fin 4 → ℝ
  w_nonneg : ∀ a, 0 ≤ w a

/-- **The (SUPPLIED) linearized area variation** `δA_Σ(h) = ½ ∑_a w_a (h(e₁ᵃ,e₁ᵃ) + h(e₂ᵃ,e₂ᵃ))` — the
    discretized first-order area response of the surface to the metric perturbation `h`. -/
noncomputable def areaVar (Sig : ScreenSurface ι) (h : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  (1 / 2) * ∑ a ∈ Sig.elems, Sig.w a * (quadForm h (Sig.e1 a) + quadForm h (Sig.e2 a))

theorem quadForm_add (h g : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    quadForm (h + g) v = quadForm h v + quadForm g v := by
  simp only [quadForm, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem quadForm_smul (c : ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    quadForm (c • h) v = c * quadForm h v := by
  simp only [quadForm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quadForm_zero (v : Fin 4 → ℝ) : quadForm (0 : Matrix (Fin 4) (Fin 4) ℝ) v = 0 := by
  simp [quadForm]

theorem quadForm_zero_vec (h : Matrix (Fin 4) (Fin 4) ℝ) : quadForm h (0 : Fin 4 → ℝ) = 0 := by
  simp [quadForm]

/-- The area variation is additive in the perturbation. -/
theorem areaVar_add (Sig : ScreenSurface ι) (h g : Matrix (Fin 4) (Fin 4) ℝ) :
    areaVar Sig (h + g) = areaVar Sig h + areaVar Sig g := by
  simp only [areaVar, quadForm_add]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The area variation is homogeneous in the perturbation. -/
theorem areaVar_smul (Sig : ScreenSurface ι) (c : ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ) :
    areaVar Sig (c • h) = c * areaVar Sig h := by
  simp only [areaVar, quadForm_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- Flat background: `δA(0) = 0`. -/
theorem areaVar_zero (Sig : ScreenSurface ι) : areaVar Sig (0 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by
  simp [areaVar, quadForm_zero]

/-- **The area probe as a linear functional** `h ↦ δA_Σ(h)` — exactly the `E →ₗ[ℝ] ℝ` probe shape the FGHMVR
    skeleton (`G1`, `Separating`) consumes. -/
noncomputable def areaProbe (Sig : ScreenSurface ι) : Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] ℝ where
  toFun := areaVar Sig
  map_add' := areaVar_add Sig
  map_smul' c h := by simpa using areaVar_smul Sig c h

/-- **A2 WIRING — the screen-code area charge varies by exactly the geometric area variation.** For a `ScreenCut`
    whose (independent) area weights are SUPPLIED as the geometrically perturbed elements
    `areaWt a = w_a·(1 + ½(h(e₁ᵃ,e₁ᵃ) + h(e₂ᵃ,e₂ᵃ)))`, the code's area charge is
    `screenArea = (background area) + δA_Σ(h)`. Under the supplied identification the code's area charge and the
    geometric linearized area are ONE object. ⚠ The identification (`hwt`) is a CARRIED hypothesis — the supplied
    emergence map, never derived here (deriving it is ingredient D). -/
theorem screenArea_eq_bg_add_areaVar (S : ScreenCut ι) (Sig : ScreenSurface ι)
    (h : Matrix (Fin 4) (Fin 4) ℝ) (hlinks : S.links = Sig.elems)
    (hwt : ∀ a ∈ Sig.elems,
      S.areaWt a = Sig.w a * (1 + (1 / 2) * (quadForm h (Sig.e1 a) + quadForm h (Sig.e2 a)))) :
    ScreenCode.screenArea S = (∑ a ∈ Sig.elems, Sig.w a) + areaVar Sig h := by
  have hA : areaVar Sig h
      = (1 / 2) * ∑ a ∈ Sig.elems, Sig.w a * (quadForm h (Sig.e1 a) + quadForm h (Sig.e2 a)) := rfl
  have hS : ScreenCode.screenArea S = ∑ e ∈ S.links, S.areaWt e := rfl
  rw [hS, hlinks, Finset.sum_congr rfl hwt, hA, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ## The separating witness — area probes genuinely reconstruct the perturbation -/

/-- A **ray surface**: a single unit-weight element with tangent `v` (second tangent zero) — the elementary
    area probe `δA(h) = ½ h(v,v)`. -/
noncomputable def raySurf (v : Fin 4 → ℝ) : ScreenSurface Unit where
  elems := {()}
  w := fun _ => 1
  e1 := fun _ => v
  e2 := fun _ => 0
  w_nonneg := fun _ => zero_le_one

/-- The ray-surface area variation is the half quadratic form: `δA_ray(v)(h) = ½ h(v,v)`. -/
theorem areaVar_ray (v : Fin 4 → ℝ) (h : Matrix (Fin 4) (Fin 4) ℝ) :
    areaVar (raySurf v) h = (1 / 2) * quadForm h v := by
  simp [areaVar, raySurf, quadForm_zero_vec]

/-- **A2 SEPARATING WITNESS — area probes separate symmetric perturbations.** A symmetric `h` whose area
    variation vanishes at EVERY ray surface is zero: area data at enough surfaces reconstructs the metric
    perturbation. This makes the FGHMVR skeleton's separating-probe hypothesis (`G1`) NON-VACUOUS with genuinely
    geometric probes. (No single surface suffices — separation needs the family.) -/
theorem area_probes_separate (h : Matrix (Fin 4) (Fin 4) ℝ) (hSym : h.IsSymm)
    (hall : ∀ v : Fin 4 → ℝ, areaVar (raySurf v) h = 0) : h = 0 := by
  have hq : ∀ v : Fin 4 → ℝ, quadForm h v = 0 := by
    intro v
    have := hall v
    rw [areaVar_ray] at this
    linarith
  have h01 : h 1 0 = h 0 1 := hSym.apply 0 1
  have h02 : h 2 0 = h 0 2 := hSym.apply 0 2
  have h03 : h 3 0 = h 0 3 := hSym.apply 0 3
  have h12 : h 2 1 = h 1 2 := hSym.apply 1 2
  have h13 : h 3 1 = h 1 3 := hSym.apply 1 3
  have h23 : h 3 2 = h 2 3 := hSym.apply 2 3
  have d0 := hq ![1, 0, 0, 0]
  have d1 := hq ![0, 1, 0, 0]
  have d2 := hq ![0, 0, 1, 0]
  have d3 := hq ![0, 0, 0, 1]
  have c01 := hq ![1, 1, 0, 0]
  have c02 := hq ![1, 0, 1, 0]
  have c03 := hq ![1, 0, 0, 1]
  have c12 := hq ![0, 1, 1, 0]
  have c13 := hq ![0, 1, 0, 1]
  have c23 := hq ![0, 0, 1, 1]
  simp only [quadForm, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at d0 d1 d2 d3 c01 c02 c03 c12 c13 c23
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    linarith [h01, h02, h03, h12, h13, h23, d0, d1, d2, d3, c01, c02, c03, c12, c13, c23]

end QIQTH.AreaMap
