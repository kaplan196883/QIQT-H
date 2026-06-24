import QIQTH.QiqtToGR

/-!
# A satisfiability witness for the headline GR theorem

`QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr` is project-axiom-free but carries 23 labelled hypotheses;
project-axiom-freedom does **not** by itself show those hypotheses are jointly satisfiable (a
contradictory premise set would make the theorem vacuously true). Here we exhibit a flat (Minkowski)
vacuum model — `g = gi = fun _ => gm` (the constant reference metric, with `gm·gm = I`), the identity
frame, `T = 0`, and zero entropy / modular-energy / area — verify **all 23 hypotheses**, and *apply*
the theorem, obtaining its conclusion (the vacuum Einstein equation). This certifies that the
headline premise set is satisfiable and the theorem non-vacuous. Uses only Lean's standard axioms.
-/

namespace QIQTH.QiqtGrWitness

open QIQTH.Curvature QIQTH.EinsteinEOS

/-! ## The curvature of a constant metric vanishes -/

variable {n : ℕ}

/-- Christoffel symbols of a constant metric vanish (every metric derivative is zero). -/
theorem christoffel_constMetric (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (μ ν ρ : Fin n) (x : Point n) :
    christoffel (fun _ => G) gi μ ν ρ x = 0 := by
  simp only [christoffel, pd_const, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]

/-- Riemann tensor of a constant metric vanishes. -/
theorem riemann_constMetric (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (ρ σ μ ν : Fin n) (x : Point n) :
    riemann (fun _ => G) gi ρ σ μ ν x = 0 := by
  simp only [riemann, pd_const, christoffel_constMetric, mul_zero, sub_self, add_zero,
    Finset.sum_const_zero]

/-- Ricci tensor of a constant metric vanishes. -/
theorem ricci_constMetric (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (σ ν : Fin n) (x : Point n) :
    ricci (fun _ => G) gi σ ν x = 0 := by
  simp only [ricci, riemann_constMetric, Finset.sum_const_zero]

/-- Scalar curvature of a constant metric vanishes. -/
theorem scalarCurv_constMetric (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (x : Point n) :
    scalarCurv (fun _ => G) gi x = 0 := by
  simp only [scalarCurv, ricci_constMetric, mul_zero, Finset.sum_const_zero]

/-- Einstein tensor of a constant metric vanishes. -/
theorem einsteinTensor_constMetric (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (σ ν : Fin n) (x : Point n) :
    einsteinTensor (fun _ => G) gi σ ν x = 0 := by
  simp only [einsteinTensor, ricci_constMetric, scalarCurv_constMetric, zero_mul, mul_zero, sub_zero]

/-- The raised divergence of the zero `(0,2)` tensor vanishes. -/
theorem div02_zeroTensor (g gi : Point n → Fin n → Fin n → ℝ) (ν : Fin n) (x : Point n) :
    div02 g gi (fun _ _ _ => 0) ν x = 0 := by
  simp only [div02, covDeriv02, pd_const, mul_zero, Finset.sum_const_zero, sub_zero,
    Finset.sum_const_zero]

/-! ## Algebra of the constant reference metric `gm = diag(-1,1,1,1)` -/

theorem gm_symm (a b : Fin 4) : gm a b = gm b a := by
  fin_cases a <;> fin_cases b <;> simp [gm]

/-- `gm` is its own inverse: `∑_σ gm_{aσ} gm_{σb} = δ_{ab}`. -/
theorem gm_mul_self (a b : Fin 4) : (∑ σ, gm a σ * gm σ b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [gm]

/-! ## The flat / vacuum model -/

/-- Constant Minkowski metric (and its own inverse). -/
abbrev gW : Point 4 → Fin 4 → Fin 4 → ℝ := fun _ => gm
/-- Identity frame. -/
abbrev idW : Point 4 → Fin 4 → Fin 4 → ℝ := fun _ i k => if i = k then (1 : ℝ) else 0
/-- Vanishing stress-energy. -/
abbrev zeroT : Point 4 → Fin 4 → Fin 4 → ℝ := fun _ _ _ => 0
/-- Vanishing per-generator entropy / modular-energy / area. -/
abbrev zeroF : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ := fun _ _ _ => 0
/-- Vanishing per-generator derivative. -/
abbrev zeroD : Point 4 → (Fin 4 → ℝ) → ℝ := fun _ _ => 0

/-- **Satisfiability witness.** The 23 hypotheses of `qiqt_bekenstein_gives_gr` are jointly
satisfiable: the flat/vacuum model verifies every one, and the theorem then yields its conclusion
(the vacuum Einstein equation). Hence the headline theorem is non-vacuous. -/
theorem qiqt_bekenstein_gives_gr_satisfiable :
    ∃ Λ : ℝ, ∀ x μ ν,
      (2 * Real.pi) * zeroT x μ ν = einsteinTensor gW gW μ ν x + Λ * gW x μ ν :=
  QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr
    gW gW
    (fun _ a b => gm_symm a b) (fun _ a b => gm_symm a b)
    (fun _ a b => gm_mul_self a b)
    (fun _ _ => contDiff_const) (fun _ _ => contDiff_const)
    zeroT 1 1 (2 * Real.pi)
    one_ne_zero one_ne_zero (by rw [mul_one, div_one])
    (fun _ _ _ => rfl)
    idW idW
    (fun x i j => by fin_cases i <;> fin_cases j <;> simp)
    (fun x i j => by fin_cases i <;> fin_cases j <;> simp)
    (fun x i j => by fin_cases i <;> fin_cases j <;> simp [gm])
    zeroF zeroF zeroF zeroD zeroD zeroD
    (fun _ _ _ => hasDerivAt_const 0 0)
    (fun _ _ _ => hasDerivAt_const 0 0)
    (fun _ _ _ => hasDerivAt_const 0 0)
    (fun _ _ _ => Filter.Eventually.of_forall (fun _ => by norm_num))
    (fun _ _ _ => by norm_num)
    (fun _ _ _ _ => by norm_num)
    (fun _ _ _ => by norm_num)
    (fun x v _ => by simp [BL])
    (fun x v _ => by simp [BL, ricci_constMetric])
    (fun f hf => by
      -- the post-crux relation forces `f = 0`: `0 = ricci + f·g`, ricci = 0, g = gm with gm₀₀ = -1
      have hf0 : f = fun _ => (0 : ℝ) := by
        funext y
        have h := hf y 0 0
        simp only [ricci_constMetric, zero_add] at h
        -- h : (2*π) * zeroT y 0 0 = 0 + f y * gW y 0 0  →  0 = f y * gm 0 0 = f y * (-1)
        have : f y * gm 0 0 = 0 := by simpa using h.symm
        simp only [gm] at this
        norm_num at this
        linarith [this]
      subst hf0
      refine ⟨fun x ρ => ?_, ?_⟩
      · exact (PdiffAt_of_contDiff _ contDiff_const ρ x)
      · simp only [scalarCurv_constMetric, mul_zero, add_zero]; exact differentiable_const 0)
    (fun x ν => by
      have : (fun y a b => (2 * Real.pi) * zeroT y a b) = (fun _ _ _ => (0 : ℝ)) := by
        funext y a b; simp
      rw [this]; exact div02_zeroTensor gW gW ν x)

end QIQTH.QiqtGrWitness
