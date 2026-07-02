/-
  Q1 (OPERATOR_EMERGENCE_PLAN.md) — the generalized decoder + the operator graviton.

  The first rung of the operator emergence map ("graviton = quantized area fluctuation of the code",
  theorem-shaped). BINDING (consult): the carrier is `Op := Module.End ℂ Fock` on the POLYNOMIAL Bargmann–Fock
  space (never a CLM on a completion — creation is unbounded there); the decoder is generalized ONCE over an
  arbitrary ℂ-module and instantiated at `Op`; the Hermitian field uses REAL plus/cross polarization data.

  • `areaDataM` / `reconstructM` — the ray-probe area data and the decoder, over ANY ℂ-module `M`
    (`M = ℝ`-shadow: the held classical `reconstruct`; `M = Op`: the operator version);
  • `reconstruct_areaDataM` — the decoder inverts the area map over any ℂ-module (the lift of the held
    `reconstruct_areaVar`, same basis-level computation);
  • `qMode λ = a_λ + a_λ†` — the Hermitian mode quadrature on the held CCR algebra;
  • `hHat pol` — the operator-valued metric perturbation `ĥ_{μν} = Σ_λ pol^λ_{μν}·q_λ` (fixed momentum,
    real symmetric plus/cross `pol`);
  • **`reconstruct_hHat`** — Q1 CAPSTONE: the decoder inverts the QUANTIZED area map at operator level —
    `reconstructM (areaDataM ĥ) = ĥ`. The metric operator is a function of its own area-fluctuation
    observables, entrywise in `End(Fock)`.

  ⚠ Honest scope: fixed momentum `k`, two polarizations, linearized, free; the code join is Q5
  (expectation-level ONLY — the finite-code CCR isometry is obstructed); NOT QG. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.GravitonQuantization
import QIQTH.AreaDecoder

namespace QIQTH.OperatorEmergence

open QIQTH.GravitonQuant QIQTH.AreaMap

/-- The operator carrier: linear endomorphisms of the polynomial Bargmann–Fock space (the honest
    unbounded-operator domain — polynomials are preserved by `creat`/`annih`). -/
abbrev Op := Module.End ℂ QIQTH.GravitonQuant.Fock

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The `M`-valued ray-probe area datum: `A(v) = ½ Σ_{μν} v_μ v_ν H_{μν}` (the `areaVar (raySurf v)`
    quadratic form, over any ℂ-module). -/
noncomputable def areaDataM (H : Matrix (Fin 4) (Fin 4) M) (v : Fin 4 → ℝ) : M :=
  (1 / 2 : ℂ) • ∑ μ, ∑ ν, ((v μ * v ν : ℝ) : ℂ) • H μ ν

/-- The `M`-valued decoder: `h_ii = 2A(e_i)`, `h_ij = A(e_i+e_j) − A(e_i) − A(e_j)`. -/
noncomputable def reconstructM (A : (Fin 4 → ℝ) → M) : Matrix (Fin 4) (Fin 4) M :=
  Matrix.of fun i j =>
    if i = j then (2 : ℂ) • A (basisVec i)
    else A (fun k => basisVec i k + basisVec j k) - A (basisVec i) - A (basisVec j)

/-- **The generalized decoder identity**: over any ℂ-module, the decoder inverts the ray-probe area map on
    the symmetric sector — the module-level lift of the held classical `reconstruct_areaVar`. -/
theorem reconstruct_areaDataM (H : Matrix (Fin 4) (Fin 4) M)
    (hSymm : ∀ i j, H i j = H j i) :
    reconstructM (areaDataM H) = H := by
  ext i j
  simp only [reconstructM, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, areaDataM]
    fin_cases i <;> (simp [Fin.sum_univ_four, basisVec]; try module)
  · rw [if_neg hij, areaDataM, areaDataM, areaDataM]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [Fin.sum_univ_four, basisVec]
           first
             | module
             | (rw [hSymm 1 0]; module)
             | (rw [hSymm 2 0]; module)
             | (rw [hSymm 3 0]; module)
             | (rw [hSymm 2 1]; module)
             | (rw [hSymm 3 1]; module)
             | (rw [hSymm 3 2]; module))

/-- The Hermitian mode quadrature `q_λ = a_λ + a_λ†` on the held Bargmann–Fock CCR algebra. -/
noncomputable def qMode (l : Fin 2) : Op := annih l + creat l

/-- **The operator-valued metric perturbation** `ĥ_{μν} = Σ_λ pol^λ_{μν} · q_λ` (fixed momentum, real
    plus/cross polarization data `pol`). -/
noncomputable def hHat (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) Op :=
  Matrix.of fun μ ν => ∑ l, ((pol l μ ν : ℝ) : ℂ) • qMode l

/-- `ĥ` is symmetric when the polarization data is. -/
theorem hHat_symm (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (hPol : ∀ l, (pol l).IsSymm) (μ ν : Fin 4) :
    hHat pol μ ν = hHat pol ν μ := by
  simp only [hHat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hPol l).apply ν μ]

/-- **Q1 CAPSTONE — the decoder inverts the QUANTIZED area map at operator level:** the operator-valued
    metric perturbation is reconstructed exactly from its own area-fluctuation data,
    `reconstructM (areaDataM ĥ) = ĥ`, entrywise in `End(Fock)`. The classical emergence map's inversion
    (`reconstruct_areaVar`) lifts verbatim to the quantized field. -/
theorem reconstruct_hHat (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (hPol : ∀ l, (pol l).IsSymm) :
    reconstructM (areaDataM (hHat pol)) = hHat pol :=
  reconstruct_areaDataM (hHat pol) (hHat_symm pol hPol)

end QIQTH.OperatorEmergence
