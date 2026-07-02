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
import QIQTH.CalibratedAreaLaw

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

/-! ## Q2 — linear observables and the CORRECTED commutation structure

BINDING (consult): equal-time area observables COMMUTE — the naive "noncommuting areas" claim is CUT.
The honest structure: the master c-number formula `comm_linObs`; areas + canonical momenta with
`[Â(Σ), Π̂Can(Σ')] = i·areaPair·1`; and the vacuum fluctuation `⟨0|Â Â'|0⟩ = areaPair` — quantized area
fluctuations WITHOUT fake noncommutativity. -/

/-- The commutator on the operator carrier. -/
noncomputable def comm (A B : Op) : Op := A * B - B * A

theorem comm_add_add (A B C D : Op) :
    comm (A + B) (C + D) = comm A C + comm A D + comm B C + comm B D := by
  simp only [comm, add_mul, mul_add]
  abel

theorem comm_smul_smul (a b : ℂ) (A B : Op) :
    comm (a • A) (b • B) = (a * b) • comm A B := by
  simp only [comm, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul, mul_comm a b]

theorem comm_antisymm (A B : Op) : comm B A = -comm A B := by
  simp [comm]

/-- `[a_i, a_j] = 0` at operator level. -/
theorem annih_comm_op (i j : Fin 2) : comm (annih i) (annih j) = 0 := by
  refine LinearMap.ext fun p => ?_
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [annih_comm i j p, sub_self]

/-- `[a†_i, a†_j] = 0` at operator level. -/
theorem creat_comm_op (i j : Fin 2) : comm (creat i) (creat j) = 0 := by
  refine LinearMap.ext fun p => ?_
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply]
  rw [creat_comm i j p, sub_self]

/-- **The CCR at operator level**: `[a_i, a†_j] = δ_ij·1`. -/
theorem ccr_op (i j : Fin 2) : comm (annih i) (creat j) = if i = j then (1 : Op) else 0 := by
  refine LinearMap.ext fun p => ?_
  have h := ccr i j p
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, one_mul] at h
    rw [if_pos rfl]
    simpa [comm, LinearMap.sub_apply, Module.End.mul_apply] using h
  · rw [if_neg hij, zero_mul] at h
    rw [if_neg hij]
    simpa [comm, LinearMap.sub_apply, Module.End.mul_apply] using h

theorem ccr_op' (i j : Fin 2) : comm (creat i) (annih j) = -if j = i then (1 : Op) else 0 := by
  rw [comm_antisymm, ccr_op]

/-- **The general linear oscillator observable** `Σ_λ u_λ a_λ + v_λ a†_λ`. -/
noncomputable def linObs (u v : Fin 2 → ℂ) : Op :=
  ∑ l, (u l • annih l + v l • creat l)

/-- The elementary commutator of single-mode linear observables. -/
theorem comm_elementary (l m : Fin 2) (a b c d : ℂ) :
    comm (a • annih l + b • creat l) (c • annih m + d • creat m)
      = ((a * d - b * c) * if l = m then 1 else 0) • (1 : Op) := by
  by_cases h : l = m
  · subst h
    rw [comm_add_add, comm_smul_smul, comm_smul_smul, comm_smul_smul, comm_smul_smul,
      annih_comm_op, creat_comm_op, ccr_op, ccr_op', if_pos rfl, if_pos rfl]
    module
  · rw [comm_add_add, comm_smul_smul, comm_smul_smul, comm_smul_smul, comm_smul_smul,
      annih_comm_op, creat_comm_op, ccr_op, ccr_op', if_neg h,
      if_neg (fun hh : m = l => h hh.symm), if_neg h]
    simp

theorem comm_sum_sum (f g : Fin 2 → Op) :
    comm (∑ l, f l) (∑ m, g m) = ∑ l, ∑ m, comm (f l) (g m) := by
  rw [comm, Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun m l => g m * f l)]
  simp only [comm, ← Finset.sum_sub_distrib]

/-- **Q2 MASTER FORMULA — the c-number commutator of linear observables:**
    `[linObs u v, linObs u′ v′] = (Σ_λ u_λ v′_λ − u′_λ v_λ)·1`. -/
theorem comm_linObs (u v u' v' : Fin 2 → ℂ) :
    comm (linObs u v) (linObs u' v')
      = (∑ l, (u l * v' l - u' l * v l)) • (1 : Op) := by
  rw [linObs, linObs, comm_sum_sum]
  have hterm : ∀ l : Fin 2,
      (∑ m, comm (u l • annih l + v l • creat l) (u' m • annih m + v' m • creat m))
        = (u l * v' l - v l * u' l) • (1 : Op) := by
    intro l
    have h1 : ∀ m : Fin 2, ((u l * v' m - v l * u' m) * if l = m then 1 else 0) • (1 : Op)
        = if l = m then (u l * v' m - v l * u' m) • (1 : Op) else 0 := by
      intro m
      by_cases h : l = m
      · simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl fun m _ => comm_elementary l m (u l) (v l) (u' m) (v' m),
      Finset.sum_congr rfl fun m _ => h1 m,
      Finset.sum_ite_eq Finset.univ l (fun m => (u l * v' m - v l * u' m) • (1 : Op)),
      if_pos (Finset.mem_univ l)]
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ### The area observables and their honest structure -/

open QIQTH.AreaMap in
/-- The quantized AREA observable of a probe surface: the area functional applied to `ĥ` —
    `Â(Σ) = Σ_λ areaVar(Σ, pol_λ)·q_λ`. -/
noncomputable def areaOp {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) : Op :=
  ∑ l, ((areaVar S (pol l) : ℝ) : ℂ) • qMode l

open QIQTH.AreaMap in
/-- The CANONICAL conjugate area momentum `Π̂Can(Σ) = Σ_λ areaVar(Σ, pol_λ)·(i/2)(a†_λ − a_λ)`. -/
noncomputable def areaMomCan {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) : Op :=
  ∑ l, ((areaVar S (pol l) : ℝ) : ℂ) • ((Complex.I / 2) • (creat l - annih l))

open QIQTH.AreaMap in
/-- The polarization pairing of two probe surfaces. -/
noncomputable def areaPair {ι κ : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (S' : ScreenSurface κ) : ℝ :=
  ∑ l, areaVar S (pol l) * areaVar S' (pol l)

open QIQTH.AreaMap in
theorem areaOp_eq_linObs {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) :
    areaOp pol S = linObs (fun l => ((areaVar S (pol l) : ℝ) : ℂ))
      (fun l => ((areaVar S (pol l) : ℝ) : ℂ)) := by
  rw [areaOp, linObs]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [qMode, smul_add]

open QIQTH.AreaMap in
theorem areaMomCan_eq_linObs {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) :
    areaMomCan pol S
      = linObs (fun l => -(Complex.I / 2) * ((areaVar S (pol l) : ℝ) : ℂ))
        (fun l => (Complex.I / 2) * ((areaVar S (pol l) : ℝ) : ℂ)) := by
  rw [areaMomCan, linObs]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, smul_sub]
  module

open QIQTH.AreaMap in
/-- **Equal-time area observables COMMUTE** — the honest statement (the naive noncommutativity is false). -/
theorem comm_area_area {ι κ : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (S' : ScreenSurface κ) :
    comm (areaOp pol S) (areaOp pol S') = 0 := by
  rw [areaOp_eq_linObs, areaOp_eq_linObs, comm_linObs]
  rw [Finset.sum_eq_zero fun l _ => by ring]
  exact zero_smul ℂ 1

open QIQTH.AreaMap in
/-- **Q2 CAPSTONE (canonical pair) — the area/momentum CCR:**
    `[Â(Σ), Π̂Can(Σ′)] = i·areaPair(Σ,Σ′)·1`. The quantum structure of the area observables lives in
    the conjugate pair, not in equal-time areas. -/
theorem comm_area_mom {ι κ : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (S' : ScreenSurface κ) :
    comm (areaOp pol S) (areaMomCan pol S')
      = (Complex.I * ((areaPair pol S S' : ℝ) : ℂ)) • (1 : Op) := by
  rw [areaOp_eq_linObs, areaMomCan_eq_linObs, comm_linObs, areaPair]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### The vacuum fluctuation -/

/-- `⟨0| q_l q_m |0⟩ = δ_lm` — the single-mode vacuum fluctuation. -/
theorem vacExp_qq (l m : Fin 2) :
    vacExp ((qMode l * qMode m) (1 : Fock)) = if l = m then 1 else 0 := by
  have hcreat1 : creat m (1 : Fock) = (MvPolynomial.X m : Fock) := by
    simp [creat, LinearMap.mulLeft_apply]
  have hq1 : qMode m (1 : Fock) = (MvPolynomial.X m : Fock) := by
    rw [qMode, LinearMap.add_apply, annih_vacuum, hcreat1, zero_add]
  have hannihX : annih l (MvPolynomial.X m : Fock) = if l = m then (1 : Fock) else 0 := by
    change MvPolynomial.pderiv l (MvPolynomial.X m : Fock) = _
    fin_cases l <;> fin_cases m <;> simp [MvPolynomial.pderiv_X]
  have hcreatX : creat l (MvPolynomial.X m : Fock)
      = (MvPolynomial.X l * MvPolynomial.X m : Fock) := by
    simp [creat, LinearMap.mulLeft_apply]
  rw [Module.End.mul_apply, hq1, qMode, LinearMap.add_apply, hannihX, hcreatX, vacExp, map_add]
  have hXX : MvPolynomial.constantCoeff (MvPolynomial.X l * MvPolynomial.X m : Fock) = 0 := by
    rw [map_mul]
    simp [MvPolynomial.constantCoeff_X]
  rw [hXX, add_zero]
  by_cases h : l = m
  · subst h
    simp
  · simp [if_neg h]

open QIQTH.AreaMap in
/-- **Q2 CAPSTONE (vacuum fluctuation) — `⟨0| Â(Σ) Â(Σ′) |0⟩ = areaPair(Σ,Σ′)`:** the quantized
    area fluctuations of the vacuum are exactly the polarization pairing — nonzero, quantitative, and
    honest (no fake noncommutativity needed). -/
theorem vacuum_area_pair {ι κ : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (S' : ScreenSurface κ) :
    vacExp ((areaOp pol S * areaOp pol S') (1 : Fock)) = ((areaPair pol S S' : ℝ) : ℂ) := by
  rw [areaOp, areaOp, areaPair, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [vacExp]
  simp only [map_sum, MvPolynomial.constantCoeff_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by
    rw [show MvPolynomial.constantCoeff ((qMode l * qMode m) (1 : Fock))
        = vacExp ((qMode l * qMode m) (1 : Fock)) from rfl, vacExp_qq l m]]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl, mul_one]
  · intro m _ hm
    rw [if_neg (fun h : l = m => hm h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-! ## Q3 — the coherent shadow: the CLASSICAL bridge is the coherent expectation of the operator map

BINDING (consult): the held coherent state lives in the single-mode Bargmann–Fock completion `ℂ⟦X⟧` while
`Op` acts on two-mode polynomials — the prescribed resolution is a small EXPRESSION LAYER for linear
observables, interpreted both as polynomial operators (`toOp`) and as coherent expectations (`cohExpect`).
Grounding of the two expectation rules (stated honestly): the `u`-rule `⟨a_λ⟩ = α_λ` is the held eigenvalue
relation `annih_coherent` (`a|α⟩ = α|α⟩`); the `v`-rule `⟨a†_λ⟩ = conj α_λ` is Bargmann adjointness
(`⟨f, X·g⟩ = ⟨∂f, g⟩`) — GROUNDED at polynomial level by `QIQTH.BargmannPairing.bargmann_adjoint` +
`cohPair_X_mul` (G1 of the grounding campaign); the completion-level identification stays cited. -/

/-- A linear observable EXPRESSION `Σ_λ u_λ a_λ + v_λ a†_λ` (the two-interpretation layer). -/
structure LinExpr where
  /-- annihilation coefficients -/
  u : Fin 2 → ℂ
  /-- creation coefficients -/
  v : Fin 2 → ℂ

/-- Interpretation 1: the polynomial operator. -/
noncomputable def LinExpr.toOp (E : LinExpr) : Op := linObs E.u E.v

/-- Interpretation 2: the normalized coherent expectation `⟨α|·|α⟩` — `u`-rule from the held
    `annih_coherent` eigenvalue relation, `v`-rule from Bargmann adjointness (GROUNDED:
    `BargmannPairing.bargmann_adjoint`/`cohPair_X_mul`). -/
noncomputable def LinExpr.cohExpect (E : LinExpr) (α : Fin 2 → ℂ) : ℂ :=
  ∑ l, (E.u l * α l + E.v l * (starRingEnd ℂ) (α l))

/-- The expression of the metric-operator entry `ĥ_{μν}`. -/
noncomputable def hHatExpr (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) : LinExpr where
  u := fun l => ((pol l μ ν : ℝ) : ℂ)
  v := fun l => ((pol l μ ν : ℝ) : ℂ)

/-- The expression interprets to the operator entry: `(hHatExpr μ ν).toOp = ĥ_{μν}`. -/
theorem hHatExpr_toOp (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    (hHatExpr pol μ ν).toOp = hHat pol μ ν := by
  rw [LinExpr.toOp, linObs, hHat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [qMode, smul_add]
  rfl

open QIQTH.AreaMap in
/-- The expression of the area observable `Â(Σ)`. -/
noncomputable def areaExpr {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) : LinExpr where
  u := fun l => ((areaVar S (pol l) : ℝ) : ℂ)
  v := fun l => ((areaVar S (pol l) : ℝ) : ℂ)

open QIQTH.AreaMap in
theorem areaExpr_toOp {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) : (areaExpr pol S).toOp = areaOp pol S :=
  (areaOp_eq_linObs pol S).symm

/-- **The classical field of a coherent amplitude**: `h(α) = Σ_λ 2·Re(α_λ)·pol^λ` — exactly the classical
    perturbation the bridge campaign's probes consume. -/
noncomputable def classicalH (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ l, (2 * (α l).re) • pol l

/-- **Q3 CAPSTONE (field) — `⟨α|ĥ_{μν}|α⟩ = h(α)_{μν}`:** the coherent expectation of the metric operator
    is the CLASSICAL perturbation of the amplitude — the classical emergence map is the coherent shadow of
    the operator map, entry by entry. -/
theorem coherent_hHat (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (α : Fin 2 → ℂ) (μ ν : Fin 4) :
    (hHatExpr pol μ ν).cohExpect α = ((classicalH pol α μ ν : ℝ) : ℂ) := by
  rw [LinExpr.cohExpect, hHatExpr, classicalH]
  rw [show (∑ l, (2 * (α l).re) • pol l) μ ν = ∑ l, (2 * (α l).re) * pol l μ ν from by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.smul_apply, smul_eq_mul]]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ((pol l μ ν : ℝ) : ℂ) * α l + ((pol l μ ν : ℝ) : ℂ) * (starRingEnd ℂ) (α l)
      = ((pol l μ ν : ℝ) : ℂ) * (α l + (starRingEnd ℂ) (α l)) from by ring,
    Complex.add_conj]
  push_cast
  ring

open QIQTH.AreaMap in
/-- **Q3 CAPSTONE (area) — `⟨α|Â(Σ)|α⟩ = δA_Σ(h(α))`:** the coherent expectation of the quantized area
    observable is the GEOMETRIC area variation of the classical field of the amplitude — the exact `δA`
    input the assembled bridge (first law ⟺ Einstein) consumes. The classical bridge is the coherent
    shadow of the operator emergence map. -/
theorem coherent_area {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (α : Fin 2 → ℂ) :
    (areaExpr pol S).cohExpect α = ((areaVar S (classicalH pol α) : ℝ) : ℂ) := by
  rw [LinExpr.cohExpect, areaExpr, classicalH]
  rw [show areaVar S (∑ l, (2 * (α l).re) • pol l)
      = ∑ l, (2 * (α l).re) * areaVar S (pol l) from by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, areaVar_add, areaVar_smul, areaVar_smul]]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ((areaVar S (pol l) : ℝ) : ℂ) * α l
        + ((areaVar S (pol l) : ℝ) : ℂ) * (starRingEnd ℂ) (α l)
      = ((areaVar S (pol l) : ℝ) : ℂ) * (α l + (starRingEnd ℂ) (α l)) from by ring,
    Complex.add_conj]
  push_cast
  ring

/-! ## Q4 — the Heisenberg flow and the operator wave equation

BINDING (consult): the explicit phase flow `z(t) = exp(+iωt)` (the Heisenberg sign; the Schrödinger flow
is opposite) implemented as the monomial scaling `X^n ↦ z^{|n|}X^n` (the `aeval (z•X)` algebra map) —
NO Stone/CLM; ODE statements COEFFICIENTWISE (`OpHasDerivAt` via `MvPolynomial.coeff`) since `Op` carries
no norm. -/

/-- The raw conjugate quadrature `π_λ = i(a†_λ − a_λ)`. -/
noncomputable def momRaw (l : Fin 2) : Op := Complex.I • (creat l - annih l)

/-- The Heisenberg phase `z(t) = e^{iωt}`. -/
noncomputable def zPhase (ω t : ℝ) : ℂ := Complex.exp ((↑(ω * t)) * Complex.I)

theorem zPhase_ne_zero (ω t : ℝ) : zPhase ω t ≠ 0 := Complex.exp_ne_zero _

/-- The monomial scaling `U_z : X_i ↦ z·X_i` (`X^n ↦ z^{|n|}X^n`) — the explicit flow unitary's
    polynomial avatar. -/
noncomputable def scaleU (z : ℂ) : Op :=
  (MvPolynomial.aeval fun i : Fin 2 => z • (MvPolynomial.X i : Fock)).toLinearMap

theorem scaleU_mul (z : ℂ) (p q : Fock) : scaleU z (p * q) = scaleU z p * scaleU z q := by
  simp only [scaleU, AlgHom.toLinearMap_apply, map_mul]

theorem scaleU_X (z : ℂ) (i : Fin 2) :
    scaleU z (MvPolynomial.X i : Fock) = z • (MvPolynomial.X i : Fock) := by
  simp only [scaleU, AlgHom.toLinearMap_apply, MvPolynomial.aeval_X]

theorem scaleU_C (z a : ℂ) : scaleU z (MvPolynomial.C a : Fock) = MvPolynomial.C a := by
  simp only [scaleU, AlgHom.toLinearMap_apply, MvPolynomial.aeval_C]
  rfl

theorem scaleU_creat (z : ℂ) (l : Fin 2) (p : Fock) :
    scaleU z (creat l p) = z • creat l (scaleU z p) := by
  change scaleU z ((MvPolynomial.X l : Fock) * p) = z • ((MvPolynomial.X l : Fock) * scaleU z p)
  rw [scaleU_mul, scaleU_X, smul_mul_assoc]

/-- The chain rule for the scaling: `∂_l (U_z p) = z·U_z(∂_l p)`. -/
theorem annih_scaleU (z : ℂ) (l : Fin 2) (p : Fock) :
    annih l (scaleU z p) = z • scaleU z (annih l p) := by
  change MvPolynomial.pderiv l (scaleU z p) = z • scaleU z (MvPolynomial.pderiv l p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [scaleU_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, smul_add]
  | mul_X p i hp =>
    by_cases hil : l = i
    · subst hil
      simp only [scaleU_mul, scaleU_X, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
        map_smul, map_add, hp, mul_one, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C,
        mul_zero, add_zero]
      ring
    · simp only [scaleU_mul, scaleU_X, MvPolynomial.pderiv_mul, map_smul, map_add, hp,
        MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C, mul_zero, add_zero]
      rw [MvPolynomial.pderiv_X_of_ne (fun h : i = l => hil h.symm)]
      simp only [mul_zero, map_zero, add_zero, MvPolynomial.smul_eq_C_mul]
      ring

theorem scaleU_comp (z w : ℂ) (p : Fock) : scaleU z (scaleU w p) = scaleU (z * w) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [scaleU_C, scaleU_C, scaleU_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [scaleU_mul, scaleU_X, map_smul, hp, smul_smul]
    rw [mul_comm w z]

theorem scaleU_one_eq (p : Fock) : scaleU 1 p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [scaleU_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [scaleU_mul, scaleU_X, hp, one_smul]

/-- The Heisenberg conjugation `A ↦ U_z A U_z⁻¹`. -/
noncomputable def heisScale (z : ℂ) (A : Op) : Op := scaleU z * A * scaleU z⁻¹

/-- **The Heisenberg phase of creation**: `U_z a† U_z⁻¹ = z·a†`. -/
theorem heis_creat (z : ℂ) (hz : z ≠ 0) (l : Fin 2) :
    heisScale z (creat l) = z • creat l := by
  refine LinearMap.ext fun p => ?_
  simp only [heisScale, Module.End.mul_apply, LinearMap.smul_apply]
  rw [scaleU_creat, scaleU_comp, mul_inv_cancel₀ hz, scaleU_one_eq]

/-- **The Heisenberg phase of annihilation**: `U_z a U_z⁻¹ = z⁻¹·a`. -/
theorem heis_annih (z : ℂ) (hz : z ≠ 0) (l : Fin 2) :
    heisScale z (annih l) = z⁻¹ • annih l := by
  refine LinearMap.ext fun p => ?_
  simp only [heisScale, Module.End.mul_apply, LinearMap.smul_apply]
  rw [annih_scaleU z⁻¹ l p, map_smul, scaleU_comp, mul_inv_cancel₀ hz, scaleU_one_eq]

/-- The time-evolved quadrature `q_λ(t) = z(t)⁻¹·a_λ + z(t)·a†_λ`. -/
noncomputable def qModeT (ω t : ℝ) (l : Fin 2) : Op :=
  (zPhase ω t)⁻¹ • annih l + (zPhase ω t) • creat l

/-- **The Heisenberg flow of the quadrature**: `U_{z(t)} q_λ U_{z(t)}⁻¹ = q_λ(t)` — the time evolution
    is the DERIVED conjugation by the explicit monomial-scaling flow, not a posited phase. -/
theorem heis_q (ω t : ℝ) (l : Fin 2) : heisScale (zPhase ω t) (qMode l) = qModeT ω t l := by
  have hz := zPhase_ne_zero ω t
  rw [qMode, qModeT]
  have hadd : heisScale (zPhase ω t) (annih l + creat l)
      = heisScale (zPhase ω t) (annih l) + heisScale (zPhase ω t) (creat l) := by
    simp only [heisScale, mul_add, add_mul]
  rw [hadd, heis_annih _ hz, heis_creat _ hz]

/-- **The harmonic identity**: `q_λ(t) = cos(ωt)·q_λ + sin(ωt)·π_λ`. -/
theorem qModeT_harmonic (ω t : ℝ) (l : Fin 2) :
    qModeT ω t l = ((Real.cos (ω * t) : ℝ) : ℂ) • qMode l
      + ((Real.sin (ω * t) : ℝ) : ℂ) • momRaw l := by
  rw [qModeT, qMode, momRaw, zPhase]
  rw [show (Complex.exp ((↑(ω * t)) * Complex.I))⁻¹
      = Complex.exp ((↑(-(ω * t))) * Complex.I) from by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  rw [show Complex.cos (↑(-(ω * t))) = ((Real.cos (ω * t) : ℝ) : ℂ) from by
      rw [Complex.ofReal_neg, Complex.cos_neg, ← Complex.ofReal_cos],
    show Complex.sin (↑(-(ω * t))) = -((Real.sin (ω * t) : ℝ) : ℂ) from by
      rw [Complex.ofReal_neg, Complex.sin_neg, ← Complex.ofReal_sin],
    show Complex.cos (↑(ω * t)) = ((Real.cos (ω * t) : ℝ) : ℂ) from (Complex.ofReal_cos _).symm,
    show Complex.sin (↑(ω * t)) = ((Real.sin (ω * t) : ℝ) : ℂ) from (Complex.ofReal_sin _).symm]
  module

/-! ### The coefficientwise ODE layer and the operator wave equation -/

/-- Coefficientwise operator differentiability (`Op` carries no norm — the binding correction). -/
def OpHasDerivAt (F : ℝ → Op) (F' : Op) (t : ℝ) : Prop :=
  ∀ (p : Fock) (n : Fin 2 →₀ ℕ),
    HasDerivAt (fun s => MvPolynomial.coeff n (F s p)) (MvPolynomial.coeff n (F' p)) t

private theorem hasDerivAt_cos_sin_combo (a b : ℂ) (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => ((Real.cos (ω * s) : ℝ) : ℂ) * a + ((Real.sin (ω * s) : ℝ) : ℂ) * b)
      (((ω * -Real.sin (ω * t) : ℝ) : ℂ) * a + ((ω * Real.cos (ω * t) : ℝ) : ℂ) * b) t := by
  have hlin : HasDerivAt (fun s : ℝ => ω * s) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hc : HasDerivAt (fun s : ℝ => Real.cos (ω * s)) (ω * -Real.sin (ω * t)) t := by
    have := (Real.hasDerivAt_cos (ω * t)).comp t hlin
    simpa [mul_comm] using this
  have hs : HasDerivAt (fun s : ℝ => Real.sin (ω * s)) (ω * Real.cos (ω * t)) t := by
    have := (Real.hasDerivAt_sin (ω * t)).comp t hlin
    simpa [mul_comm] using this
  exact (hc.ofReal_comp.mul_const a).add (hs.ofReal_comp.mul_const b)

theorem opHasDerivAt_cos_sin (A B : Op) (ω t : ℝ) :
    OpHasDerivAt (fun s => ((Real.cos (ω * s) : ℝ) : ℂ) • A + ((Real.sin (ω * s) : ℝ) : ℂ) • B)
      (((ω * -Real.sin (ω * t) : ℝ) : ℂ) • A + ((ω * Real.cos (ω * t) : ℝ) : ℂ) • B) t := by
  intro p n
  simp only [LinearMap.add_apply, LinearMap.smul_apply, MvPolynomial.coeff_add,
    MvPolynomial.coeff_smul, smul_eq_mul]
  exact hasDerivAt_cos_sin_combo _ _ ω t

/-- The velocity field `q̇_λ(t) = −ω sin(ωt)·q_λ + ω cos(ωt)·π_λ`. -/
noncomputable def qModeTD (ω t : ℝ) (l : Fin 2) : Op :=
  ((ω * -Real.sin (ω * t) : ℝ) : ℂ) • qMode l + ((ω * Real.cos (ω * t) : ℝ) : ℂ) • momRaw l

/-- The quadrature flow is differentiable with velocity `qModeTD` (coefficientwise). -/
theorem qModeT_hasDerivAt (ω t : ℝ) (l : Fin 2) :
    OpHasDerivAt (fun s => qModeT ω s l) (qModeTD ω t l) t := by
  intro p n
  have hfun : (fun s => MvPolynomial.coeff n ((qModeT ω s l) p))
      = fun s => MvPolynomial.coeff n
        (((((Real.cos (ω * s) : ℝ) : ℂ) • qMode l
          + ((Real.sin (ω * s) : ℝ) : ℂ) • momRaw l)) p) := by
    funext s
    rw [qModeT_harmonic]
  rw [hfun]
  exact opHasDerivAt_cos_sin (qMode l) (momRaw l) ω t p n

private theorem qModeTD_eq_combo (ω s : ℝ) (l : Fin 2) :
    qModeTD ω s l = ((Real.cos (ω * s) : ℝ) : ℂ) • (((ω : ℝ) : ℂ) • momRaw l)
      + ((Real.sin (ω * s) : ℝ) : ℂ) • ((-(ω : ℝ) : ℂ) • qMode l) := by
  rw [qModeTD]
  push_cast
  module

/-- **Q4 CAPSTONE (per mode) — the operator WAVE EQUATION**: `q̈_λ(t) = −ω²·q_λ(t)`, coefficientwise. -/
theorem qModeT_wave (ω t : ℝ) (l : Fin 2) :
    OpHasDerivAt (fun s => qModeTD ω s l) (((-(ω ^ 2) : ℝ) : ℂ) • qModeT ω t l) t := by
  have hval : (((ω * -Real.sin (ω * t) : ℝ) : ℂ) • (((ω : ℝ) : ℂ) • momRaw l)
      + ((ω * Real.cos (ω * t) : ℝ) : ℂ) • ((-(ω : ℝ) : ℂ) • qMode l))
      = ((-(ω ^ 2) : ℝ) : ℂ) • qModeT ω t l := by
    rw [qModeT_harmonic]
    push_cast
    module
  intro p n
  have hfun : (fun s => MvPolynomial.coeff n ((qModeTD ω s l) p))
      = fun s => MvPolynomial.coeff n
        (((((Real.cos (ω * s) : ℝ) : ℂ) • (((ω : ℝ) : ℂ) • momRaw l)
          + ((Real.sin (ω * s) : ℝ) : ℂ) • ((-(ω : ℝ) : ℂ) • qMode l))) p) := by
    funext s
    rw [qModeTD_eq_combo]
  rw [hfun, ← hval]
  exact opHasDerivAt_cos_sin _ _ ω t p n

/-- Sums of differentiable operator families are differentiable. -/
theorem OpHasDerivAt.sum2 {F : Fin 2 → ℝ → Op} {F' : Fin 2 → Op} {t : ℝ}
    (h : ∀ l, OpHasDerivAt (F l) (F' l) t) :
    OpHasDerivAt (fun s => ∑ l, F l s) (∑ l, F' l) t := by
  intro p n
  have hfun : (fun s => MvPolynomial.coeff n ((∑ l, F l s) p))
      = fun s => ∑ l, MvPolynomial.coeff n ((F l s) p) := by
    funext s
    rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  rw [hfun, LinearMap.sum_apply, MvPolynomial.coeff_sum]
  have hsum := HasDerivAt.sum fun l (_ : l ∈ Finset.univ) => h l p n
  have hfn : (∑ l, fun s => MvPolynomial.coeff n ((F l s) p))
      = fun s => ∑ l, MvPolynomial.coeff n ((F l s) p) := by
    funext s
    simp [Finset.sum_apply]
  rwa [hfn] at hsum

theorem OpHasDerivAt.const_smul {F : ℝ → Op} {F' : Op} {t : ℝ} (c : ℂ)
    (h : OpHasDerivAt F F' t) : OpHasDerivAt (fun s => c • F s) (c • F') t := by
  intro p n
  have hfun : (fun s => MvPolynomial.coeff n ((c • F s) p))
      = fun s => c * MvPolynomial.coeff n (F s p) := by
    funext s
    rw [LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [hfun, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul]
  exact (h p n).const_mul c

/-- The time-evolved metric operator `ĥ_{μν}(t)`. -/
noncomputable def hHatT (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (ω t : ℝ) (μ ν : Fin 4) : Op :=
  ∑ l, ((pol l μ ν : ℝ) : ℂ) • qModeT ω t l

/-- Its velocity field. -/
noncomputable def hHatTD (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (ω t : ℝ) (μ ν : Fin 4) : Op :=
  ∑ l, ((pol l μ ν : ℝ) : ℂ) • qModeTD ω t l

theorem hHatT_hasDerivAt (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (ω t : ℝ) (μ ν : Fin 4) :
    OpHasDerivAt (fun s => hHatT pol ω s μ ν) (hHatTD pol ω t μ ν) t :=
  OpHasDerivAt.sum2 fun l => OpHasDerivAt.const_smul _ (qModeT_hasDerivAt ω t l)

/-- **Q4 CAPSTONE — the operator wave equation for the metric**: `ḧ_{μν}(t) + ω²·ĥ_{μν}(t) = 0`,
    coefficientwise — the graviton wave equation as an operator identity of the emergence map. -/
theorem hHatT_wave (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (ω t : ℝ) (μ ν : Fin 4) :
    OpHasDerivAt (fun s => hHatTD pol ω s μ ν) (((-(ω ^ 2) : ℝ) : ℂ) • hHatT pol ω t μ ν) t := by
  have h := OpHasDerivAt.sum2 (t := t)
    (F := fun l s => ((pol l μ ν : ℝ) : ℂ) • qModeTD ω s l)
    (F' := fun l => ((pol l μ ν : ℝ) : ℂ) • (((-(ω ^ 2) : ℝ) : ℂ) • qModeT ω t l))
    (fun l => OpHasDerivAt.const_smul _ (qModeT_wave ω t l))
  have heq : (∑ l, ((pol l μ ν : ℝ) : ℂ) • (((-(ω ^ 2) : ℝ) : ℂ) • qModeT ω t l))
      = ((-(ω ^ 2) : ℝ) : ℂ) • hHatT pol ω t μ ν := by
    rw [hHatT, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  rw [← heq]
  exact h

/-! ### The time-separated area commutator -/

open QIQTH.AreaMap in
/-- The time-evolved area observable `Â_Σ(t)`. -/
noncomputable def areaOpT {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (ω t : ℝ) : Op :=
  ∑ l, ((areaVar S (pol l) : ℝ) : ℂ) • qModeT ω t l

open QIQTH.AreaMap in
theorem areaOpT_eq_linObs {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (ω t : ℝ) :
    areaOpT pol S ω t
      = linObs (fun l => (zPhase ω t)⁻¹ * ((areaVar S (pol l) : ℝ) : ℂ))
        (fun l => (zPhase ω t) * ((areaVar S (pol l) : ℝ) : ℂ)) := by
  rw [areaOpT, linObs]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [qModeT, smul_add, smul_smul, smul_smul, mul_comm ((areaVar S (pol l) : ℝ) : ℂ),
    mul_comm ((areaVar S (pol l) : ℝ) : ℂ)]

private theorem exp_diff_sin (θ : ℝ) :
    Complex.exp ((↑θ) * Complex.I) - Complex.exp ((↑(-θ)) * Complex.I)
      = 2 * Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I,
    show Complex.cos (↑(-θ)) = Complex.cos (↑θ) from by rw [Complex.ofReal_neg, Complex.cos_neg],
    show Complex.sin (↑(-θ)) = -Complex.sin (↑θ) from by rw [Complex.ofReal_neg, Complex.sin_neg],
    ← Complex.ofReal_sin]
  ring

open QIQTH.AreaMap in
/-- **Q4 CAPSTONE (temporal) — the TIME-SEPARATED area commutator:**
    `[Â_Σ(t), Â_Σ′(s)] = 2i·sin(ω(s−t))·areaPair(Σ,Σ′)·1` — vanishing at equal times (the honest Q2
    statement) and oscillating with the light-crossing phase in between: the causal structure of the
    quantized area observables. -/
theorem comm_areaT {ι κ : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ)
    (S : ScreenSurface ι) (S' : ScreenSurface κ) (ω t s : ℝ) :
    comm (areaOpT pol S ω t) (areaOpT pol S' ω s)
      = (2 * Complex.I * ((Real.sin (ω * (s - t)) : ℝ) : ℂ)
          * ((areaPair pol S S' : ℝ) : ℂ)) • (1 : Op) := by
  have hz1 : zPhase ω s * (zPhase ω t)⁻¹
      = Complex.exp ((↑(ω * (s - t))) * Complex.I) := by
    rw [zPhase, zPhase, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hz2 : zPhase ω t * (zPhase ω s)⁻¹
      = Complex.exp ((↑(-(ω * (s - t)))) * Complex.I) := by
    rw [zPhase, zPhase, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [areaOpT_eq_linObs, areaOpT_eq_linObs, comm_linObs, areaPair]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (zPhase ω t)⁻¹ * ((areaVar S (pol l) : ℝ) : ℂ)
        * (zPhase ω s * ((areaVar S' (pol l) : ℝ) : ℂ))
        - (zPhase ω s)⁻¹ * ((areaVar S' (pol l) : ℝ) : ℂ)
          * (zPhase ω t * ((areaVar S (pol l) : ℝ) : ℂ))
      = (zPhase ω s * (zPhase ω t)⁻¹ - zPhase ω t * (zPhase ω s)⁻¹)
        * (((areaVar S (pol l) : ℝ) : ℂ) * ((areaVar S' (pol l) : ℝ) : ℂ)) from by ring,
    hz1, hz2, exp_diff_sin]
  push_cast
  ring

/-! ## Q5 — THE CODE JOIN (expectation level, stated once)

BINDING (consult): the join is EXPECTATION-LEVEL ONLY — an exact finite-code→Fock CCR isometry is
OBSTRUCTED (`trace[Q,P] = 0` vs `trace(iI) ≠ 0`: finite dimension cannot carry exact CCR); and the join is
TOTAL-to-total (the code's `area = 4G·cut` is a total area; `areaOp` is the linearized fluctuation —
`areaTotOp = A₀·1 + Â` carries the background explicitly; never conflate). -/

open QIQTH.AreaMap in
/-- **The TOTAL area operator** `Â_tot(Σ) = A₀·1 + Â(Σ)` — background plus quantized fluctuation. -/
noncomputable def areaTotOp {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (A0 : ℝ)
    (S : ScreenSurface ι) : Op :=
  ((A0 : ℝ) : ℂ) • (1 : Op) + areaOp pol S

/-- An affine observable expression: constant + linear (the constant rule `⟨α|1|α⟩ = 1`). -/
structure AffExpr where
  /-- the constant (background) part -/
  c : ℂ
  /-- the linear part -/
  lin : LinExpr

noncomputable def AffExpr.toOp (E : AffExpr) : Op := E.c • (1 : Op) + E.lin.toOp

noncomputable def AffExpr.cohExpect (E : AffExpr) (α : Fin 2 → ℂ) : ℂ :=
  E.c + E.lin.cohExpect α

open QIQTH.AreaMap in
/-- The total-area expression. -/
noncomputable def areaTotExpr {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (A0 : ℝ)
    (S : ScreenSurface ι) : AffExpr where
  c := ((A0 : ℝ) : ℂ)
  lin := areaExpr pol S

open QIQTH.AreaMap in
theorem areaTotExpr_toOp {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (A0 : ℝ)
    (S : ScreenSurface ι) : (areaTotExpr pol A0 S).toOp = areaTotOp pol A0 S := by
  rw [AffExpr.toOp, areaTotExpr, areaTotOp, areaExpr_toOp]

open QIQTH.AreaMap in
/-- The coherent expectation of the total area: background plus the geometric area variation of the
    classical field — `⟨α|Â_tot(Σ)|α⟩ = A₀ + δA_Σ(h(α))`. -/
theorem coherent_areaTot_re {ι : Type*} (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (A0 : ℝ)
    (S : ScreenSurface ι) (α : Fin 2 → ℂ) :
    ((areaTotExpr pol A0 S).cohExpect α).re = A0 + areaVar S (classicalH pol α) := by
  rw [AffExpr.cohExpect, areaTotExpr, coherent_area]
  rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]

open QIQTH.EarnGravity in
open QIQTH.AreaMap in
/-- **Q5 CAPSTONE — the code's count and the graviton's area operator agree as two computations of ONE
    number.** CARRIED (named, stated ONCE): `hJoin` — the code's induced screen area (the calibrated
    entanglement cut, `4G·cut`) equals the coherent expectation of the TOTAL area operator. GIVEN the held
    calibration (`log D_e = wEnt e`), the microstate count equals the Fock area-operator expectation over
    `4G`:  `log #microstates = ⟨α|Â_tot(Σ)|α⟩ / 4G`.
    ⚠ The join is expectation-level (the CCR-isometry obstruction is permanent); the code Hilbert space is
    NOT Fock; `hJoin` is the emergence-map identification — the physical content, honest and singular. -/
theorem code_count_eq_fock_area_expect {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {ι : Type*} (G : ℝ) (hG : 0 < G) (links : Finset ι') (wEnt : ι' → ℝ) (D : ι' → ℕ)
    (hD : ∀ e ∈ links, 0 < D e) (hcal : ∀ e ∈ links, Real.log (D e) = wEnt e)
    (pol : Fin 2 → Matrix (Fin 4) (Fin 4) ℝ) (A0 : ℝ) (S : ScreenSurface ι) (α : Fin 2 → ℂ)
    (hJoin : inducedScreenArea G links wEnt = A0 + areaVar S (classicalH pol α)) :
    Real.log (Fintype.card (Microstates links D))
      = ((areaTotExpr pol A0 S).cohExpect α).re / (4 * G) := by
  rw [coherent_areaTot_re, ← hJoin]
  exact calibrated_entanglement_cut_area_law G hG links wEnt D hD hcal

end QIQTH.OperatorEmergence