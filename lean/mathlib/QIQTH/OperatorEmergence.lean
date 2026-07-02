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
(`⟨f, X·g⟩ = ⟨∂f, g⟩`, whence `⟨α|a†|α⟩ = conj α·⟨α|α⟩`) — standard Bargmann calculus, cited; formalizing
the polynomial Bargmann inner product with its adjointness is a named follow-on. -/

/-- A linear observable EXPRESSION `Σ_λ u_λ a_λ + v_λ a†_λ` (the two-interpretation layer). -/
structure LinExpr where
  /-- annihilation coefficients -/
  u : Fin 2 → ℂ
  /-- creation coefficients -/
  v : Fin 2 → ℂ

/-- Interpretation 1: the polynomial operator. -/
noncomputable def LinExpr.toOp (E : LinExpr) : Op := linObs E.u E.v

/-- Interpretation 2: the normalized coherent expectation `⟨α|·|α⟩` — `u`-rule from the held
    `annih_coherent` eigenvalue relation, `v`-rule from Bargmann adjointness (cited). -/
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

end QIQTH.OperatorEmergence
