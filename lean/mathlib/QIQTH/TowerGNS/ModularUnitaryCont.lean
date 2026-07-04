/-
  THE RESOLVENT CAMPAIGN — R5 (THE_RESOLVENT_PLAN.md) — **strong continuity of `Δ^{it}`
  plus the honesty pair `U_tΩ = Ω` and `E({0}) = 0` — still NO claim `U = towerFlow`.**

  R4 delivered the tower modular unitary group `U_t = towerModUnitary t = u_t(R)` (the
  bounded Borel FC of the resolvent at the junk-value-1 symbol `u_t(r) = ((1−r)/r)^{it}`
  on `(0,1)`): group laws, adjoint law, unitarity, isometry, and the inner cocycle
  `⟪U_a x, U_b y⟫ = ⟪x, U_{b−a} y⟫`.  This file completes the textbook package:

  * **STRONG CONTINUITY** `t ↦ U_t x` (`towerModUnitary_stronglyContinuous`) — the
    line-by-line port of the compiled `modUnitary_stronglyContinuous` template
    (StandardSubspaceModularFlow.lean): the sequential criterion, the dominated-convergence
    engine `tendsto_inner_boundedFC_of_dominated` (`u_{a−t_n} → 1` pointwise, all bounded
    by `1`), and the norm-square identity
    `‖U_{t_n}x − U_ax‖² = 2‖x‖² − 2·Re⟪x, U_{a−t_n}x⟫` from the R4 cocycle + isometry.
    (Norm continuity FAILS near the spectral endpoints — strong is the true statement.)

  * **THE HONESTY PAIR** — the two facts certifying `U_t` genuinely represents
    `δ^{it} = ((1−r)/r)^{it}` and fixes the state:
      - `towerModUnitary_cyclicVec`: `U_tΩ = Ω` — `RΩ = ½Ω` (R2) makes `Ω` an eigenvector
        at `r = ½ ∈ σ(R)`, and the R3 eigenvector calculus `f(R)x = f(r)•x` evaluates the
        symbol: `u_t(½) = exp(i·t·log((1−½)/½)) = exp(i·t·log 1) = 1`.
      - `towerResolvent_pvm_atom_zero`: `E({0}) = 0` — no spectral weight at the junk
        point, forced by kernel triviality (R1 `towerResolvent_injective`) through the R3
        kernel-atom lemma.

  NOT here (deliberately): commutation with `R`/`Δ` (R6), `Δ^{1/2}`, `J`, KMS, Tomita,
  `towerGen = log Δ`, any claim that `towerModUnitary` equals the transported `towerFlow`
  (the exponential-recovery wall — the named next campaign), any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ModularUnitary

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.SpectralTheorem
open scoped InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### R5.1 — `t`-continuity of the symbol (at each fixed `r`)

    The pointwise input to strong continuity: for fixed `r` the map `t ↦ u_t(r)` is
    continuous — on the bulk branch it is `exp` of a continuous purely imaginary linear
    function of `t`; on the junk branch it is the constant `1`. -/

/-- `t ↦ u_t(r)` is continuous (for each fixed `r`) — the pointwise input to strong
    continuity (verbatim `modChar_continuous` port). -/
theorem towerModChar_continuous (r : ℝ) : Continuous (fun t => towerModChar t r) := by
  unfold towerModChar
  by_cases h : r ∈ Set.Ioo (0 : ℝ) 1
  · simp only [Set.piecewise_eq_of_mem _ _ _ h]
    exact Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  · simp only [Set.piecewise_eq_of_notMem _ _ _ h]
    exact continuous_const

/-! ### R5.2 — ★ strong continuity of `t ↦ U_t x` ★ -/

/-- **★ STRONG CONTINUITY:** `t ↦ U_t x` is continuous — so `Δ^{it} := towerModUnitary`
    is a STRONGLY CONTINUOUS one-parameter unitary group (the full textbook definition;
    norm continuity fails near the spectral endpoints).  Proof (the verbatim
    `modUnitary_stronglyContinuous` port): sequential criterion + the bounded-Borel-FC
    dominated-convergence engine, via
    `‖U_{t_n}x − U_ax‖² = 2‖x‖² − 2·Re⟪x, U_{a−t_n}x⟫ → 0` since `u_{a−t_n} → 1`
    pointwise (all bounded by `1`). -/
theorem towerModUnitary_stronglyContinuous (x : TowerGNS L ω β) :
    Continuous (fun t => towerModUnitary L ω β t x) := by
  -- the real inner product (`re ⟪·,·⟫_ℂ`), kept LOCAL to this proof (project precedent:
  -- ModularSurjective.exists_re_pairing) — needed only for `norm_sub_sq_real`
  letI : InnerProductSpace ℝ (TowerGNS L ω β) :=
    InnerProductSpace.rclikeToReal ℂ (TowerGNS L ω β)
  rw [continuous_iff_seqContinuous]
  intro u a hu
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ha : IsSelfAdjoint (towerResolvent L ω β) := towerResolvent_isSelfAdjoint L ω β
  set P := PVM_of_selfAdjoint (towerResolvent L ω β) ha with hP
  -- pointwise convergence `u_{a−u n} → 1`
  have hptw : ∀ r, Filter.Tendsto (fun n => towerModSpecFun L ω β (a - u n) r)
      Filter.atTop (nhds ((fun _ => (1 : ℂ)) r)) := by
    intro r
    have h0 : Filter.Tendsto (fun n => a - u n) Filter.atTop (nhds 0) := by
      simpa using hu.const_sub a
    have hc := ((towerModChar_continuous r.val).tendsto 0).comp h0
    simpa [towerModSpecFun, towerModChar_zero] using hc
  -- inner products converge: `⟪x, U_{a−u n}x⟫ → ⟪x, x⟫`
  have hinner : Filter.Tendsto
      (fun n => inner ℂ x (towerModUnitary L ω β (a - u n) x)) Filter.atTop
      (nhds (inner ℂ x x)) := by
    have heng := P.tendsto_inner_boundedFC_of_dominated
      (f := fun n => towerModSpecFun L ω β (a - u n)) (g := fun _ => (1 : ℂ)) zero_le_one
      (fun n => towerModSpecFun_measurable L ω β (a - u n)) measurable_const
      (fun n r => towerModSpecFun_norm_le L ω β (a - u n) r)
      (fun r => le_of_eq norm_one) hptw x x
    rw [P.inner_boundedFC, P.bilinDiag_const, one_mul] at heng
    exact heng
  -- the squared norm
  have hform : ∀ n, ‖towerModUnitary L ω β (u n) x - towerModUnitary L ω β a x‖ ^ 2
      = 2 * ‖x‖ ^ 2 - 2 * (inner ℂ x (towerModUnitary L ω β (a - u n) x)).re := by
    intro n
    rw [norm_sub_sq_real, norm_towerModUnitary_apply, norm_towerModUnitary_apply]
    have hib : (inner ℝ (towerModUnitary L ω β (u n) x) (towerModUnitary L ω β a x))
        = (inner ℂ x (towerModUnitary L ω β (a - u n) x)).re := by
      show (inner ℂ (towerModUnitary L ω β (u n) x) (towerModUnitary L ω β a x)).re = _
      rw [inner_towerModUnitary_towerModUnitary]
    rw [hib]; ring
  -- ‖·‖² → 0, then ‖·‖ → 0
  have hself : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  have hsq : Filter.Tendsto
      (fun n => ‖towerModUnitary L ω β (u n) x - towerModUnitary L ω β a x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto
        (fun n => (inner ℂ x (towerModUnitary L ω β (a - u n) x)).re)
        Filter.atTop (nhds ((inner ℂ x x).re)) := (Complex.continuous_re.tendsto _).comp hinner
    have hlim : Filter.Tendsto
        (fun n => 2 * ‖x‖ ^ 2 - 2 * (inner ℂ x (towerModUnitary L ω β (a - u n) x)).re)
        Filter.atTop (nhds (2 * ‖x‖ ^ 2 - 2 * (inner ℂ x x).re)) :=
      (hg.const_mul 2).const_sub (2 * ‖x‖ ^ 2)
    rw [hself, show (2 * ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2) = 0 by ring] at hlim
    simpa only [hform] using hlim
  have hfin := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero] at hfin
  exact Filter.Tendsto.congr (fun n => Real.sqrt_sq (norm_nonneg _)) hfin

/-! ### R5.3 — the honesty pair: `U_tΩ = Ω` and `E({0}) = 0` -/

/-- **`U_t` fixes the cyclic vector: `U_tΩ = Ω`.**  `RΩ = ½Ω` (R2) exhibits `Ω ≠ 0` as an
    eigenvector at `r = ½` (so `½ ∈ σ(R)`); the R3 eigenvector calculus gives
    `U_tΩ = u_t(½)•Ω`, and the symbol evaluates to
    `u_t(½) = exp(i·t·log((1−½)/½)) = exp(i·t·log 1) = 1`. -/
theorem towerModUnitary_cyclicVec (t : ℝ) :
    towerModUnitary L ω β t (towerCyclicVec L ω β) = towerCyclicVec L ω β := by
  -- Ω ≠ 0, from ‖Ω‖ = 1
  have hΩ : towerCyclicVec L ω β ≠ 0 := by
    intro h0
    have h1 := norm_cyclicVec L ω β
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  -- the eigenvector equation in the real-scalar form the R3 calculus expects
  have hTx : towerResolvent L ω β (towerCyclicVec L ω β)
      = (((2⁻¹ : ℝ)) : ℂ) • towerCyclicVec L ω β := by
    rw [towerResolvent_cyclicVec]
    norm_num
  -- ½ ∈ σ(R)
  have hr : (2⁻¹ : ℝ) ∈ spectrum ℝ (towerResolvent L ω β) :=
    mem_spectrum_of_eigenvector (towerResolvent L ω β) hΩ hTx
  -- the FC acts on Ω by evaluation of the symbol at ½
  have hval := borelFC_apply_eigenvector (towerResolvent L ω β)
    (towerResolvent_isSelfAdjoint L ω β) (towerModSpecFun_measurable L ω β t)
    zero_le_one (towerModSpecFun_norm_le L ω β t) hr hTx
  -- the symbol value: `u_t(½) = exp(i·t·log 1) = 1`
  have hsym : towerModSpecFun L ω β t ⟨(2⁻¹ : ℝ), hr⟩ = 1 := by
    show towerModChar t (2⁻¹ : ℝ) = 1
    unfold towerModChar
    have hmem : (2⁻¹ : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
    rw [Set.piecewise_eq_of_mem _ _ _ hmem]
    have harg : ((1 : ℝ) - 2⁻¹) / 2⁻¹ = 1 := by norm_num
    rw [harg, Real.log_one]
    simp
  rw [towerModUnitary, hval, hsym, one_smul]

/-- Bridge from R1's kernel form (`Rh = 0 → h = 0`) to `Function.Injective`. -/
theorem towerResolvent_function_injective :
    Function.Injective (towerResolvent L ω β) := by
  intro a b hab
  have h0 : towerResolvent L ω β (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (towerResolvent_injective L ω β h0)

/-- **No spectral weight at the junk point: `E({0}) = 0`.**  Kernel triviality of the
    resolvent (R1) forces the spectral measure of `R` to carry no atom at `0` (the R3
    kernel-atom lemma) — so the junk value of the symbol is never seen by the calculus,
    and `U_t` genuinely represents `((1−r)/r)^{it} = δ^{it}` on the spectrum. -/
theorem towerResolvent_pvm_atom_zero :
    (PVM_of_selfAdjoint (towerResolvent L ω β)
        (towerResolvent_isSelfAdjoint L ω β)).E (Subtype.val ⁻¹' ({0} : Set ℝ)) = 0 :=
  E_zero_atom_of_injective (towerResolvent L ω β) (towerResolvent_isSelfAdjoint L ω β)
    (towerResolvent_function_injective L ω β)

end QIQTH.TowerGNS
