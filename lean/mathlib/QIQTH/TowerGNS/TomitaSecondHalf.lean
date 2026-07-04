/-
  THE MODULAR CONJUGATION J8 (THE_MODULAR_CONJUGATION_PLAN.md) — TOMITA'S THEOREM,
  SECOND HALF (INCLUSION FORM): `J · towerLimitVN · J ⊆ towerLimitVN′`.

  This is the COMPUTABLE half of Tomita's second theorem: the modular conjugation `J`
  conjugates the limit von Neumann algebra INTO its commutant. Assembly from the J7
  intertwining identity `J π_C(a) J = R_{jStage a}` plus the S-campaign right-multiplication
  commutation `towerRightMul_comm_limitVN`, closed by the SOT-closedness of the commuting
  condition (`SOTApprox.mem_centralizer`, extracted from the double-commutant theorem).

  Deliverables:
  • `SOTApprox.mem_centralizer` — the reusable core lifted from
    `mem_centralizer_centralizer_iff_sotApprox` (Bicommutant.lean mpr): commuting with a set
    `𝒞` is an SOT-closed condition, so an SOT-limit of operators each in the centralizer of
    `𝒞` is again in the centralizer of `𝒞`.
  • `towerRightMulCLM_mem_commutant` — `R_a ∈ M′` (right multiplication is in the commutant).
  • ★★ `jconj_limitVN_mem_commutant` — THE INCLUSION `J M J ⊆ M′`: for `T ∈ towerLimitVN`,
    `jconj T = J T J ∈ (towerLimitVN)′`. Route: SOTApprox of `T` from the stages →
    `jconj_sotApprox` → each `jconj (π_C a) = R_{jStage a} ∈ M′` → `SOTApprox.mem_centralizer`.
  • `mem_limitVN_eq_jconj_commutant` — the mirror `M ⊆ J M′ J`: every `T ∈ M` is `jconj S`
    for some `S ∈ M′` (`jconj` is an involution swapping the two inclusions).
  • `towerCyclicVec_separating_commutant` — Ω is SEPARATING for the commutant `M′` (from Ω
    CYCLIC for `M`: `S ∈ M′`, `SΩ = 0 ⟹ S` vanishes on the dense orbit `MΩ ⟹ S = 0`).

  HONEST SCOPE: the INCLUSION `J M J ⊆ M′` ONLY. The REVERSE inclusion `M′ ⊆ J M J` — i.e.
  the full equality `J M J = M′` — is Tomita's HARD half and is NOT proved (the commutant of
  the limit algebra is not characterized; the named route for later is the Rieffel–van Daele
  real-subspace argument, NOT analytic continuation). No unbounded `Δ^{1/2}`, no strip-KMS,
  no type classification. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ConjImplements
import QIQTH.TowerGNS.Separation

/-! ### Item 1 — the SOT-closedness of the commuting condition (generic, `QIQTH.VonNeumann`) -/

namespace QIQTH.VonNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **`SOTApprox.mem_centralizer`** — commuting with a set `𝒞` is an SOT-closed condition.
    If `T` is strong-operator approximable from `𝒮` and every element of `𝒮` lies in the
    centralizer of `𝒞`, then `T` itself lies in the centralizer of `𝒞`. This is the reusable
    core lifted verbatim from the `mpr` direction of `mem_centralizer_centralizer_iff_sotApprox`
    (with the algebra `A := 𝒮` and the arbitrary commuting set `𝒞`), the `![x, m x]` estimate
    `‖(mT − Tm)x‖ ≤ ‖m‖·‖(T−a)x‖ + ‖(a−T)(mx)‖` closing the commutation in the limit. -/
theorem SOTApprox.mem_centralizer {𝒮 𝒞 : Set (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : SOTApprox 𝒮 T) (h𝒮 : ∀ s ∈ 𝒮, s ∈ Set.centralizer 𝒞) :
    T ∈ Set.centralizer 𝒞 := by
  intro m hm
  refine ContinuousLinearMap.ext fun x => ?_
  have key : ∀ ε > (0 : ℝ), ‖m (T x) - T (m x)‖ < ε := by
    intro ε hε
    set δ : ℝ := ε / (‖m‖ + 1) with hδdef
    have hmpos : (0 : ℝ) < ‖m‖ + 1 := by positivity
    have hδ : 0 < δ := div_pos hε hmpos
    obtain ⟨a, ha, hclose⟩ := hT 2 ![x, m x] δ hδ
    have h0 : ‖T x - a x‖ < δ := by simpa using hclose 0
    have h1 : ‖T (m x) - a (m x)‖ < δ := by simpa using hclose 1
    have hcomm : m (a x) = a (m x) := by
      have hcen := h𝒮 a ha m hm
      have happ := congrArg (fun (F : H →L[ℂ] H) => F x) hcen
      simpa only [ContinuousLinearMap.mul_apply] using happ
    have hsplit : m (T x) - T (m x)
        = m (T x - a x) + (a (m x) - T (m x)) := by
      rw [map_sub, hcomm]
      abel
    calc ‖m (T x) - T (m x)‖
        = ‖m (T x - a x) + (a (m x) - T (m x))‖ := by rw [hsplit]
      _ ≤ ‖m (T x - a x)‖ + ‖a (m x) - T (m x)‖ := norm_add_le _ _
      _ ≤ ‖m‖ * ‖T x - a x‖ + ‖a (m x) - T (m x)‖ := by
          have := m.le_opNorm (T x - a x)
          gcongr
      _ < ‖m‖ * δ + δ := by
          rw [norm_sub_rev] at h1
          have hm0 : (0 : ℝ) ≤ ‖m‖ := norm_nonneg m
          nlinarith
      _ ≤ ε := by
          rw [hδdef]
          rw [show ‖m‖ * (ε / (‖m‖ + 1)) + ε / (‖m‖ + 1)
              = (‖m‖ + 1) * (ε / (‖m‖ + 1)) from by ring]
          rw [mul_div_cancel₀ _ hmpos.ne']
  have hzero : ‖m (T x) - T (m x)‖ ≤ 0 := by
    by_contra h
    exact absurd (key _ (not_le.mp h)) (lt_irrefl _)
  have hnorm := norm_le_zero_iff.mp hzero
  have hdiff : m (T x) = T (m x) := sub_eq_zero.mp hnorm
  show m (T x) = T (m x)
  exact hdiff

end QIQTH.VonNeumann

/-! ### Items 2–5 — the assembly on the tower (`QIQTH.TowerGNS`) -/

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.VonNeumann
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### Item 2 — the right multiplications lie in the commutant -/

/-- **`R_a ∈ M′`**: the represented right multiplication `towerRightMulCLM C a` lies in the
    commutant of the tower limit von Neumann algebra — `R_a` commutes with every `T ∈ M`
    (`towerRightMul_comm_limitVN`), which is exactly commutant membership (`mem_commutant_iff`,
    direction-aligned by `.symm`). -/
theorem towerRightMulCLM_mem_commutant (C : Finset M) (a : DiamondAlg L C) :
    towerRightMulCLM L ω β C a ∈ (towerLimitVN L ω β).commutant := by
  rw [VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  exact (towerRightMul_comm_limitVN L ω β C a hT).symm

/-! ### Item 3 — ★★ THE INCLUSION `J M J ⊆ M′` -/

/-- **★★ J8 CAPSTONE — TOMITA'S SECOND HALF, INCLUSION FORM: `J M J ⊆ M′`**.
    For `T ∈ towerLimitVN`, the double conjugation `jconj T = J T J` lands in the commutant
    `(towerLimitVN)′`. Route: `mem_towerLimitVN_iff` presents `T` as SOT-approximable from the
    finite stages; `jconj_sotApprox` transports this to `jconj T` approximable from the
    `jconj`-images of the stages; each such image `jconj (π_C a) = R_{jStage a}` lies in the
    commutant (J7 `jconj_towerRep` + item 2); and `SOTApprox.mem_centralizer` closes, because
    commuting with `M` is SOT-closed.

    HONEST: the INCLUSION only. The reverse `M′ ⊆ J M J` (full equality `J M J = M′`) is
    Tomita's HARD half — NOT proved here (Rieffel–van Daele route, for later). -/
theorem jconj_limitVN_mem_commutant {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    jconj L ω β T ∈ (towerLimitVN L ω β).commutant := by
  rw [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant]
  rw [mem_towerLimitVN_iff] at hT
  have hj := jconj_sotApprox L ω β hT
  refine hj.mem_centralizer ?_
  rintro s ⟨u, hu, rfl⟩
  rw [Set.mem_iUnion] at hu
  obtain ⟨C, hu⟩ := hu
  obtain ⟨a, rfl⟩ := hu
  change jconj L ω β (towerRep L ω β C a) ∈ _
  rw [jconj_towerRep]
  have hR := towerRightMulCLM_mem_commutant L ω β C (jStage L ω β C a)
  rwa [← SetLike.mem_coe, VonNeumannAlgebra.coe_commutant] at hR

/-! ### Item 4 — the mirror `M ⊆ J M′ J` -/

/-- **The mirror `M ⊆ J M′ J`**: every `T ∈ towerLimitVN` is the `J`-conjugate of a commutant
    element — `T = jconj S` with `S = jconj T ∈ (towerLimitVN)′` — since `jconj` is an
    involution (`jconj_involutive`) swapping the two inclusions. (Only the inclusion direction
    is asserted; no `M′ ⊆ J M J` reverse is claimed.) -/
theorem mem_limitVN_eq_jconj_commutant {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hT : T ∈ towerLimitVN L ω β) :
    ∃ S ∈ (towerLimitVN L ω β).commutant, T = jconj L ω β S :=
  ⟨jconj L ω β T, jconj_limitVN_mem_commutant L ω β hT, (jconj_involutive L ω β T).symm⟩

/-! ### Item 5 — Ω is SEPARATING for the commutant -/

/-- **Ω IS SEPARATING FOR `M′`**: an element `S` of the commutant `(towerLimitVN)′` vanishing on
    the cyclic vector Ω is ZERO. Standard-form fact dual to `towerCyclicVec_separating`: for
    every stage operator `π_C(a) ∈ M`, `S (π_C(a) Ω) = π_C(a) (S Ω) = 0` (S commutes with M),
    so `S` vanishes on the dense orbit `M Ω` (`dense_span_towerRep_cyclicVec`) and hence
    `S = 0`. Together with the cyclicity of Ω for `M` this exhibits the standard-form pair on
    the commutant side.

    NOTE: the dual `Ω is CYCLIC for M′` is left as a plan note — the honest route is
    `J (M Ω) = M′ Ω` (via `jconj (π_C a) Ω = J (π_C a Ω)` and `JΩ = Ω`), whose density needs
    the antilinear-span image manipulation `J '' (span_ℂ base) = span_ℂ (J '' base)`; deferred
    to avoid overreach in this assembly increment. -/
theorem towerCyclicVec_separating_commutant
    {S : TowerGNS L ω β →L[ℂ] TowerGNS L ω β}
    (hS : S ∈ (towerLimitVN L ω β).commutant)
    (h0 : S (towerCyclicVec L ω β) = 0) : S = 0 := by
  refine ContinuousLinearMap.ext_on (dense_span_towerRep_cyclicVec L ω β) ?_
  rintro v ⟨C, a, rfl⟩
  have hcomm : towerRep L ω β C a * S = S * towerRep L ω β C a :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hS) (towerRep L ω β C a)
      (towerRep_mem_towerLimitVN L ω β C a)
  rw [ContinuousLinearMap.zero_apply, ← ContinuousLinearMap.mul_apply, ← hcomm,
    ContinuousLinearMap.mul_apply, h0, map_zero]

end QIQTH.TowerGNS
