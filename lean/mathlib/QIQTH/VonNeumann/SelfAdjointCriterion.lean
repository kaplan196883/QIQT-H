/-
  THE VON NEUMANN CAMPAIGN — VN1 (THE_VON_NEUMANN_PLAN.md) — the abstract kernel.

  **The basic criterion for self-adjointness, positive-operator form** (the von Neumann
  kernel): a densely defined SYMMETRIC partial linear map `A` on a Hilbert space over any
  `RCLike` field `𝕜` with `ran(1 + A) = ⊤` is genuinely SELF-ADJOINT — `A† = A` in the
  Mathlib `LinearPMap.adjoint` sense (`IsSelfAdjoint` through `LinearPMap.instStar`).
  ABSENT from Mathlib at this pin: the LinearPMap adjoint file has
  `IsFormalAdjoint.le_adjoint` (symmetric ⟹ `A ≤ A†`) but no criterion closing the reverse
  inclusion `A† ≤ A`.

  Route (the `stoneGen_isSelfAdjoint` pattern of QIQTH/Spectral/Garding.lean, transposed
  from `A ± i`-surjectivity to `1 + A`-surjectivity — the positive-operator normalization):
  `A ≤ A†` by `le_adjoint`; for `z ∈ dom A†`, surjectivity of `1 + A` produces `x ∈ dom A`
  with `(1 + A)x = (1 + A†)z`; then `u := z − x` has `(1 + A†)u = 0` (value agreement from
  `A ≤ A†`), so `⟪u, (1 + A)y⟫ = ⟪(1 + A†)u, y⟫ = 0` for EVERY `y ∈ dom A`
  (`adjoint_isFormalAdjoint`), and surjectivity again — at `h := u` — forces
  `⟪u, u⟫ = 0`, i.e. `z = x ∈ dom A`. Domains agree; `eq_of_le_of_domain_eq` finishes.

  This file is ABSTRACT and REUSABLE: Mathlib-only imports, no QIQTH dependency (a
  Mathlib-gap contribution). Consumed at `𝕜 = ℂ` by VN5 (`towerModularOp_isSelfAdjoint`),
  with the surjectivity input supplied by VN2 + VN4. NOT here (deliberately): closedness or
  positivity hypotheses (not needed — surjectivity of `1 + A` carries everything), the
  graph decomposition (VN2), von Neumann's `T†T` theorem itself (VN3).
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace QIQTH.VonNeumann

open LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- **★★★ The von Neumann kernel criterion (VN1):** a densely defined symmetric
(`A.IsFormalAdjoint A`) partial linear map with `1 + A` surjective onto the whole space is
SELF-ADJOINT: `A† = A` (stated through `LinearPMap`'s `Star` instance). The half `A ≤ A†` is
Mathlib's `le_adjoint`; the reverse inclusion is the content: for `z ∈ dom A†`, solve
`(1 + A)x = (1 + A†)z`, note `u := z − x` satisfies `(1 + A†)u = 0`, hence `u ⊥ ran(1 + A) = ⊤`,
hence `u = 0` and `z = x ∈ dom A`. Field-generic (`RCLike 𝕜`) — no `±i` anywhere. -/
theorem isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective
    {A : E →ₗ.[𝕜] E} (hd : Dense (A.domain : Set E))
    (hsym : A.IsFormalAdjoint A)
    (hsurj : ∀ h : E, ∃ x : A.domain, (x : E) + A x = h) :
    IsSelfAdjoint A := by
  have hle : A ≤ A.adjoint := hsym.le_adjoint hd
  rw [LinearPMap.isSelfAdjoint_def]
  refine (LinearPMap.eq_of_le_of_domain_eq hle
    (le_antisymm hle.1 fun z hz => ?_)).symm
  -- `z ∈ dom A†`: solve `(1 + A) x = (1 + A†) z`
  obtain ⟨x, hx⟩ := hsurj (z + A.adjoint ⟨z, hz⟩)
  -- `x` also lies in `dom A†`, with the same value there (`A ≤ A†`)
  have hxadj : (x : E) ∈ A.adjoint.domain := hle.1 x.2
  have hAx : A.adjoint ⟨(x : E), hxadj⟩ = A x :=
    (hle.2 (x := x) (y := ⟨(x : E), hxadj⟩) rfl).symm
  -- `u := z − x` satisfies `(1 + A†) u = 0`
  have hu : z - (x : E) ∈ A.adjoint.domain := Submodule.sub_mem _ hz hxadj
  have hueq : (z - (x : E)) + A.adjoint ⟨z - (x : E), hu⟩ = 0 := by
    have hpair : (⟨z - (x : E), hu⟩ : A.adjoint.domain)
        = ⟨z, hz⟩ - ⟨(x : E), hxadj⟩ := rfl
    rw [hpair, LinearPMap.map_sub, hAx]
    have hrw : z - (x : E) + (A.adjoint ⟨z, hz⟩ - A x)
        = (z + A.adjoint ⟨z, hz⟩) - ((x : E) + A x) := by abel
    rw [hrw, hx, sub_self]
  -- hence `u ⊥ ran(1 + A)`: `⟪u, (1 + A) y⟫ = ⟪(1 + A†) u, y⟫ = 0` for every `y ∈ dom A`
  have hpair0 : ∀ y : A.domain, ⟪z - (x : E), (y : E) + A y⟫ = 0 := by
    intro y
    have hfa : ⟪A.adjoint ⟨z - (x : E), hu⟩, (y : E)⟫ = ⟪z - (x : E), A y⟫ :=
      adjoint_isFormalAdjoint hd ⟨z - (x : E), hu⟩ y
    rw [inner_add_right, ← hfa, ← inner_add_left, hueq, inner_zero_left]
  -- `ran(1 + A) = ⊤`, so `u ⊥ u`, so `u = 0`, so `z = x ∈ dom A`
  obtain ⟨y, hy⟩ := hsurj (z - (x : E))
  have hzero : z - (x : E) = 0 := by
    have h0 := hpair0 y
    rw [hy] at h0
    exact inner_self_eq_zero.mp h0
  rw [sub_eq_zero.mp hzero]
  exact x.2

/-- The criterion restated as the raw adjoint equation `A† = A` (adapter corollary — the
form `LinearPMap.eq_of_le_of_domain_eq` naturally lands in, unfolded from the `Star`
instance for downstream consumers that avoid `IsSelfAdjoint`). -/
theorem adjoint_eq_of_isFormalAdjoint_of_one_add_surjective
    {A : E →ₗ.[𝕜] E} (hd : Dense (A.domain : Set E))
    (hsym : A.IsFormalAdjoint A)
    (hsurj : ∀ h : E, ∃ x : A.domain, (x : E) + A x = h) :
    A.adjoint = A :=
  LinearPMap.isSelfAdjoint_def.mp
    (isSelfAdjoint_of_isFormalAdjoint_of_one_add_surjective hd hsym hsurj)

end QIQTH.VonNeumann
