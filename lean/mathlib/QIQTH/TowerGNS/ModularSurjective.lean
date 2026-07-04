/-
  THE VON NEUMANN CAMPAIGN — VN4 (THE_VON_NEUMANN_PLAN.md) — the i-twist + surjectivity of
  1 + Δ: the von Neumann RANGE CONDITION for the tower modular operator.

  Two pieces, both new:

  (a) **THE ABSTRACT i-TWIST** (`conj_pairing_of_re_pairing`): for a conjugate-homogeneous
      ℝ-linear partial map `g` on a ℂ-inner-product space, a REAL-PART pairing identity
      `re ⟪g a, y⟫ = re ⟪w, a⟫` (∀ a in the domain) upgrades to the FULL ℂ pairing
      `⟪g a, y⟫ = ⟪w, a⟫`. Route: evaluate the real identity at `a` (the real parts) and at
      `i • a` (ConjHomogeneous supplies membership AND the value `g(i•a) = conj i • g a`;
      the twist turns both sides into `re (i • z)`, i.e. MINUS the imaginary parts);
      `Complex.ext` finishes. This is the ONLY place where the ℝ-geometry of VN2 learns
      that S̄ was conjugate-linear.

  (b) **THE TOWER SURJECTIVITY** (`towerModularOp_one_add_surjective`): `ran (1 + Δ) = ⊤`,
      i.e. every `h` is `x + Δ x` for some `x ∈ dom Δ`. Route: VN2's graph decomposition
      (`QIQTH.VonNeumann.exists_pairing_of_isClosed`) at `𝕜 = ℝ` on the CLOSED S̄ — through
      `InnerProductSpace.rclikeToReal ℂ` (a `letI` INSIDE the proof of the private
      re-pairing lemma ONLY; the real inner product is DEFINITIONALLY `re ⟪·,·⟫_ℂ`, and its
      module structure is definitionally the global `complexToReal` one under S̄) — giving
      `x ∈ dom S̄` with `re ⟪a, h − x⟫ = re ⟪S̄ a, S̄ x⟫` for all `a`; `inner_re_symm`
      reorients; the i-twist (a) upgrades to `⟪S̄ a, S̄ x⟫ = ⟪h − x, a⟫` — which is VERBATIM
      the ∃-Riesz membership `S̄ x ∈ dom F` with witness `h − x`; so `x ∈ dom Δ` (the
      two-layer domain) and `Δ x = F (S̄ x) = h − x` by the choice-discharge
      `conjAdjoint_eq`; hence `x + Δ x = h`.

  This is the load-bearing increment: with VN1's abstract kernel and the already-proved
  symmetry + dense domain of Δ, the range condition proved here is the LAST input of
  Δ† = Δ (VN5). NOT here (deliberately): self-adjointness itself, the resolvent, Δ^{1/2},
  J, Δ^{it}, KMS, any type statement.
-/
import Mathlib
import QIQTH.TowerGNS.ModularOp
import QIQTH.VonNeumann.GraphDecomposition

namespace QIQTH.TowerGNS

open QIQTH.ConjClosure QIQTH.ConjAdjoint
open scoped InnerProductSpace

/-! ### VN4(a) — the abstract i-twist -/

section AbstractTwist

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **THE i-TWIST (VN4a)**: for a conjugate-homogeneous ℝ-linear partial map `g` on a
ℂ-inner-product space, a real-part pairing identity `re ⟪g a, y⟫ = re ⟪w, a⟫` on the whole
domain upgrades to the full ℂ pairing `⟪g a, y⟫ = ⟪w, a⟫`. The imaginary parts come from
evaluating the real identity at `i • a`: conjugate-homogeneity gives
`g (i • a) = conj i • g a`, so the left side picks up `conj (conj i) = i`
(first-slot conjugation) while the right side picks up `i` (second slot untouched) — the
SAME factor `i`, and `re (i • z) = − im z` on both sides. -/
theorem conj_pairing_of_re_pairing {g : E →ₗ.[ℝ] E} (hg : ConjHomogeneous g) {y w : E}
    (h : ∀ a : g.domain, RCLike.re ⟪(g a : E), y⟫_ℂ = RCLike.re ⟪w, (a : E)⟫_ℂ) :
    ∀ a : g.domain, ⟪(g a : E), y⟫_ℂ = ⟪w, (a : E)⟫_ℂ := by
  intro a
  -- the domain element `i • a` and the twisted value of `g` there
  obtain ⟨hIa, hval⟩ := hg Complex.I a
  -- the real identity at `i • a`
  have h2 := h ⟨Complex.I • (a : E), hIa⟩
  rw [hval] at h2
  have e2 : ((⟨Complex.I • (a : E), hIa⟩ : g.domain) : E) = Complex.I • (a : E) := rfl
  rw [e2, inner_smul_left, inner_smul_right, starRingEnd_self_apply] at h2
  -- h2 : re (I * ⟪g a, y⟫) = re (I * ⟪w, a⟫), i.e. the imaginary parts agree
  refine Complex.ext ?_ ?_
  · simpa using h a
  · simpa [Complex.mul_re] using h2
end AbstractTwist

/-! ### VN4(b) — the tower surjectivity of 1 + Δ -/

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **The re-pairing from the graph decomposition** (private: the ONLY place the
`rclikeToReal` real structure appears, kept INSIDE this proof): VN2's
`exists_pairing_of_isClosed` at `𝕜 = ℝ` on the closed S̄ produces, for every `h`, an
`x ∈ dom S̄` with `re ⟪a, h − x⟫_ℂ = re ⟪S̄ a, S̄ x⟫_ℂ` for every `a ∈ dom S̄` — the real
inner product of `InnerProductSpace.rclikeToReal ℂ` IS `re ⟪·,·⟫_ℂ` definitionally, and
its underlying module structure is definitionally the global `complexToReal` one carrying
S̄. -/
private theorem exists_re_pairing (h : TowerGNS L ω β) :
    ∃ x : (towerTomitaBar L ω β).domain,
      ∀ a : (towerTomitaBar L ω β).domain,
        RCLike.re ⟪(a : TowerGNS L ω β), h - (x : TowerGNS L ω β)⟫_ℂ
          = RCLike.re ⟪(towerTomitaBar L ω β a : TowerGNS L ω β),
              (towerTomitaBar L ω β x : TowerGNS L ω β)⟫_ℂ := by
  letI : InnerProductSpace ℝ (TowerGNS L ω β) :=
    InnerProductSpace.rclikeToReal ℂ (TowerGNS L ω β)
  obtain ⟨x, hx⟩ := QIQTH.VonNeumann.exists_pairing_of_isClosed
    (𝕜 := ℝ) (towerTomitaBar_isClosed L ω β) h
  exact ⟨x, fun a => hx a⟩

/-- **★★★ THE VON NEUMANN RANGE CONDITION (VN4b): 1 + Δ IS SURJECTIVE ★★★** — every
`h : TowerGNS` is `x + Δ x` for some `x` in the domain of the tower modular operator.
Route: the graph decomposition of the closed S̄ over ℝ (VN2) gives `x ∈ dom S̄` with the
re-pairing `re ⟪a, h − x⟫ = re ⟪S̄ a, S̄ x⟫`; `inner_re_symm` reorients; the i-twist (VN4a,
fed by the conjugate-homogeneity of S̄) upgrades it to the full ℂ pairing
`⟪S̄ a, S̄ x⟫ = ⟪h − x, a⟫` — verbatim the ∃-Riesz membership `S̄ x ∈ dom F` with witness
`h − x`; so `x ∈ dom Δ` and `Δ x = F (S̄ x) = h − x`, i.e. `x + Δ x = h`. This is the last
input of Δ† = Δ (VN5). -/
theorem towerModularOp_one_add_surjective :
    ∀ h : TowerGNS L ω β, ∃ x : (towerModularOp L ω β).domain,
      (x : TowerGNS L ω β) + towerModularOp L ω β x = h := by
  intro h
  -- VN2 at ℝ: the re-pairing
  obtain ⟨x, hx⟩ := exists_re_pairing L ω β h
  -- reorient: re ⟪S̄ a, S̄ x⟫ = re ⟪h − x, a⟫
  have hre : ∀ a : (towerTomitaBar L ω β).domain,
      RCLike.re ⟪(towerTomitaBar L ω β a : TowerGNS L ω β),
          (towerTomitaBar L ω β x : TowerGNS L ω β)⟫_ℂ
        = RCLike.re ⟪h - (x : TowerGNS L ω β), (a : TowerGNS L ω β)⟫_ℂ :=
    fun a => (hx a).symm.trans (inner_re_symm _ _)
  -- the i-twist: the full ℂ pairing ⟪S̄ a, S̄ x⟫ = ⟪h − x, a⟫
  have hpair : ∀ a : (towerTomitaBar L ω β).domain,
      ⟪(towerTomitaBar L ω β a : TowerGNS L ω β),
          (towerTomitaBar L ω β x : TowerGNS L ω β)⟫_ℂ
        = ⟪h - (x : TowerGNS L ω β), (a : TowerGNS L ω β)⟫_ℂ :=
    conj_pairing_of_re_pairing (towerTomitaBar_conjHomogeneous L ω β) hre
  -- the ∃-Riesz membership: S̄ x ∈ dom F, with witness h − x
  have hF : towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), x.2⟩
      ∈ (towerTomitaF L ω β).domain :=
    mem_towerTomitaF_dom L ω β hpair
  -- the two-layer membership: x ∈ dom Δ
  have hmem : (x : TowerGNS L ω β) ∈ towerModularDom L ω β :=
    mem_towerModularDom L ω β x.2 hF
  refine ⟨⟨(x : TowerGNS L ω β), hmem⟩, ?_⟩
  -- the value: Δ x = F (S̄ x) = h − x (spec + choice-discharge)
  have hΔ : towerModularOp L ω β ⟨(x : TowerGNS L ω β), hmem⟩
      = h - (x : TowerGNS L ω β) := by
    have h1 : towerModularOp L ω β ⟨(x : TowerGNS L ω β), hmem⟩
        = towerTomitaF L ω β
            ⟨towerTomitaBar L ω β ⟨(x : TowerGNS L ω β), x.2⟩, hF⟩ :=
      towerModularOp_apply' L ω β ⟨(x : TowerGNS L ω β), hmem⟩ x.2 hF
    rw [h1]
    exact conjAdjoint_eq (towerTomitaBar L ω β) (dense_towerTomitaBar_domain L ω β) hpair
  rw [hΔ]
  show (x : TowerGNS L ω β) + (h - (x : TowerGNS L ω β)) = h
  abel

end QIQTH.TowerGNS
