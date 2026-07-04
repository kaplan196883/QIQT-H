/-
  THE CONJUGATE ADJOINT M1–M2 (THE_MODULAR_OPERATOR_PLAN.md) — the abstract layer.

  Tomita's F as the conjugate-linear adjoint of an ℝ-linear partial map `g` (the shape of S̄)
  through the sesquilinear pairing ⟪F y, x⟫ = ⟪g x, y⟫, built on THE ∃-RIESZ DOMAIN
  (binding verdict A2): `conjAdjointDom g := {y | ∃ w, ∀ x : g.domain, ⟪g x, y⟫ = ⟪w, x⟫}` —
  no toDual, no CLM extension, no boundedness predicate, no completeness; the classical
  equivalence of the ∃-Riesz domain with the boundedness domain is NOT formalized and NOT
  needed. The witness is UNIQUE against a dense domain (`Dense.eq_of_inner_left`), giving a
  well-defined conjugate-linear (starRingEnd ℂ)-semilinear partial map
  `conjAdjoint g hd : E →ₛₗ.[starRingEnd ℂ] E` (the towerTomita₀ packaging precedent).

  CHOICE HYGIENE (the tomitaFun_eq pattern): ONE witness def (`conjAdjointFun`,
  `Classical.choose` contained there) + ONE spec lemma (`conjAdjointFun_spec`), everything
  else routed through the spec + the uniqueness lemma; `conjAdjoint` is never unfolded
  downstream — `conjAdjoint_apply_spec` is the one lemma downstream uses.

  M1 — the domain, the witness, uniqueness, the semilinear packaging, closedness of the
       graph in honest sequence form (`conjAdjoint_closed`: limits pass through the pairing).
  M2 — the equalizer core-extension lemma (`pairing_extends_of_closure`): a pairing identity
       on a core extends to the closure — the set {p | ⟪p.2, y⟫ = ⟪w, p.1⟫} is closed and
       contains the graph, hence contains the graph of the closure
       (`IsClosable.graph_closure_eq_closure_graph`).

  This file is ABSTRACT: it imports Mathlib + ConjClosure only and knows nothing about
  TowerGNS. NOT here (verdict A6): Δ, J, Δ^{1/2}, Δ^{it}, self-adjointness (von Neumann's
  theorem), KMS-at-the-limit, a von Neumann type — not constructed or claimed.
-/
import QIQTH.TowerGNS.ConjClosure

namespace QIQTH.ConjAdjoint

open Filter Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### M1 — the ∃-Riesz domain -/

/-- **The ∃-Riesz adjoint domain** of an ℝ-linear partial map `g` (the shape of S̄): the set
of `y` admitting a Riesz witness `w` with `⟪g x, y⟫ = ⟪w, x⟫` for every `x` in the domain.
A `Submodule ℂ` — the smul witness carries the TWIST `starRingEnd ℂ c • w` (first-slot
conjugate-linearity: `⟪conj c • w, x⟫ = c * ⟪w, x⟫`). No boundedness predicate anywhere;
the classical equivalence with the boundedness domain is not formalized and not needed. -/
def conjAdjointDom (g : E →ₗ.[ℝ] E) : Submodule ℂ E where
  carrier := {y : E | ∃ w : E, ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ}
  zero_mem' := ⟨0, fun x => by simp⟩
  add_mem' := by
    rintro y₁ y₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
    exact ⟨w₁ + w₂, fun x => by rw [inner_add_right, h₁ x, h₂ x, inner_add_left]⟩
  smul_mem' := by
    rintro c y ⟨w, h⟩
    refine ⟨starRingEnd ℂ c • w, fun x => ?_⟩
    rw [inner_smul_right, h x, inner_smul_left, starRingEnd_self_apply]

/-- Membership unfolding for the ∃-Riesz domain (definitional). -/
theorem mem_conjAdjointDom_iff {g : E →ₗ.[ℝ] E} {y : E} :
    y ∈ conjAdjointDom g ↔
      ∃ w : E, ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ :=
  Iff.rfl

/-- Membership introduction: any Riesz witness certifies membership. -/
theorem mem_conjAdjointDom {g : E →ₗ.[ℝ] E} {y w : E}
    (h : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ) :
    y ∈ conjAdjointDom g :=
  ⟨w, h⟩

/-- **Uniqueness of the Riesz witness** against a dense domain: two witnesses pair equally
with every element of the dense set, hence are equal (`Dense.eq_of_inner_left` — the dense
vectors sit in the SECOND slot, the candidates in the first). -/
theorem conjAdjoint_witness_unique {g : E →ₗ.[ℝ] E} (hd : Dense (g.domain : Set E))
    {y w₁ w₂ : E} (h₁ : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w₁, (x : E)⟫_ℂ)
    (h₂ : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w₂, (x : E)⟫_ℂ) : w₁ = w₂ :=
  hd.eq_of_inner_left ℂ fun v hv => (h₁ ⟨v, hv⟩).symm.trans (h₂ ⟨v, hv⟩)

/-- The chosen Riesz witness of a domain element (`Classical.choose` — contained HERE, with
the ONE spec lemma below; everything else routes through `conjAdjointFun_spec` and
`conjAdjoint_witness_unique`). The definition needs no density — density enters only for
the well-definedness (additivity/semilinearity) of the packaging. -/
noncomputable def conjAdjointFun (g : E →ₗ.[ℝ] E) (y : conjAdjointDom g) : E :=
  Classical.choose (mem_conjAdjointDom_iff.mp y.2)

/-- **THE ONE SPEC LEMMA** (choice hygiene, binding): the chosen witness satisfies the
pairing `⟪g x, y⟫ = ⟪F y, x⟫` for every `x` in the domain of `g`. -/
theorem conjAdjointFun_spec (g : E →ₗ.[ℝ] E) (y : conjAdjointDom g) (x : g.domain) :
    ⟪(g x : E), (y : E)⟫_ℂ = ⟪conjAdjointFun g y, (x : E)⟫_ℂ :=
  Classical.choose_spec (mem_conjAdjointDom_iff.mp y.2) x

/-- **THE CONJUGATE ADJOINT** `F` of `g` (the abstract Tomita F), packaged as a
conjugate-linear (`starRingEnd ℂ`-semilinear) partial map on the ∃-Riesz domain.
The semilinear law `F (c • y) = conj c • F y` IS the conjugate-homogeneity of `F` —
no separate predicate is needed (`map_smulₛₗ` carries it). Density of `g.domain` makes
the chosen witness unique, hence additive and conjugate-homogeneous. -/
noncomputable def conjAdjoint (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E)) :
    E →ₛₗ.[starRingEnd ℂ] E where
  domain := conjAdjointDom g
  toFun :=
    { toFun := conjAdjointFun g
      map_add' := fun y₁ y₂ =>
        conjAdjoint_witness_unique hd (conjAdjointFun_spec g (y₁ + y₂)) fun x => by
          rw [Submodule.coe_add, inner_add_right, conjAdjointFun_spec g y₁ x,
            conjAdjointFun_spec g y₂ x, inner_add_left]
      map_smul' := fun c y =>
        conjAdjoint_witness_unique hd (conjAdjointFun_spec g (c • y)) fun x => by
          rw [Submodule.coe_smul, inner_smul_right, conjAdjointFun_spec g y x,
            inner_smul_left, starRingEnd_self_apply] }

/-- The domain of the conjugate adjoint is the ∃-Riesz domain (definitional). -/
@[simp]
theorem conjAdjoint_domain (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E)) :
    (conjAdjoint g hd).domain = conjAdjointDom g :=
  rfl

/-- The conjugate adjoint computes as the chosen witness (definitional adapter). -/
theorem conjAdjoint_apply (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E))
    (y : (conjAdjoint g hd).domain) :
    conjAdjoint g hd y = conjAdjointFun g y :=
  rfl

/-- **The spec transported to the packaged map** — THE ONE LEMMA DOWNSTREAM USES:
`⟪g x, y⟫ = ⟪F y, x⟫` for every `y` in the adjoint domain and `x` in the domain of `g`. -/
theorem conjAdjoint_apply_spec (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E))
    (y : (conjAdjoint g hd).domain) (x : g.domain) :
    ⟪(g x : E), (y : E)⟫_ℂ = ⟪conjAdjoint g hd y, (x : E)⟫_ℂ :=
  conjAdjointFun_spec g y x

/-- **The choice-discharge lemma** (the `tomitaFun_eq` pattern): on ANY presentation of the
pairing — `w` a Riesz witness for `y` — the conjugate adjoint computes to `w`, by
uniqueness against the dense domain. -/
theorem conjAdjoint_eq (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E)) {y w : E}
    (h : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ) :
    conjAdjoint g hd ⟨y, mem_conjAdjointDom h⟩ = w :=
  conjAdjoint_witness_unique hd
    (conjAdjointFun_spec g ⟨y, mem_conjAdjointDom h⟩) h

/-- The value of the conjugate adjoint depends only on the domain VECTOR (the
membership-proof-transport adapter — the `towerTomita₀_congr` pattern). -/
theorem conjAdjoint_congr (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E)) {x y : E}
    (hx : x ∈ (conjAdjoint g hd).domain) (hy : y ∈ (conjAdjoint g hd).domain) (h : x = y) :
    conjAdjoint g hd ⟨x, hx⟩ = conjAdjoint g hd ⟨y, hy⟩ := by
  cases h
  rfl

/-- **Graph closedness of the conjugate adjoint, in honest sequence form**: if `yₙ` lies in
the adjoint domain, `yₙ → y`, and `F yₙ → w`, then `y` lies in the adjoint domain and
`F y = w` — limits pass through the spec pairing in both slots (`Filter.Tendsto.inner`),
so `w` is a Riesz witness for `y`; the value is `w` by uniqueness. No completeness of `E`
anywhere. -/
theorem conjAdjoint_closed (g : E →ₗ.[ℝ] E) (hd : Dense (g.domain : Set E)) {y w : E}
    (yseq : ℕ → (conjAdjoint g hd).domain)
    (hy : Tendsto (fun n => ((yseq n : E))) atTop (𝓝 y))
    (hw : Tendsto (fun n => conjAdjoint g hd (yseq n)) atTop (𝓝 w)) :
    ∃ hmem : y ∈ (conjAdjoint g hd).domain, conjAdjoint g hd ⟨y, hmem⟩ = w := by
  have hpair : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ := by
    intro x
    have h1 : Tendsto (fun n => ⟪(g x : E), ((yseq n : E))⟫_ℂ) atTop
        (𝓝 ⟪(g x : E), y⟫_ℂ) :=
      tendsto_const_nhds.inner hy
    have h2 : Tendsto (fun n => ⟪conjAdjoint g hd (yseq n), (x : E)⟫_ℂ) atTop
        (𝓝 ⟪w, (x : E)⟫_ℂ) :=
      hw.inner tendsto_const_nhds
    have heq : (fun n => ⟪(g x : E), ((yseq n : E))⟫_ℂ)
        = fun n => ⟪conjAdjoint g hd (yseq n), (x : E)⟫_ℂ :=
      funext fun n => conjAdjoint_apply_spec g hd (yseq n) x
    exact tendsto_nhds_unique (heq ▸ h1) h2
  exact ⟨mem_conjAdjointDom hpair, conjAdjoint_eq g hd hpair⟩

/-! ### M2 — the equalizer core-extension lemma -/

/-- **THE CORE-EXTENSION LEMMA** (verdict A5): a Riesz pairing identity holding on a
closable map extends to its closure — the equalizer set
`{p : E × E | ⟪p.2, y⟫ = ⟪w, p.1⟫}` is CLOSED (the inner product is continuous in each
slot) and contains the graph of `g`, hence contains its closure, which is the graph of
`g.closure` (`IsClosable.graph_closure_eq_closure_graph`). This is how a pairing verified
on the core (the orbit domain) reaches S̄. -/
theorem pairing_extends_of_closure {g : E →ₗ.[ℝ] E} (hc : g.IsClosable) {y w : E}
    (h : ∀ x : g.domain, ⟪(g x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ) :
    ∀ x : g.closure.domain, ⟪(g.closure x : E), y⟫_ℂ = ⟪w, (x : E)⟫_ℂ := by
  -- the equalizer set is closed
  have hA : IsClosed {p : E × E | ⟪p.2, y⟫_ℂ = ⟪w, p.1⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_const.inner continuous_fst)
  -- the graph of g lands in it
  have hsub : (g.graph : Set (E × E)) ⊆ {p : E × E | ⟪p.2, y⟫_ℂ = ⟪w, p.1⟫_ℂ} := by
    intro p hp
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hp
    obtain ⟨x, hx1, hx2⟩ := hp
    show ⟪p.2, y⟫_ℂ = ⟪w, p.1⟫_ℂ
    rw [← hx1, ← hx2]
    exact h x
  -- hence so does the closure of the graph = the graph of the closure
  intro x
  have hg : ((x : E), g.closure x) ∈ g.closure.graph := g.closure.mem_graph x
  rw [← hc.graph_closure_eq_closure_graph] at hg
  have hmem : ((x : E), g.closure x) ∈ _root_.closure (g.graph : Set (E × E)) := hg
  exact hA.closure_subset_iff.mpr hsub hmem

end QIQTH.ConjAdjoint
