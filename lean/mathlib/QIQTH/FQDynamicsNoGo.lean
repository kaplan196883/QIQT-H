/-
  FQ Dynamics No-Go — exact finite admissibility ⇒ trivial evolution.

  GPT-5.5-pro audit observation:

      If (FQ) is read as "the admissible state space `H_phys` is
      *literally* a finite set of states", and time evolution is
      continuous on H_phys preserving it, then every connected
      one-parameter orbit is constant — i.e., the dynamics is trivial.

  This forces the paper to be precise about what (FQ) means.  An
  exactly finite invariant grid of amplitudes is incompatible with
  non-trivial continuous Hamiltonian evolution.  The framework
  presumably means "finite operational distinguishability" or
  "bounded information content", not an exactly finite invariant
  set.  The audit makes this distinction explicit.
-/

import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace QIQTH
namespace FQDynamicsNoGo

/-- A continuous function from a preconnected space to a T2 space with
    finite range is constant.  Proof: each fiber `f⁻¹{y}` is clopen
    (closed since T2; open because its complement is a finite union
    of closed fibers).  A preconnected space has no proper nonempty
    clopen subset. -/
theorem connected_finite_range_subsingleton
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hfin : (Set.range f).Finite) :
    (Set.range f).Subsingleton := by
  intro y hy z hz
  by_contra h_ne
  -- Fiber f⁻¹{y} is closed (T2 ⇒ singletons closed).
  have h_fiber_closed : IsClosed (f ⁻¹' {y}) :=
    (isClosed_singleton : IsClosed ({y} : Set Y)).preimage hf
  -- Complement equals f⁻¹(range f \ {y}), a closed preimage of a finite set.
  have h_compl_eq : (f ⁻¹' {y})ᶜ = f ⁻¹' (Set.range f \ {y}) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
               Set.mem_diff]
    refine ⟨fun hx => ⟨Set.mem_range_self x, hx⟩, fun ⟨_, hne⟩ => hne⟩
  have h_diff_finite : (Set.range f \ {y}).Finite := hfin.diff
  have h_diff_closed : IsClosed (Set.range f \ {y}) := h_diff_finite.isClosed
  have h_compl_closed : IsClosed ((f ⁻¹' {y})ᶜ) := by
    rw [h_compl_eq]; exact h_diff_closed.preimage hf
  have h_fiber_open : IsOpen (f ⁻¹' {y}) := by
    rw [← compl_compl (f ⁻¹' {y})]
    exact h_compl_closed.isOpen_compl
  have h_compl_open : IsOpen ((f ⁻¹' {y})ᶜ) := h_fiber_closed.isOpen_compl
  -- Witnesses to nonempty fiber and nonempty complement:
  obtain ⟨x_y, hxy⟩ := hy
  obtain ⟨x_z, hxz⟩ := hz
  have h_x_y_in : x_y ∈ f ⁻¹' {y} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hxy
  have h_x_z_notin : x_z ∉ f ⁻¹' {y} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    intro h; apply h_ne; rw [← hxz, h]
  -- A preconnected universe cannot be split into two disjoint nonempty opens.
  have h_cover : (Set.univ : Set X) ⊆ (f ⁻¹' {y}) ∪ (f ⁻¹' {y})ᶜ := by
    intro x _; exact (em (x ∈ f ⁻¹' {y})).imp id id
  have h_disj : Disjoint (f ⁻¹' {y}) ((f ⁻¹' {y})ᶜ) := disjoint_compl_right
  have h_or := isPreconnected_univ.subset_or_subset
    h_fiber_open h_compl_open h_disj h_cover
  rcases h_or with h | h
  · exact h_x_z_notin (h (Set.mem_univ _))
  · exact (h (Set.mem_univ _)) h_x_y_in

/-- **FQ Dynamics No-Go theorem.**

    If the FQ-admissible state space `H_phys` is literally finite,
    and time evolution is a continuous flow preserving it (with the
    identity at `t = 0`), then every admissible state is
    evolution-fixed:  `Φ t ρ = ρ` for every `t` and `ρ ∈ H_phys`.

    Strategic implication: (FQ) cannot mean "exactly finite invariant
    grid of admissible states" if the framework wants non-trivial
    Hamiltonian evolution.  The framework's actual reading must be
    "bounded information content" / "finite operational
    distinguishability", which permits approximate / discrete-time
    / coarse-grained dynamics on a continuous state manifold. -/
theorem finite_admissible_flow_fixed
    {State : Type*} [TopologicalSpace State] [T2Space State]
    (Hphys : Set State) (hfin : Hphys.Finite)
    (Φ : ℝ → State → State)
    (hcont : ∀ ρ ∈ Hphys, Continuous fun t : ℝ => Φ t ρ)
    (hpres : ∀ (t : ℝ) ρ, ρ ∈ Hphys → Φ t ρ ∈ Hphys)
    (hzero : ∀ ρ ∈ Hphys, Φ 0 ρ = ρ) :
    ∀ (t : ℝ) ρ, ρ ∈ Hphys → Φ t ρ = ρ := by
  intro t ρ hρ
  set g : ℝ → State := fun t => Φ t ρ
  have h_g_cont : Continuous g := hcont ρ hρ
  have h_g_range_sub : Set.range g ⊆ Hphys := by
    rintro y ⟨t', rfl⟩; exact hpres t' ρ hρ
  have h_g_range_fin : (Set.range g).Finite := hfin.subset h_g_range_sub
  have h_sub : (Set.range g).Subsingleton :=
    connected_finite_range_subsingleton h_g_cont h_g_range_fin
  have h_eq : g t = g 0 :=
    h_sub (Set.mem_range_self t) (Set.mem_range_self 0)
  show Φ t ρ = ρ
  calc Φ t ρ = g t   := rfl
    _ = g 0          := h_eq
    _ = Φ 0 ρ        := rfl
    _ = ρ            := hzero ρ hρ

end FQDynamicsNoGo
end QIQTH
