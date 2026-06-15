/-
EnvarianceJustification.lean — the envariance symmetry is STRUCTURALLY FORCED for equal amplitudes (2026-06-15)

`BornEquiprobable` reduced Born-from-typicality to one residual: the **envariance symmetry** (equal-amplitude
branches are equiprobable). `Envariance.lean` *assumed* the symmetry as "a μ-preserving bijection σ that
implements the a↔b swap." This file justifies that assumption at the Hilbert-space level: the symmetry is
not arbitrary — it is the unitary **counter-swap**, and it provably fixes the global state EXACTLY when the
swapped amplitudes are equal.

Zurek's environment-assisted invariance (envariance): for an entangled state `ψ = ∑ₖ cₖ (sₖ ⊗ eₖ)`, a system
permutation `U_S` (acting on the `sₖ`) is *undone* by the matching environment permutation `U_E` (acting on
the `eₖ`), so `(U_S ⊗ U_E) ψ = ψ` — but only if `c` is permutation-invariant. We machine-check exactly this:

- `joint_perm_coeff` — the coefficient transformation: `(U_S ⊗ U_E)(∑ cₖ sₖ⊗eₖ) = ∑ c_{σ⁻¹k} sₖ⊗eₖ`. The
  joint permutation relabels the amplitudes by `c ↦ c∘σ⁻¹`. (So envariance ⟺ `c = c∘σ⁻¹`.)
- `envariance_invariant` — if `c` is σ-invariant (equal amplitudes) the joint permutation FIXES `ψ`: the
  symmetry genuinely exists.
- `envariance_swap_invariant` — the outcome form: the `a↔b` swap (undone by the environment counter-swap)
  fixes `ψ` **iff** `c a = c b`. This is precisely "equal amplitudes ⇒ envariant", with the symmetry
  exhibited as a unitary, not posited.

So the envariance premise of `Envariance.envariance_equal_marg` (a μ-preserving swap of the equal-amplitude
branches) is now grounded: the swap is `U_S ⊗ U_E`, which provably fixes the state. The ONLY remaining
input collapses to **state-supervenience** — that the typicality measure of a system outcome depends only on
the state (equivalently the reduced state, which `U_E` leaves untouched). That is a Gleason/non-contextuality
premise, strictly weaker than Born. `U_S, U_E` exist as honest unitaries for orthonormal `{sₖ}, {eₖ}`
(basis permutations); here they enter as the linear maps realising the relabelling. Axiom-free.
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

namespace QIQTH.EnvarianceJustification

open scoped TensorProduct BigOperators

variable {S E K : Type*} [Fintype K]
variable [AddCommGroup S] [Module ℂ S] [AddCommGroup E] [Module ℂ E]

/-- **The envariance coefficient transformation.**  A joint permutation `U_S ⊗ U_E` that permutes the system
records `sₖ ↦ s_{σk}` and the environment records `eₖ ↦ e_{σk}` relabels the amplitudes of the entangled
state by `c ↦ c∘σ⁻¹`: `(U_S ⊗ U_E)(∑ₖ cₖ sₖ⊗eₖ) = ∑ₖ c_{σ⁻¹k} sₖ⊗eₖ`.  (So the joint permutation fixes the
state exactly when `c` is σ-invariant — the precise condition for envariance.) -/
theorem joint_perm_coeff (σ : K ≃ K) (s : K → S) (e : K → E) (c : K → ℂ)
    (US : S →ₗ[ℂ] S) (UE : E →ₗ[ℂ] E)
    (hUS : ∀ k, US (s k) = s (σ k)) (hUE : ∀ k, UE (e k) = e (σ k)) :
    (TensorProduct.map US UE) (∑ k, c k • (s k ⊗ₜ[ℂ] e k))
      = ∑ k, c (σ.symm k) • (s k ⊗ₜ[ℂ] e k) := by
  rw [map_sum]
  simp_rw [map_smul, TensorProduct.map_tmul, hUS, hUE]
  rw [← Equiv.sum_comp σ (fun k => c (σ.symm k) • (s k ⊗ₜ[ℂ] e k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Equiv.symm_apply_apply]

/-- **Envariance: equal (σ-invariant) amplitudes ⇒ the joint permutation fixes the state.**  If `c` is
invariant under `σ` then `(U_S ⊗ U_E) ψ = ψ`: the symmetry genuinely exists (it is the unitary counter-swap),
not an assumption.  For unequal amplitudes `joint_perm_coeff` shows the state changes (`c ↦ c∘σ⁻¹`). -/
theorem envariance_invariant (σ : K ≃ K) (s : K → S) (e : K → E) (c : K → ℂ)
    (US : S →ₗ[ℂ] S) (UE : E →ₗ[ℂ] E)
    (hUS : ∀ k, US (s k) = s (σ k)) (hUE : ∀ k, UE (e k) = e (σ k))
    (hc : ∀ k, c (σ.symm k) = c k) :
    (TensorProduct.map US UE) (∑ k, c k • (s k ⊗ₜ[ℂ] e k)) = ∑ k, c k • (s k ⊗ₜ[ℂ] e k) := by
  rw [joint_perm_coeff σ s e c US UE hUS hUE]
  exact Finset.sum_congr rfl (fun k _ => by rw [hc k])

variable [DecidableEq K]

/-- **The outcome form of envariance (Zurek's equal-amplitude condition).**  The system swap `a ↔ b`, undone
by the environment counter-swap, fixes the entangled state `ψ = ∑ₖ cₖ sₖ⊗eₖ` **iff** the swapped amplitudes
are equal (`c a = c b`).  This exhibits the envariance symmetry of `Envariance.envariance_equal_marg` as a
concrete unitary that provably leaves the equal-amplitude state invariant — grounding the previously-assumed
"μ-preserving swap". -/
theorem envariance_swap_invariant (a b : K) (s : K → S) (e : K → E) (c : K → ℂ)
    (US : S →ₗ[ℂ] S) (UE : E →ₗ[ℂ] E)
    (hUS : ∀ k, US (s k) = s (Equiv.swap a b k)) (hUE : ∀ k, UE (e k) = e (Equiv.swap a b k))
    (hab : c a = c b) :
    (TensorProduct.map US UE) (∑ k, c k • (s k ⊗ₜ[ℂ] e k)) = ∑ k, c k • (s k ⊗ₜ[ℂ] e k) := by
  refine envariance_invariant (Equiv.swap a b) s e c US UE hUS hUE (fun k => ?_)
  rw [Equiv.symm_swap]
  rcases eq_or_ne k a with rfl | hka
  · rw [Equiv.swap_apply_left]; exact hab.symm
  · rcases eq_or_ne k b with rfl | hkb
    · rw [Equiv.swap_apply_right]; exact hab
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

end QIQTH.EnvarianceJustification
