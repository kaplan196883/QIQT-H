/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P3 — the photon finite-capacity bound `S_vN ≤ log C(dim h_γ + N, N)`

The bosonic mirror of the electron's CAR capacity bound `S_vN ≤ log dim(⋀h_R)`
(`QIQTH/FQBoundMicro.lean` `vonNeumannEntropy_le_log_card`, the honest von Neumann max-entropy bound),
now on the **number-cutoff bosonic Fock** `Γ_s^{≤N}(h_γ)`.  The photon is bosonic, so its Fock space is
*infinite-dimensional* even for a finite one-particle space — the regional von Neumann entropy is bounded
only once a photon-number cutoff `N` is imposed.  With that cutoff the bound is finite and explicit:

  `S_vN(ρ) ≤ log dim Γ_s^{≤N}(h_γ) = log C(dim h_γ + N, N)`,

via `truncFockDim_eq_choose` (P2, `dim Γ_s^{≤N}(h) = C(d+N, N)`) fed into the cutoff-free von Neumann
bound `S_vN ≤ log (Fintype.card)`.  The companion `photon_capacity_unbounded` states the contrast with the
electron: the truncated dimension is **unbounded as `N → ∞`** (`truncFockDim_strictMono`, `d ≥ 1`), so the
photon's regional capacity has no finite ceiling without the cutoff — the "`sup S = ∞` without a cutoff"
fact of `PHOTON_FIELD_PLAN` §0/P3 (the structural reason the photon bound is stated only with `N`).

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only; the
area-term coefficient (`A/4ℓ_P²`) is never assigned — only the capacity *form* is proved here.
-/
import QIQTH.Fock.Photon.PhotonFock
import QIQTH.FQBoundMicro

namespace QIQTH.Fock.Photon

open QIQTH.QuantumEntropy

/-- `n ≤ f n` for a strictly monotone `f : ℕ → ℕ` (elementary; used for the capacity-unboundedness
contrast). -/
private theorem nat_le_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.lt_of_le_of_lt ih (hf (Nat.lt_succ_self k))

/-- **★ The photon finite-capacity bound** `S_vN(ρ) ≤ log C(dim h_γ + N, N)`.  For any density matrix `ρ`
on the number-cutoff bosonic Fock `Γ_s^{≤N}(h_γ)` (dimension `truncFockDim d N = C(d+N, N)`, `d = dim h_γ`),
the von Neumann entropy is at most the log of that finite dimension.  The bosonic mirror of the electron's
CAR `S_vN ≤ log dim(⋀h_R)` — but **finite only because of the photon-number cutoff `N`** (the bosonic Fock
is otherwise infinite-dimensional).  Proof: the cutoff-free von Neumann bound `S_vN ≤ log(Fintype.card)`
(`QIQTH.vonNeumannEntropy_le_log_card`) on `Fin (truncFockDim d N)`, rewritten through `Fintype.card_fin`
and the P2 closed form `truncFockDim_eq_choose`. -/
theorem photon_capacity_bound {d N : ℕ}
    {ρ : Matrix (Fin (truncFockDim d N)) (Fin (truncFockDim d N)) ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ Real.log ((d + N).choose N) := by
  rw [← truncFockDim_eq_choose]
  have key := QIQTH.vonNeumannEntropy_le_log_card h
  rwa [Fintype.card_fin] at key

/-- **The capacity has no finite ceiling without a cutoff** (`d = dim h_γ ≥ 1`).  The truncated bosonic
dimension `dim Γ_s^{≤N}(h_γ)` exceeds *any* bound `B` for large enough `N` (it is strictly increasing in
`N`, `truncFockDim_strictMono`).  So `log dim Γ_s^{≤N}(h_γ) → ∞`: the photon's regional von Neumann
capacity is **unbounded** as the photon-number cutoff is removed — the structural contrast with the
electron's cutoff-free finite CAR capacity (`dim ⋀h = 2^(dim h)`), and the reason `photon_capacity_bound`
is stated only with the cutoff `N`. -/
theorem photon_capacity_unbounded (d : ℕ) (hd : 1 ≤ d) (B : ℕ) :
    ∃ N, B < truncFockDim d N := by
  have hmono : StrictMono (truncFockDim d) :=
    strictMono_nat_of_lt_succ fun _ => truncFockDim_strictMono d hd
  exact ⟨B + 1, lt_of_lt_of_le (Nat.lt_succ_self B) (nat_le_of_strictMono hmono (B + 1))⟩

end QIQTH.Fock.Photon
