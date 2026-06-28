/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# PHOTON_FIELD_PLAN P2 — the truncated bosonic (symmetric) Fock dimension

The photon is **bosonic**: its Fock space is the *symmetric* algebra `Γ_s(h)` over the physical
one-particle space `h` (the transverse / helicity-±1 photon modes).  Unlike the electron's CAR/exterior
Fock `⋀ h` (finite-dimensional, `dim = 2^(dim h)`), the **bosonic** Fock `Γ_s(h)` is
*infinite-dimensional even for finite-dimensional `h`* — so the photon's regional **capacity is unbounded
without a cutoff** (`PHOTON_FIELD_PLAN` §0, the structural difference from CAR).

The physically meaningful finite object is the **number-cutoff** Fock space
`Γ_s^{≤N}(h) = ⊕_{k=0}^{N} Sym^k(h)` (at most `N` photons).  Its dimension is

  `dim Γ_s^{≤N}(h) = ∑_{k=0}^{N} dim Sym^k(h) = ∑_{k=0}^{N} multichoose(d, k) = C(d + N, N)`,  `d = dim h`,

the count of monomials of total degree `≤ N` in `d` variables.  This module proves that closed form
(`truncFockDim_eq_choose`) — the analytic core of the photon finite-capacity bound (P3, the bosonic mirror
of the electron's CAR `S ≤ log dim(⋀h_R)`, now `S ≤ log C(dim h_γ + N, N)`, **with the number cutoff `N`**).

Proof: induction on `N` + Pascal's rule (`Nat.choose_succ_succ`), using `Nat.multichoose_eq`
(`multichoose d k = (d+k-1).choose k`).  Pure `ℕ` combinatorics — no Fock analytic structure needed for
the dimension count, exactly as the electron capacity bound reduced to `dim(⋀h)=2^n`.

Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.  Free Maxwell only.
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace QIQTH.Fock.Photon

open Finset

/-- **The truncated bosonic Fock dimension** `dim Γ_s^{≤N}(h)` for `d = dim h`: the number of bosonic
states with at most `N` photons in `d` modes, `∑_{k=0}^{N} dim Sym^k(h) = ∑_{k=0}^{N} multichoose(d,k)`.
`Sym^k` of a `d`-dim space has dimension `multichoose(d,k) = C(d+k-1,k)` (monomials of degree exactly
`k` in `d` variables); summing `k = 0..N` gives the `≤ N`-photon sector. -/
def truncFockDim (d N : ℕ) : ℕ := ∑ k ∈ range (N + 1), Nat.multichoose d k

@[simp] theorem truncFockDim_zero_photons (d : ℕ) : truncFockDim d 0 = 1 := by
  simp [truncFockDim, Nat.multichoose_zero_right]

/-- **The number-cutoff recurrence**: raising the cutoff by one photon adds exactly the new top sector
`Sym^{N+1}(h)` of dimension `multichoose(d, N+1)`:
`dim Γ_s^{≤N+1}(h) = dim Γ_s^{≤N}(h) + multichoose(d, N+1)`. -/
theorem truncFockDim_succ (d N : ℕ) :
    truncFockDim d (N + 1) = truncFockDim d N + Nat.multichoose d (N + 1) := by
  rw [truncFockDim, Finset.sum_range_succ, ← truncFockDim]

/-- **The closed form: `dim Γ_s^{≤N}(h) = C(d + N, N)`.**  The number of bosonic states of `d` modes with
at most `N` photons equals `C(d+N, N)` — the count of monomials of total degree `≤ N` in `d` variables.
Proof: induction on `N`; the step is exactly Pascal's rule
`C(d+N+1, N+1) = C(d+N, N) + C(d+N, N+1)`, with the new `(N+1)`-photon sector
`multichoose(d, N+1) = C(d+N, N+1)`.  This is the analytic heart of the photon finite-capacity bound
(P3): a *finite* dimension only because of the photon-number cutoff `N` (the bosonic Fock is otherwise
infinite-dimensional — the structural contrast with the electron's finite CAR `dim ⋀h = 2^(dim h)`). -/
theorem truncFockDim_eq_choose (d N : ℕ) : truncFockDim d N = (d + N).choose N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [truncFockDim_succ, ih]
    -- new top sector: multichoose d (N+1) = (d + N).choose (N+1)
    have hmc : Nat.multichoose d (N + 1) = (d + N).choose (N + 1) := by
      rw [Nat.multichoose_eq, show d + (N + 1) - 1 = d + N from by omega]
    rw [hmc]
    -- Pascal: (d+N+1).choose (N+1) = (d+N).choose N + (d+N).choose (N+1)
    rw [show d + (N + 1) = (d + N) + 1 by ring, Nat.choose_succ_succ]

/-- **Bosonic capacity needs a cutoff (monotonicity in `N`).**  `dim Γ_s^{≤N}(h)` is (weakly) increasing
in the photon-number cutoff `N`: more allowed photons can only add states.  Together with the fact that
`Sym^k(h) ≠ 0` for every `k` when `dim h ≥ 1`, this is the finite-`N` shadow of the photon's *unbounded*
capacity as `N → ∞` (the bosonic Fock `Γ_s(h)` is infinite-dimensional) — the reason the photon capacity
bound (P3) is stated *only* with a number cutoff, unlike the electron's cutoff-free CAR bound. -/
theorem truncFockDim_mono (d : ℕ) : Monotone (truncFockDim d) := by
  intro M N hMN
  rw [truncFockDim_eq_choose, truncFockDim_eq_choose]
  have eM : (d + M).choose M = (d + M).choose d := by
    have h := Nat.choose_symm (n := d + M) (k := M) (Nat.le_add_left M d)
    rw [show d + M - M = d by omega] at h
    exact h.symm
  have eN : (d + N).choose N = (d + N).choose d := by
    have h := Nat.choose_symm (n := d + N) (k := N) (Nat.le_add_left N d)
    rw [show d + N - N = d by omega] at h
    exact h.symm
  rw [eM, eN]
  exact Nat.choose_le_choose d (by omega)

/-- **Strict growth for a nonempty mode space** (`d ≥ 1`): adding photon capacity strictly increases the
truncated dimension, `dim Γ_s^{≤N}(h) < dim Γ_s^{≤N+1}(h)`.  Each new top sector `Sym^{N+1}(h)` is
nonzero (`multichoose(d, N+1) ≥ 1` for `d ≥ 1`), so the dimension strictly climbs with `N` — the photon
capacity has **no finite ceiling**; only the cutoff `N` makes it finite.  (The clean statement of the
"`sup S = ∞` without a cutoff" corollary flagged in `PHOTON_FIELD_PLAN` §0/P3.) -/
theorem truncFockDim_strictMono (d : ℕ) (hd : 1 ≤ d) :
    truncFockDim d N < truncFockDim d (N + 1) := by
  rw [truncFockDim_succ]
  have : 1 ≤ Nat.multichoose d (N + 1) := by
    rw [Nat.multichoose_eq]
    apply Nat.choose_pos
    omega
  omega

end QIQTH.Fock.Photon
