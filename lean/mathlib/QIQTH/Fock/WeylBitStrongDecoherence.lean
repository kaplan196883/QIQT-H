/-
WeylBitStrongDecoherence.lean — STRONG decoherence of the free-field Born histories (2026-06-15)

`WeylBitConsistency` proved MEDIUM decoherence (`Re D = 0`) for all single-bit coarse-grainings — the
exact Gell-Mann–Hartle condition the Born sum rules need.  The residual flagged there: the
*multi-bit-differing* pairs (e.g. `vec(+,+)` vs `vec(−,−)` in the Bell config), whose real parts only
*sum* to zero by normalization but were not shown to vanish individually.

Here we close that residual for **orthogonal record modes** — and get more than medium: the pairs vanish
*exactly* (STRONG decoherence, `D = 0`, not just `Re D = 0`).  The mechanism: on the vacuum the Weyl
two-point function `⟪Ω, W(u)Ω⟫ = weylCoeff u 0 = exp(−½‖u‖²)` is REAL, and for orthogonal modes
`⟪u,v⟫ = 0` the Gaussian overlaps collapse via the identity `weylCoeff v 0 · weylCoeff v w · exp⟪v,v⟫ = 1`.

- `bitOp_vac_expVec_cross` — the engine: `⟪A(v,1)Ω, A(v,−1) e(w)⟫ = 0` whenever `⟪v,w⟫ = 0`.
- `vacuum_bit_strong_decoherence` — single Weyl bit on the vacuum is *exactly* orthogonal (`w = 0`
  instance): `⟪A(u,1)Ω, A(u,−1)Ω⟫ = 0`.  Upgrades medium → strong on the vacuum, the state histories
  are built on.

HONEST SCOPE: the orthogonal-mode hypothesis `⟪u,v⟫ = 0` is exactly the physical "distinct / spacelike
record" condition (disjoint mode supports).  For NON-orthogonal modes the multi-bit cross term does not
vanish — it equals `(1/8)(⟪Ω,W(u+v)Ω⟫ − ⟪Ω,W(v−u)Ω⟫)`, governed by `Re⟪u,v⟫` (the mode overlap); that
residual is the genuine record-overlap correction, suppressed by the SBS/redundancy mechanism (cited).
Axiom-free.
-/
import QIQTH.Fock.WeylBitConsistency
import QIQTH.Fock.WeylCCR
import Mathlib.Tactic

namespace QIQTH.Fock

open scoped InnerProductSpace ComplexConjugate
open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The coherent-state inner product on the pre-Fock space (the instance inner is `fockInner`). -/
private theorem inner_eVec (a b : H) :
    ⟪FockPre.expVec a, FockPre.expVec b⟫_ℂ = Complex.exp ⟪a, b⟫_ℂ := by
  show fockInner (FockPre.expVec a) (FockPre.expVec b) = _
  exact FockPre.inner_expVec a b

/-- `weylCoeff v 0 = exp(−½⟪v,v⟫)` is REAL — the vacuum Weyl one-point function is real (it is what makes
even the *single* bit strongly, not just medium, decoherent on the vacuum). -/
private theorem conj_weylCoeff_vac (v : H) :
    (starRingEnd ℂ) (Weyl.weylCoeff v 0) = Weyl.weylCoeff v 0 := by
  unfold Weyl.weylCoeff
  rw [← Complex.exp_conj]
  congr 1
  simp only [inner_zero_right, sub_zero, map_mul, inner_self_conj, map_neg, map_div₀, map_one,
    map_ofNat]

/-- **The engine: a Weyl bit on the vacuum vs on an orthogonal coherent state is strongly orthogonal.**
For `⟪v,w⟫ = 0`, the two outcomes of bit `v` — read on the vacuum `Ω` and on the coherent state `e(w)` —
have vanishing decoherence functional: `⟪A(v,1)Ω, A(v,−1) e(w)⟫ = 0`, exactly.  The Gaussian overlaps
collapse via `weylCoeff v 0 = weylCoeff v w` and `weylCoeff v 0 · weylCoeff v w · exp⟪v,v⟫ = 1`. -/
theorem bitOp_vac_expVec_cross (v w : H) (h : ⟪v, w⟫_ℂ = 0) :
    ⟪bitOp v 1 (vac H), bitOp v (-1) (FockPre.expVec w)⟫_ℂ = 0 := by
  have hb1 : bitOp v 1 (vac H)
      = (1 / 2 : ℂ) • (FockPre.expVec (0 : H) + (Weyl.weylCoeff v 0) • FockPre.expVec v) := by
    rw [show vac H = FockPre.expVec (0 : H) from rfl, bitOp_apply, one_smul, weylPre_expVec, zero_add]
  have hb2 : bitOp v (-1) (FockPre.expVec w)
      = (1 / 2 : ℂ) • (FockPre.expVec w
          + (-1 : ℂ) • (Weyl.weylCoeff v w • FockPre.expVec (w + v))) := by
    rw [bitOp_apply, weylPre_expVec]
  -- key scalar facts
  have hc : Weyl.weylCoeff v 0 = Weyl.weylCoeff v w := by
    simp only [Weyl.weylCoeff]; rw [inner_zero_right, h]
  have hid : Weyl.weylCoeff v 0 * Weyl.weylCoeff v w * Complex.exp ⟪v, v⟫_ℂ = 1 := by
    simp only [Weyl.weylCoeff]
    rw [inner_zero_right, h, ← Complex.exp_add, ← Complex.exp_add]
    conv_rhs => rw [← Complex.exp_zero]
    congr 1
    ring
  have e1 : Complex.exp ⟪(0 : H), w⟫_ℂ = 1 := by rw [inner_zero_left, Complex.exp_zero]
  have e2 : Complex.exp ⟪(0 : H), w + v⟫_ℂ = 1 := by rw [inner_zero_left, Complex.exp_zero]
  have e3 : Complex.exp ⟪v, w⟫_ℂ = 1 := by rw [h, Complex.exp_zero]
  have e4 : Complex.exp ⟪v, w + v⟫_ℂ = Complex.exp ⟪v, v⟫_ℂ := by rw [inner_add_right, h, zero_add]
  rw [hb1, hb2]
  -- Expand the (FockPre) inner product over the sums/scalars first ...
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right]
  -- ... THEN convert exponential-vector inners to `exp⟪·,·⟫` (so `inner_add_right` does not also
  -- expand the `⟪v, w+v⟫` inside the exponentials).
  simp only [inner_eVec, map_div₀, map_one, map_ofNat, conj_weylCoeff_vac]
  rw [e1, e2, e3, e4]
  linear_combination (1 / 4 : ℂ) * hc - (1 / 4 : ℂ) * hid

/-- **Single Weyl bit on the vacuum is STRONGLY decoherent.**  `⟪A(u,1)Ω, A(u,−1)Ω⟫ = 0` exactly (not
merely `Re = 0`): the two outcome history vectors are genuinely orthogonal, because the vacuum Weyl
one-point function is real.  The `w = 0` instance of `bitOp_vac_expVec_cross`. -/
theorem vacuum_bit_strong_decoherence (u : H) :
    ⟪bitOp u 1 (vac H), bitOp u (-1) (vac H)⟫_ℂ = 0 := by
  exact bitOp_vac_expVec_cross u (0 : H) (inner_zero_right u)

/-! ### The full Bell two-record configuration: ALL pairs (including multi-bit-differing) vanish -/

/-- `W(u)` is unitary with adjoint `W(−u)`: `⟪W(u)x, y⟫ = ⟪x, W(−u)y⟫` (`fockInner_weyl_adjoint`). -/
private theorem weyl_adjoint (u : H) (x y : FockPre H) :
    ⟪weylPre u x, y⟫_ℂ = ⟪x, weylPre (-u) y⟫_ℂ :=
  fockInner_weyl_adjoint u x y

/-- For symplectically orthogonal modes (`Im⟪w,v⟫ = 0`), `W(w)` commutes with the bit operator
`A(v,s)` — the microcausality of the free field (`weyl_microcausality`). -/
private theorem weylPre_bitOp_comm (w v : H) (hwv : Complex.im ⟪w, v⟫_ℂ = 0) (s : ℂ) (ψ : FockPre H) :
    weylPre w (bitOp v s ψ) = bitOp v s (weylPre w ψ) := by
  have hmc : weylPre w (weylPre v ψ) = weylPre v (weylPre w ψ) := by
    have h := LinearMap.congr_fun (weyl_microcausality w v hwv) ψ
    simpa using h
  rw [bitOp_apply, bitOp_apply, map_smul, map_add, map_smul, hmc]

/-- **The cross term `⟪A(v,1)Ω, W(w) A(v,−1)Ω⟫` vanishes** for orthogonal `w` — the engine of the
multi-bit assembly.  `W(w)` commutes through `A(v,−1)` (microcausality), acts on the vacuum as
`weylCoeff w 0 · e(w)`, and `bitOp_vac_expVec_cross` finishes. -/
private theorem cross_weyl_vanishes (v w : H) (hvw : ⟪v, w⟫_ℂ = 0) (hwv : Complex.im ⟪w, v⟫_ℂ = 0) :
    ⟪bitOp v 1 (vac H), weylPre w (bitOp v (-1) (vac H))⟫_ℂ = 0 := by
  have hwvac : weylPre w (vac H) = Weyl.weylCoeff w 0 • FockPre.expVec w := by
    rw [show vac H = FockPre.expVec (0 : H) from rfl, weylPre_expVec, zero_add]
  rw [weylPre_bitOp_comm w v hwv, hwvac, map_smul, inner_smul_right,
    bitOp_vac_expVec_cross v w hvw, mul_zero]

/-- **STRONG decoherence of the full Bell two-record configuration.**  For orthogonal record modes
`⟪u,v⟫ = 0` (the physical "distinct / spacelike records" condition), the maximally-different history
vectors `vec(+,+)` and `vec(−,−)` — differing in BOTH bits — are *exactly orthogonal*:
`⟪A(u,1)A(v,1)Ω, A(u,−1)A(v,−1)Ω⟫ = 0`.  This closes the multi-bit-differing residual left open by
`WeylBitConsistency` — and gives strong (`D = 0`), not merely medium (`Re D = 0`), decoherence.
Peel `A(u,±1)` (`W(u)` isometry + `W(u)* = W(−u)`), reducing to two `cross_weyl_vanishes` terms. -/
theorem bell_two_bit_strong_decoherence (u v : H) (huv : ⟪u, v⟫_ℂ = 0) :
    ⟪bitOp u 1 (bitOp v 1 (vac H)), bitOp u (-1) (bitOp v (-1) (vac H))⟫_ℂ = 0 := by
  have him : Complex.im ⟪u, v⟫_ℂ = 0 := by rw [huv]; simp
  have hvu : ⟪v, u⟫_ℂ = 0 := by rw [← inner_conj_symm v u, huv, map_zero]
  have hv_negu : ⟪v, -u⟫_ℂ = 0 := by rw [inner_neg_right, hvu, neg_zero]
  have him_negu : Complex.im ⟪-u, v⟫_ℂ = 0 := by rw [inner_neg_left, huv]; simp
  have key : ⟪bitOp u 1 (bitOp v 1 (vac H)), bitOp u (-1) (bitOp v (-1) (vac H))⟫_ℂ
      = (1 / 4 : ℂ) * (⟪bitOp v 1 (vac H), weylPre (-u) (bitOp v (-1) (vac H))⟫_ℂ
          - ⟪bitOp v 1 (vac H), weylPre u (bitOp v (-1) (vac H))⟫_ℂ) := by
    rw [show bitOp u 1 (bitOp v 1 (vac H))
          = (1 / 2 : ℂ) • (bitOp v 1 (vac H) + weylPre u (bitOp v 1 (vac H)))
        from by rw [bitOp_apply, one_smul],
      show bitOp u (-1) (bitOp v (-1) (vac H))
          = (1 / 2 : ℂ) • (bitOp v (-1) (vac H) + (-1 : ℂ) • weylPre u (bitOp v (-1) (vac H)))
        from by rw [bitOp_apply]]
    simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      map_div₀, map_one, map_ofNat, weyl_adjoint, weylPre_neg_cancel]
    ring
  have hA : ⟪bitOp v 1 (vac H), weylPre (-u) (bitOp v (-1) (vac H))⟫_ℂ = 0 :=
    cross_weyl_vanishes v (-u) hv_negu him_negu
  have hB : ⟪bitOp v 1 (vac H), weylPre u (bitOp v (-1) (vac H))⟫_ℂ = 0 :=
    cross_weyl_vanishes v u hvu him
  rw [key, hA, hB]
  ring

end QIQTH.Fock
