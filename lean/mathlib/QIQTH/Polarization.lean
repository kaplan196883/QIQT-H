/-
  Polarization — the cubic diagonal-vanishing ⟹ full-symmetrization identity.

  Route-(c) Lemma 5 of the RNC-gauge discharge (THE_EXP_JETS_PLAN.md, the GPT-5.5-pro pivot).
  Standalone multilinear algebra: for a trilinear (continuous) map `T` whose diagonal `T x x x`
  vanishes for every `x`, the FULL symmetrization over the six argument permutations vanishes.
  This is the polarization step that turns the radial-geodesic identity `DΓ̃₀(v)(v,v) = 0 ∀v`
  (obtained by differentiating `Γ̃(s·v)(v,v)=0` at `s=0`) into the symmetrized normal-coordinate
  gauge condition `∂_(l Γ̃^i_{jk)}(0) = 0`.

  Pure `ℝ`-multilinearity + `abel`; no geometry, no `exp`-map dependency (hence a fresh file, no
  contention with the in-flight `ExpMap.lean` work).  HONEST: an algebraic identity — it does NOT
  by itself discharge the gauge (that needs the radial identity `DΓ̃₀ x x x = 0`, Lemmas 1–4),
  NOT the pullback metric, NOT numerical-G.
-/
import Mathlib

namespace QIQTH.Polarization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **The polarization identity for the cubic diagonal.**  For a trilinear continuous map
    `T : V →L V →L V →L W`, the six-fold symmetrization equals the inclusion–exclusion combination
    of the diagonal `P x := T x x x` over the sub-sums of `{a,b,c}`:
    `∑_{σ∈S₃} T aσ bσ cσ = P(a+b+c) − P(a+b) − P(a+c) − P(b+c) + P(a) + P(b) + P(c)`.
    Pure multilinearity (`map_add` + `ContinuousLinearMap.add_apply`), closed by `abel`. -/
theorem sixSym_eq_incl_excl (T : V →L[ℝ] V →L[ℝ] V →L[ℝ] W) (a b c : V) :
    T a b c + T a c b + T b a c + T b c a + T c a b + T c b a
      = T (a + b + c) (a + b + c) (a + b + c)
        - T (a + b) (a + b) (a + b) - T (a + c) (a + c) (a + c) - T (b + c) (b + c) (b + c)
        + T a a a + T b b b + T c c c := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

/-- **Cubic diagonal vanishing ⟹ full symmetrization vanishes.**  If `T x x x = 0` for every `x`
    (the radial-geodesic identity in normal coordinates), then the six-fold symmetrization of `T`
    vanishes identically.  With lower-index Christoffel symmetry this is exactly the symmetrized
    RNC gauge `∂_(l Γ̃^i_{jk)}(0) = 0`.  Proof: the inclusion–exclusion identity `sixSym_eq_incl_excl`
    with every diagonal term killed by `hdiag`. -/
theorem trilinear_diag_zero_fullSymm (T : V →L[ℝ] V →L[ℝ] V →L[ℝ] W)
    (hdiag : ∀ x, T x x x = 0) (a b c : V) :
    T a b c + T a c b + T b a c + T b c a + T c a b + T c b a = 0 := by
  rw [sixSym_eq_incl_excl T a b c,
    hdiag (a + b + c), hdiag (a + b), hdiag (a + c), hdiag (b + c), hdiag a, hdiag b, hdiag c]
  abel

end QIQTH.Polarization
