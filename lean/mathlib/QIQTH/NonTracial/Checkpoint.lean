/-
  THE NON-TRACIALITY CAMPAIGN (N1–N4) — THE CAMPAIGN CHECKPOINT (all increments landed;
  axiom-free std-3, budget 0; every increment first-try green).

  HAVE: "The tower limit state is a genuine non-tracial KMS state, machine-checked. Its
  canonical vector state ω(·) = ⟪Ω, π(·)Ω⟫ = tr(ρ_C ·) is NOT a trace: on the matrix units
  a = E_{nm}, b = E_{mn} at any stage where the Gibbs weights differ (w_n ≠ w_m),
  ω(π(a)π(b)) = w_n ≠ w_m = ω(π(b)π(a)). Equivalently the modular data is non-trivial: the
  modular operator acts non-identically, Δ↑(of C E_{nm}) = (w_n/w_m)•↑(of C E_{nm}) ≠
  ↑(of C E_{nm}) on a nonzero pure-component eigenvector, and the modular unitary group
  Δ^{it} = towerFlow is not the identity flow (∃ t, U_t v ≠ v). So Ω is not a tracial vector
  and towerLimitVN, in this state, is not in tracial standard form — the Powers
  'not-the-tracial-case' separation, at the resolution the finite modular eigenbasis
  delivers."

  HAVE NOT: "This does NOT show towerLimitVN is 'not type II₁' as an ALGEBRA statement — ω
  being non-tracial does not preclude some OTHER faithful normal tracial state (each finite
  stage is a full matrix algebra, type I_finite, and DOES carry the normalized trace; ω simply
  is not it). No type III / III_λ / III₁ claim, no Connes S-invariant, no
  modular-spectrum-closure statement is made or proved — those need the crossed-product /
  flow-of-weights machinery, which is absent from Mathlib and the repo and depends on
  weight-sequence asymptotics the finite eigenbasis cannot see. Mathlib has no
  trace/tracial-state/factor/type API at this pin, so 'no tracial state exists' is not even
  stateable here; only the concrete inequalities are proved. Araki–Woods 1968, Connes 1973,
  and Buchholz–Wichmann (local algebras type III₁) stay CITED, never invoked. Everything
  remains the finite-stage Gibbs inductive-limit state; the free-field/Type-III continuum
  objects are untouched."
-/
import QIQTH.NonTracial.FiniteNonTrace
import QIQTH.NonTracial.TowerNonTrace
import QIQTH.NonTracial.ModularNonTrivial

namespace QIQTH.NonTracial

/-- Marker: THE NON-TRACIALITY CAMPAIGN complete (N1–N4). See the file docstring for the
verbatim HAVE / HAVE-NOT. This is state non-traciality + modular non-triviality only —
explicitly NOT a type classification. -/
theorem non_traciality_campaign_complete : True := trivial

end QIQTH.NonTracial
