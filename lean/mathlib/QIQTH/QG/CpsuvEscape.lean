/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# J6 — the CPSUV escape-in-principle certificate: capacity ⊕ Lorentz-covariance, structurally decoupled

The capstone of `COVARIANT_CAPACITY_CPSUV_PLAN.md`. The campaign established (J1–J4): the one-loop speed
splitting `Δc²` is sourced by the regulator's frame anisotropy; `Δc² = 0 ⟺` the matter UV symbol is Lorentz-
scalar `⟺ B = 0` (J3); a modular/diamond *mode* cutoff always sources `Δc² ≠ 0` (J1/J4); and QIQT-H's actual
capacity is an algebraic record-COUNT, not a mode cutoff (J2). GPT-5.5-pro's J6 verdict (rigorous): the
**crossed-product Type II construction** (Chandrasekaran–Longo–Penington–Witten / Witten, *Gravity and the
Crossed Product*) genuinely escapes CPSUV — the matter wedge algebra stays **Type III₁** (an ordinary
Lorentz-covariant local QFT, propagators UNMODIFIED ⟹ `B = 0` ⟹ `Δc² = 0`), while the **finite renormalized
entropy `S_ren ≤ Q = A(∂D)/4ℓ_P²` comes from the Type II trace `τ`, NOT a matter mode cutoff**. The modular flow
crossed in is *wedge-covariant* (`τ_{gW}∘Φ_g = τ_W`), not frame-fixing, and the observer/clock variable does not
multiply matter propagators. So **finiteness (a trace property) and Lorentz-covariance (the matter symbol) are
structurally DECOUPLED.**

This file formalizes the **escape-in-principle certificate**: a structure carrying simultaneously a Lorentz-scalar
matter sector (`Δc² = 0`, via J3) and a finite capacity bound (`S_ren ≤ Q`), with the matter frame and the
clock/modular frame as **independent type parameters** — proving the two are JOINTLY realizable, non-vacuously,
with no shared frame. Hence the CPSUV inference "finite capacity ⟹ frame-picking regulator ⟹ `B ≠ 0` ⟹
`Δc² ≠ 0`" is **refuted**: capacity does not force anisotropy.

**Honest scope (what this does NOT prove — the cited frontier, GPT-5.5-pro's single remaining obstruction):** the
upgrade from the Type II trace entropy bound to QIQT-H's *literal per-diamond record cardinality*
`card(P.X D) ≤ exp(Q_D)` (a Type II factor is diffuse; trace-dimension ≠ Hilbert dimension); the full finite-`G`,
all-diamonds Standard-Model-plus-gravity crossed-product construction; and `τ(p_D) = exp(A(∂D)/4ℓ_P²)` per
causal diamond. Those remain research-grade. Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`);
never claim the value of `G`; the `1/4` ratio is derived (`SakharovRatio.lean`).

⚠️ **RED-TEAM CAVEAT (GPT-5.5-pro adversarial second opinion, 2026-06-30).** The theorems below are TRUE but
**conditional / near-tautological**: they *assume* the decoupling (Lorentz-scalar matter `B = 0` AND an
independent capacity sector) and conclude `Δc² = 0` ∧ finite capacity. They do **NOT** prove the physical
decoupling. The substantive claim "QIQT-H escapes CPSUV" is **NOT established** and faces a dilemma: (i) if the
matter propagators are genuinely unmodified, the finite capacity does no matter-UV work — the "escape" is
**vacuous** (ordinary Type III₁ QFT with finiteness relabelled into a trace); (ii) if capacity is made literal/
operational, it must restrict states/records and likely destroys the Type III₁ structure or reintroduces a
modular-time/observer frame — **reopening CPSUV**. Worse, a literal finite `card(P.X D)` is in structural tension
with the diffuse Type III₁ matter algebra (no atoms, no finite trace, and noncompact Lorentz has no nontrivial
finite-dim unitary reps). The red-team estimate for the substantive claim is **only ~10–20%**, with the
trace/cardinality/type mismatch the most likely **fatal** flaw. So read this file as a *structural conditional*
(the algebra of the decoupling IF it holds), NOT as a proof that QIQT-H reconciles finite capacity with Lorentz.
See `COVARIANT_CAPACITY_CPSUV_PLAN.md` §6′ and `TRACE_CARDINALITY_SCOPE.md`.
-/
import QIQTH.QG.WardSpeedSplitting

namespace QIQTH.QG

/-- **The matter sector.** Kinetic form `Γ⁽²⁾ = A·p² + B·(u·p)²` (J3), with the **Lorentz-scalar condition
`B = 0`** — the matter UV kernel is covariant (a proper-time / □ / Pauli–Villars kernel = the unmodified
Type III₁ local-QFT propagator), NOT a mode / modular-energy cutoff. `MatterFrame` records that the matter
sector carries its OWN frame data, kept a free type parameter independent of the capacity sector. -/
structure MatterSector (MatterFrame : Type) where
  A : ℝ
  B : ℝ
  hAB : A + B ≠ 0
  scalar : B = 0

/-- The speed splitting of the matter sector, via J3 (`speedSplitting`). -/
noncomputable def MatterSector.Δc2 {MF : Type} (m : MatterSector MF) : ℝ :=
  speedSplitting (m.A + m.B) m.A

/-- **The matter sector is Lorentz-safe: `Δc² = 0`** (from `B = 0`, by the J3 dichotomy
`speedSplitting_aniso_eq_zero_iff`). -/
theorem MatterSector.Δc2_eq_zero {MF : Type} (m : MatterSector MF) : m.Δc2 = 0 :=
  (speedSplitting_aniso_eq_zero_iff m.A m.B m.hAB).mpr m.scalar

/-- **The capacity sector.** A finite renormalized entropy `Sren` bounded by the holographic capacity `Q`
(`Sren ≤ Q`, `Q = A(∂D)/4ℓ_P²`) — supplied by the crossed-product Type II trace (CLPW/Witten; our
`Phase5Master`/`FiniteTracePhase5` instance), NOT by any matter mode cutoff. `ClockFrame` records the
modular/observer-clock data, a free type parameter independent of the matter sector. -/
structure TraceCapacity (ClockFrame : Type) where
  Sren : ℝ
  Q : ℝ
  bound : Sren ≤ Q

/-- **★ J6 — the CPSUV escape-in-principle certificate.** A structure carrying simultaneously a Lorentz-scalar
matter sector (`Δc² = 0`) and a finite capacity bound (`Sren ≤ Q`), with `MatterFrame` and `ClockFrame` as
**independent type parameters** — the formal expression of the structural decoupling: covariant Type III₁ matter
(no mode cutoff ⟹ no preferred frame ⟹ `B = 0`) ⊕ finite Type II trace (the area/entropy bound). The capacity
sector carries NO matter-frame datum; the matter sector carries NO clock/modular cutoff. -/
structure EscapeCertificate (MatterFrame ClockFrame : Type) where
  matter : MatterSector MatterFrame
  cap : TraceCapacity ClockFrame

namespace EscapeCertificate

theorem deltaC2_zero {MF CF : Type} (E : EscapeCertificate MF CF) : E.matter.Δc2 = 0 :=
  E.matter.Δc2_eq_zero

theorem capacity_bound {MF CF : Type} (E : EscapeCertificate MF CF) : E.cap.Sren ≤ E.cap.Q :=
  E.cap.bound

/-- **The escape core:** Lorentz-safety (`Δc² = 0`) AND finite capacity (`Sren ≤ Q`) hold **simultaneously** in
one certificate — covariant matter and finite capacity coexist. -/
theorem escape_core {MF CF : Type} (E : EscapeCertificate MF CF) :
    E.matter.Δc2 = 0 ∧ E.cap.Sren ≤ E.cap.Q :=
  ⟨deltaC2_zero E, capacity_bound E⟩

end EscapeCertificate

/-- **Non-vacuity — the escape is UNOBSTRUCTED in principle.** For any nonnegative capacity `Q`, an escape
certificate EXISTS: a Lorentz-scalar matter sector (`B = 0 ⟹ Δc² = 0`) paired with a finite capacity bound
(`Sren ≤ Q`). So covariant matter and finite capacity are JOINTLY realizable — no contradiction. -/
theorem escape_certificate_exists (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ E : EscapeCertificate PUnit PUnit, E.matter.Δc2 = 0 ∧ E.cap.Sren ≤ E.cap.Q :=
  ⟨⟨⟨1, 0, by norm_num, rfl⟩, ⟨0, Q, hQ⟩⟩, EscapeCertificate.escape_core _⟩

/-- **★ The anti-CPSUV theorem.** A finite capacity bound does **not** force matter anisotropy: there is an
escape certificate with `Sren ≤ Q` whose matter is Lorentz-scalar (`B = 0`). This refutes the CPSUV inference
"finite capacity ⟹ a frame-picking matter regulator ⟹ `B ≠ 0` ⟹ `Δc² ≠ 0`": capacity and Lorentz violation are
**decoupled** (the capacity lives in the trace, the Lorentz-safety in the matter symbol). -/
theorem capacity_not_force_anisotropy (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ E : EscapeCertificate PUnit PUnit, E.cap.Sren ≤ E.cap.Q ∧ E.matter.B = 0 :=
  ⟨⟨⟨1, 0, by norm_num, rfl⟩, ⟨0, Q, hQ⟩⟩, hQ, rfl⟩

end QIQTH.QG
