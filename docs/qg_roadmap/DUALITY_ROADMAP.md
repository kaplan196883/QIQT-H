# DUALITY ROADMAP — what separates the verified dictionary from a genuine duality

**Date:** 2026-07-11. **Companions:** `ADSCFT_GAP_ANALYSIS.md` (the mechanism-by-mechanism
comparison), `WHERE_WE_ARE.md` (the full-credit status), `FLAT_RECORD_GRAVITY_CONJECTURE.md`
(the target statement). **Definition used throughout:** a DUALITY is two independently defined
theories provably describing the same physics; a DICTIONARY is a set of proven correspondences
between two bookkeepings of one constructed object. QIQT-H today holds the dictionary (much of it
as theorems); this file enumerates exactly what is missing for the duality, item by item, each
with its Lean-precise obstruction status.

## The six missing pieces

### D1 — an interacting boundary Hamiltonian (the theory itself)
The boundary has kinematics, thermodynamics, and dissipation — but its unitary dynamics is FREE
(`Hcode = Σ ω_k N_k`; `alpha_diagonal` PROVES the free flow cannot create records) and record
formation is a coupling MODEL (IC1's pure-dephasing/measurement limit, einselection derived at the
Cesàro level). A duality needs one self-contained interacting Hamiltonian on the code from which
the dephasing, the geometry-decoding correlations, and the equilibria all FOLLOW.
**Status:** the pointer-competition case `[H_S, A] ≠ 0` is the named next brick; nothing
structural blocks it — it is unbuilt, not obstructed.

### D2 — the large-capacity limit as an actual limit theory (the N → ∞ slot)
The exact CCR is recovered as D → ∞ at bounded occupations (DS1 `commutator_eventually_exact`)
and the limit algebra `towerLimitVN` exists with its COMPLETE modular theory — but the ladder
stops two rungs short:
- **JMJ = M′ past the Kaplansky gap** (LA1′: the equality holds pointwise on the cyclic orbit;
  the obstruction is Lean-precise — the RATIO-weighted Frobenius operator bound vs the
  COLUMN-weighted GNS bound are inequivalent quadratic forms; the Δ-smoothing route is the named
  escape);
- **the type III₁ classification** (the Araki–Woods fingerprint is proven arithmetically, T1–T8;
  the operator inference is CITED — and no proof assistant has a factor/type API).
Without the completed limit, "the boundary theory contains the graviton" remains a
truncated-avatar statement (EM1–EM7), not a spectral one.
**Status:** two named rungs, each with a characterized obstruction.

### D3 — THE STRONG HALF OF DECOUPLING (the duality-making theorem; the center)
DS1–DS7 proved the weak half: the MATTER sector survives the cutoff limit, and the area weight is
rigid. A duality requires the GEOMETRY side to survive the SAME limit from the SAME parent — so
that `S = A/4G` becomes a consistency theorem of ONE theory rather than two bookkeepings
calibrated to shared primitives (`AdSCFTComparison.lean`'s exact diagnosis of what AdS/CFT
uniquely has). This statement EXISTS as the named Prop **`FlatSpaceRecordGravityCorrespondence`**
(`Conjectures.lean`): micro continuum record entropy = one-loop conical entropy = area/4G_ind,
ONE microscopic system computing both the states and G. Its finite half is PROVEN
(`finiteEvidence_holds`); the continuum half is the conjecture.
**Status:** stated, finite-evidenced, open. Proving it IS acquiring the duality.

### D4 — bulk dynamics from boundary dynamics
Held: statics (equilibria are Einstein states — `boundary_dynamics_equilibria_are_geometry`,
E4-conditional) and the decoder (`reconstruct` — metric from area data). Missing: the theorem
that boundary EVOLUTION generates bulk EVOLUTION. Even the composable first rung — the RC
relaxation trajectory `T_s ρ` inducing a metric trajectory `h(s)` through the held area probes,
with its evolution law inherited from the flow — is not built. (In AdS/CFT this is automatic:
one Hamiltonian, two readings.)
**Status:** first rung composable from held pieces; unbuilt.

### D5 — the radial dimension
Entanglement-at-all-scales becoming the holographic direction (Maldacena's U = RG scale). Held:
the substrate (exact RT = `maxFlow_min_cut`, unconditional; the refinement tower with its rigid
forced-weight invariant; state-decoded geometry through dS₂). Missing: the scale-as-dimension
theorem — the decoded bulk is spatial and single-scale.
**Status:** substrate unconditional; the theorem absent.

### D6 — protection (what makes a dictionary RIGID)
Non-renormalization is why AdS/CFT's dictionary has fixed coefficients. No analogue exists here,
which is why `N_eff/4`, `Λ_s`, and the heat-kernel `c_i` float — with the `c_i` blocker (the
`(1/6−ξ)` Seeley–DeWitt coefficient) gated on the ecosystem-wide Riemannian heat-kernel gap that
no proof assistant has crossed. Without protection, even a proven correspondence is a
one-parameter FAMILY of dictionaries, not THE dictionary.
**Status:** absent; the deepest blocker is external (Mathlib's own diff-geo frontier).

## The dependency structure and the critical path

```
D1 (interacting H)  ──►  D2 (limit theory)  ──►  D3 (strong decoupling = THE DUALITY)
       │
       └──►  D4 (bulk dynamics)                 D5, D6: parallel tracks
```

D1 → D2 → D3 is a chain: the interacting theory feeds the limit; the limit is where the
strong-decoupling conjecture lives. D4 hangs off D1 (needs dynamics worth transporting). D5 and
D6 are parallel and independently valuable.

**The critical path to "duality" is exactly three objects long:** the interacting code
Hamiltonian (D1), the completed limit algebra (D2), and the DY7 continuum correspondence (D3) —
and the third is already written down with its finite half proven.

## Suggested next bricks (each loop-sized, in path order)

- **D1a:** the pointer-competition model — `H = H_S + A⊗B` with `[H_S, A] ≠ 0`; target: the
  einselected basis as a function of the coupling strength (the honest hard case of IC1).
- **D4a:** the statics→dynamics rung — `h(s) := reconstruct(δA(T_s ρ))` and its evolution law
  (composable from held pieces; the first machine-checked "boundary relaxation drives bulk
  geometry in time").
- **D2a:** the Δ-smoothing campaign (the Kaplansky escape — mollify the compression approximants
  by bounded functions of the held Δ).
- **D3a:** the first continuum rung of `FlatSpaceRecordGravityCorrespondence` (scope with a
  design consult; the conjecture's finite evidence names the shape).

## HONEST scope firewall (binding)

This file plans; it claims nothing. Every "held" item above carries its original conditions
(capacity postulate, hTkk, Clausius floor, carried BW/CHM/IW where applicable, finite corners
where stated). Proving D1–D6 in full is the QG-core of the tier roadmap — research-grade, not
increment-grade; the bricks listed are the honest loop-sized entry points, and checkpointing at
genuine walls remains the discipline. NOT QG; not a claim that the duality exists.
