# Symbolic (sympy) verification — off-gate reconciliation of the mixed `hNormalForm` (J4-792)

Independent sympy cross-check of the two algebraic/analytic facts underlying
`QIQTH/MixedNormalFormFull.lean` (`witnessMixed_hNormalForm_full`), which extends the on-gate
`mTerm`-form match (J4-790, `witnessMixed_gate_eq_mTerm`) to the FULL `∀ζ` `hNormalForm` that
`MixedSliverXUniform.witness_sliver2_xuniform_mixed` consumes pointwise at every field point.

The Lean proof splits on `ζ ∈ S z₀` (on gate, via the J4-790 match with transparent gated amplitudes)
vs `ζ ∉ S z₀` (off gate). This document verifies the OFF-gate half.

## Fact 1 — off-gate `mTerm`-sum with zeroed (S-gated) amplitudes is identically 0

With the `Set.indicator (S z₀)`-gated amplitude fields (`gateAmp`), off the gate all four amplitudes
`A0, A1i, A1j, A2` are `0`. Each normal-form term is `gaussDdim · (geometric factor) · A`, so the whole
four-term sum collapses:

    mTerm0 + mTerm1(i) + mTerm1(j) + sTerm2
      = g·H·A0 + g·grad·A1i + g·grad·A1j + g·A2
      = 0            (all amplitudes 0)   ✓  (sympy: `simplify(tot) == 0` → True)

This is the RHS-vanishing that matches the (also-zero) witness partial. The nonzero Gaussian
`gaussDdim τ (V ζ)` is harmless precisely BECAUSE the amplitude carries the gate — the reason the RAW
`chartFieldAmp` (radial-cutoff only, NOT S-gated) would fail off-gate is confirmed by contrast.

## Fact 2 — a kernel whose radial cutoff vanishes before the gate boundary has zero 2nd derivative there

The witness partial's off-gate vanishing (`hOffNhd` ⟹ `pd_pd_mixed_eq_zero_of_eventuallyZero`) requires the
witness to be `0` on a NEIGHBORHOOD of each off-gate point. In the open exterior of the open gate this is
automatic; at the boundary `∂(S z₀)` it holds exactly when `radialCutoff a b (chart …)` has already killed
the parametrix before the boundary (the geometric `S z₀ ⊇ radial support` condition). Modelling the witness
by a smooth bump supported in `|x| < 0.5` inside a gate `|x| < 1`:

    witness(x) = exp(-1/(0.25 - x²))·[|x|<0.5]     (radial cutoff support strictly inside the gate)
    witness''(0.9) = 0     and     amplitude(0.9) = 0     ✓  (sympy)

so both the second derivative and the amplitude vanish at the off-gate point `x = 0.9`, exactly as the
reconciliation requires. This is the honest geometric content the `hOffNhd` hypothesis packages.

## Result

Both facts verified with sympy 1.14.0, zero discrepancies. The off-gate reconciliation is algebraically and
analytically sound; the sole carried residue (`hOffNhd`, the chart-surface `S ⊇ radial support` germ) is a
genuine geometric input, satisfiable (e.g. `S z₀ = Set.univ` makes the off-gate case vacuous, or the witness
`≡ 0`), and is NOT the conclusion.

**This is a verification artifact. NOT `a₁ = R/6` — `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv,
hCConv}`.**
