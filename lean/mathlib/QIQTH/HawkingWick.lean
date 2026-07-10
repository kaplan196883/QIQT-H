/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# HAWKING–WICK — imaginary time: the Wick identities, the two faces of 2π, and the
thermal reread (brick E3, campaign close)

Closing brick of the HAWKING–EUCLIDEAN campaign
(`docs/qg_roadmap/HAWKING_EUCLIDEAN_PLAN.md`).

## (1) Wick rotation — why the Riemannian GH program is the thermal layer

The formal substitution `t = iτ` turns the (1+1)-Lorentzian interval
`σ_L = −t² + x²` into the Euclidean quadratic form `σ_E = τ² + x²`
(`wick_identity`, an elementary complex-number identity, machine-checked here).
This identity is the reason the COMPLETED Riemannian Gromov–Hausdorff program of
this repository (cones, cubes, tori) constitutes the *thermal / equilibrium-spacetime*
layer of the framework: Euclidean sections compute static and thermal physics.

## (2) THE TWO FACES OF 2π

* **Geometric face** — `QIQTH.ConeFlat.cone_flat_iff` (brick E2): the Euclidean
  near-horizon cone `Cone θ` embeds isometrically in the plane **iff `θ = 2π`** —
  the conical singularity is absent exactly at the full angle.
* **Algebraic face** — `QIQTH.Fock.BoostKMS.stripKMSrvd_boostUnitary`
  (`QIQTH/Fock/BoostKMS.lean`): for every mass `m > 0` the rapidity-boost unitary
  group `t ↦ boostUnitary (2π·t)` satisfies the RvD half-strip KMS condition
  (`StripKMSrvd`) on the standard wedge subspace `closure (niceWedgeGenSet m)` —
  the modular flow of the wedge is **thermal at exactly 2π** (unit-strip KMS for
  the `2π`-rescaled boost = inverse temperature `2π` in rapidity).

Both faces are machine-checked theorems; `hawking_two_pi_coincidence` states them
side by side.  The IDENTIFICATION of the two `2π`'s — `θ = κβ`, the KMS temperature
of the boost = the Unruh temperature `κ/2π`, smoothness of the Euclidean section =
equilibrium of the Lorentzian wedge — is the **Gibbons–Hawking / Bisognano–Wichmann
DICTIONARY**, cited to the literature (Gibbons–Hawking 1977; Bisognano–Wichmann
1975/76; Sewell 1982), NOT derived here.

## (3) Periodic imaginary time = temperature — the thermal reread

Compactifying imaginary time on a circle of circumference `β` is the standard
Euclidean encoding of a thermal state at inverse temperature `β`
(`thermalCircle`).  The flat-torus GH limits of the stencil campaign
(`torusD_toGHSpace_tendsto_flatTorus`, re-exported as `thermalTorus_limit`)
therefore reread as *finite-temperature Euclidean geometries*: `FlatTorus 1` is
the thermal circle itself, `FlatTorus d` a thermal box with periodic space.

## (4) The Lorentzian seed

`sqrt_mul_add_le` — the reverse-triangle Cauchy–Schwarz inequality
`√(ab) + √(cd) ≤ √((a+c)(b+d))` — is the elementary engine of the REVERSE triangle
inequality of Lorentzian length spaces (timelike geodesics MAXIMIZE), stored here
as the seed for the future Lorentzian ladder.

## Scope firewall (MANDATORY, HONEST)

* The identities and re-exports below are theorems; **ALL physics identifications
  (`θ = κβ`, temperature, horizon, Unruh/Hawking) are INTERPRETATION**, cited to
  the literature, not formalized field-theory derivations.
* **Wick rotation is legitimate for static/thermal situations only and LOSES the
  causal structure** — the Euclidean section is not the Lorentzian spacetime; the
  Lorentzian ladder (causal sets, reverse-triangle geometry, of which
  `sqrt_mul_add_le` is the seed) is a separate CITED plan, not this file.
* The replica trick / entropy derivative at the conical angle `2π` (the
  Callan–Wilczek / Gibbons–Hawking entropy computation) is a **cited frontier**,
  not formalized.
* `θ` and `β` are INPUTS — chosen parameters, not derived.
* NOT GR, NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import QIQTH.ConeFlat
import QIQTH.TorusStencilGH
import QIQTH.Fock.BoostKMS

noncomputable section

namespace QIQTH.HawkingWick

/-! ## Part 1 — the Wick identities -/

/-- **The Lorentzian interval** in 1+1 dimensions, signature `(−, +)`:
`σ_L(t, x) = −t² + x²` (negative for timelike separation). -/
def sigmaL (t x : ℝ) : ℝ := -t ^ 2 + x ^ 2

/-- **The Euclidean quadratic form**: `σ_E(τ, x) = τ² + x²` — the flat metric of the
Euclidean section, the geometry the whole Riemannian GH program lives in. -/
def sigmaE (τ x : ℝ) : ℝ := τ ^ 2 + x ^ 2

/-- The complexified Lorentzian interval at a real time `t`: bookkeeping identity
tying `sigmaL` to the complex substitution of `wick_identity`. -/
theorem sigmaL_complex (t x : ℝ) : (sigmaL t x : ℂ) = -(t : ℂ) ^ 2 + (x : ℂ) ^ 2 := by
  unfold sigmaL
  push_cast
  ring

/-- **THE WICK IDENTITY**: substituting `t = iτ` into the (complexified) Lorentzian
interval `−t² + x²` yields exactly the Euclidean form `τ² + x²`.  Elementary — the
entire content is `I² = −1` — but this identity is WHY Euclidean geometry computes
static/thermal Lorentzian physics.  (Legitimacy of the rotation for a given theory,
and everything causal, is NOT contained in this identity: see the firewall.) -/
theorem wick_identity (τ x : ℝ) :
    (sigmaE τ x : ℂ) = -(Complex.I * (τ : ℂ)) ^ 2 + (x : ℂ) ^ 2 := by
  unfold sigmaE
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

/-- Null coordinate `u = (t − x)/√2` (retarded). -/
def nullU (t x : ℝ) : ℝ := (t - x) / Real.sqrt 2

/-- Null coordinate `v = (t + x)/√2` (advanced). -/
def nullV (t x : ℝ) : ℝ := (t + x) / Real.sqrt 2

/-- **The null-coordinate identity**: `2uv = t² − x²` — the Lorentzian interval
factorizes through the light-cone coordinates.  (In these coordinates the boost is
the dilation `(u, v) ↦ (e^{−s}u, e^{s}v)`, the flow whose KMS thermality is the
algebraic face below.) -/
theorem null_coords_identity (t x : ℝ) :
    2 * nullU t x * nullV t x = t ^ 2 - x ^ 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← pow_two]
    exact Real.sq_sqrt (by norm_num)
  unfold nullU nullV
  rw [show 2 * ((t - x) / Real.sqrt 2) * ((t + x) / Real.sqrt 2)
      = ((t - x) * (t + x)) * (2 / (Real.sqrt 2 * Real.sqrt 2)) from by ring, h]
  ring

/-- **THE LORENTZIAN SEED — reverse-triangle Cauchy–Schwarz**:
`√(ab) + √(cd) ≤ √((a+c)(b+d))` for nonnegative reals.  In null coordinates the
Lorentzian proper time of a timelike segment is `√(2uv)`, and this inequality IS the
reverse triangle inequality (timelike geodesics MAXIMIZE proper time) — stored here
as the elementary engine for the future Lorentzian ladder (cited plan, not this
campaign).  Proof: square both sides; the cross term obeys the AM–GM bound
`2√(ad·cb) ≤ ad + cb`. -/
theorem sqrt_mul_add_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  have hL : 0 ≤ Real.sqrt (a * b) + Real.sqrt (c * d) := by positivity
  have hab : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha hb)
  have hcd : Real.sqrt (c * d) ^ 2 = c * d := Real.sq_sqrt (mul_nonneg hc hd)
  -- the cross term: √(ab)·√(cd) = √(ad)·√(cb), then AM–GM
  have hswap : Real.sqrt (a * b) * Real.sqrt (c * d)
      = Real.sqrt (a * d) * Real.sqrt (c * b) := by
    rw [← Real.sqrt_mul (mul_nonneg ha hb), ← Real.sqrt_mul (mul_nonneg ha hd)]
    congr 1
    ring
  have hAMGM : 2 * (Real.sqrt (a * d) * Real.sqrt (c * b)) ≤ a * d + c * b := by
    nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (c * b)),
      Real.sq_sqrt (mul_nonneg ha hd), Real.sq_sqrt (mul_nonneg hc hb)]
  have key : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2 ≤ (a + c) * (b + d) := by
    have expand : (Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2
        = a * b + c * d + 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) := by
      rw [add_sq, hab, hcd]
      ring
    rw [expand, hswap]
    nlinarith [hAMGM]
  calc Real.sqrt (a * b) + Real.sqrt (c * d)
      = Real.sqrt ((Real.sqrt (a * b) + Real.sqrt (c * d)) ^ 2) :=
        (Real.sqrt_sq hL).symm
    _ ≤ Real.sqrt ((a + c) * (b + d)) := Real.sqrt_le_sqrt key

/-! ## Part 2 — THE TWO FACES OF 2π -/

section TwoFaces

open QIQTH.ConeMetric QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.BoostKMS

/-- **The geometric face of 2π** (named re-export of `QIQTH.ConeFlat.cone_flat_iff`,
brick E2): for `0 < θ ≤ 2π` the Euclidean near-horizon cone `Cone θ` embeds
isometrically in the plane **iff `θ = 2π`** — the Euclidean section is smooth exactly
at the full angle.  Via the Gibbons–Hawking dictionary (`θ = κβ`, INTERPRETATION):
smooth ⟺ `β = 2π/κ`, the Hawking–Unruh inverse temperature. -/
theorem hawking_geometric_face (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)] :
    (∃ f : Cone θ → ℂ, ∀ p q : Cone θ, dist (f p) (f q) = dist p q)
      ↔ θ = 2 * Real.pi :=
  QIQTH.ConeFlat.cone_flat_iff θ

/-- **The algebraic face of 2π** (named re-export of
`QIQTH.Fock.BoostKMS.stripKMSrvd_boostUnitary`): for every mass `m > 0` the
rapidity-boost group at the `2π`-rescaled parameter, `t ↦ boostUnitary (2π·t)`,
satisfies the RvD half-strip KMS condition on the standard wedge subspace
`closure (niceWedgeGenSet m)` — the free-field Bisognano–Wichmann thermality of the
wedge, at inverse temperature `2π` in rapidity.  Machine-checked, axiom-free. -/
theorem hawking_algebraic_face {m : ℝ} (hm : 0 < m) :
    StripKMSrvd (fun t => boostUnitary (2 * Real.pi * t))
      (closure (niceWedgeGenSet m)) :=
  stripKMSrvd_boostUnitary hm

/-- **THE TWO FACES OF 2π, side by side** (thin conjunction; campaign capstone).
For any admissible cone angle `θ` and any mass `m > 0`:

1. *(geometric)* the Euclidean cone `Cone θ` is flat **iff `θ = 2π`**, and
2. *(algebraic)* the boost group `t ↦ boostUnitary (2π·t)` is KMS-thermal on the
   standard wedge subspace of the mass-`m` free field.

Both conjuncts are machine-checked theorems.  The statement that the two `2π`'s are
THE SAME `2π` — that the smooth Euclidean period `β = 2π/κ` and the KMS temperature
of the Lorentzian wedge are two computations of one Hawking–Unruh temperature — is
the **Gibbons–Hawking / Bisognano–Wichmann dictionary**: INTERPRETATION, cited
(Gibbons–Hawking 1977; Bisognano–Wichmann 1975/76; Sewell 1982), not derived.  This
theorem is the honest formal content: the two faces, each proved, paired. -/
theorem hawking_two_pi_coincidence (θ : ℝ) [Fact (0 < θ)] [Fact (θ ≤ 2 * Real.pi)]
    {m : ℝ} (hm : 0 < m) :
    ((∃ f : Cone θ → ℂ, ∀ p q : Cone θ, dist (f p) (f q) = dist p q)
        ↔ θ = 2 * Real.pi)
    ∧ StripKMSrvd (fun t => boostUnitary (2 * Real.pi * t))
        (closure (niceWedgeGenSet m)) :=
  ⟨QIQTH.ConeFlat.cone_flat_iff θ, stripKMSrvd_boostUnitary hm⟩

end TwoFaces

/-! ## Part 3 — the thermal reread: periodic imaginary time = temperature -/

/-- **The thermal circle**: compactified imaginary time at inverse temperature `β` —
Euclidean time with the identification `τ ∼ τ + β`.  The standard Euclidean encoding
of a thermal (KMS) state at temperature `1/β` (INTERPRETATION, cited: Matsubara;
Gibbons–Hawking).  `β` is an INPUT. -/
def thermalCircle (β : ℝ) : Type := AddCircle β

section ThermalReread

open Filter QIQTH.TorusStencilGH QIQTH.TorusStencilGraph

/-- **The thermal reread of the torus limits** (named re-export of
`QIQTH.TorusStencilGH.torusD_toGHSpace_tendsto_flatTorus`): the purely combinatorial
scaled stencil tori converge in Gromov–Hausdorff space to the flat torus
`FlatTorus d = (ℝ/ℤ)ᵈ`.  Reread through Part 1's Wick identity: a flat torus with one
periodic direction of circumference `β` IS a finite-temperature Euclidean geometry —
periodic imaginary time at inverse temperature `β` (`d = 1`: the thermal circle
itself; general `d`: a thermal box with periodic space).  The GEOMETRY and the LIMIT
are theorems; the temperature reading is the cited dictionary. -/
theorem thermalTorus_limit (d : ℕ) :
    Tendsto (fun N : ℕ => GromovHausdorff.toGHSpace (ScaledTorusD d N)) atTop
      (nhds (GromovHausdorff.toGHSpace (FlatTorus d))) :=
  torusD_toGHSpace_tendsto_flatTorus d

end ThermalReread

end QIQTH.HawkingWick
