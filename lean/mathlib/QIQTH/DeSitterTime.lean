/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# DE SITTER TIME — the curved Lorentzian target: reversed Cauchy–Schwarz and the
# reverse triangle inequality on dS₂ (brick L4, Lorentzian-ladder finale)

## The space

2D de Sitter spacetime is the one-sheeted hyperboloid `dS₂ = {x ∈ ℝ^{1,2} : B(x,x) = 1}`
in 3-dimensional Minkowski space with bilinear form `B(x,y) = −x₀y₀ + x₁y₁ + x₂y₂`
(signature `(−,+,+)`).  It is the **Lorentzian sphere**: the constant-positive-curvature
Lorentzian space form, exactly as the round sphere (`SphereMetric.lean`) is the
constant-positive-curvature Riemannian one.

## The causal classification and the time separation

For `p, q` on the hyperboloid the connecting vector `v = p − q` has
`B(v,v) = 2 − 2·B(p,q)` (`sep_sq`), so

* `B(p,q) > 1`  ⟺  timelike-separated (`chron`, proved: `chron_iff_timelike_sep`),
* `B(p,q) = 1`  ⟺  null or coincident,
* `B(p,q) < 1`  ⟺  spacelike (and `B(p,q) ≤ −1` is the beyond-the-horizon regime).

The geodesic **proper time** between timelike-related points is `τ(p,q) = arcosh B(p,q)`
(`tauDS`, via Mathlib's `Real.arcosh`) — verified against the explicit timelike geodesic
`t ↦ (sinh t, cosh t, 0)`, on which `B(x(s), x(t)) = cosh(s−t)` (`B_geoPoint`) and `τ` is
exactly additive (`tauDS_geo_additive` — the equality case for collinear chains).  `tauDS`
is total (`arcosh` takes junk values below `1`); every theorem carries explicit
timelike hypotheses selecting the physical sector.

## The two theorems

* **THE REVERSED CAUCHY–SCHWARZ INEQUALITY** (`reversed_cauchy_schwarz`): for TIMELIKE
  vectors `w, w'` of `ℝ^{1,2}` (i.e. `B(w,w) < 0`), `B(w,w)·B(w',w') ≤ B(w,w')²` — the
  sign-flipped mirror of the Euclidean Cauchy–Schwarz inequality, and the engine of all
  Lorentzian reverse triangle inequalities.  Proof: the orthogonal complement of a
  timelike vector is spacelike (`ortho_spacelike`, a Lagrange-identity computation), then
  the Gram argument with the denominator-free orthogonal part `B(w,w)·w' − B(w,w')·w`.
  This mirrors the orthogonal-decomposition proof of Mathlib's SPHERICAL triangle
  inequality (`InnerProductGeometry.angle_le_angle_add_angle`) with every signature flipped.

* **THE REVERSE TRIANGLE INEQUALITY** (`tauDS_reverse_triangle`, cosh-level form
  `B_reverse_triangle`): for a timelike chain `p, q, r` (`B(p,q) > 1`, `B(q,r) > 1`) whose
  orthogonal parts at `q` point to OPPOSITE time-cones (`0 ≤ B(wpart p q, wpart r q)` —
  this branch hypothesis IS the time-ordering `p ≺ q ≺ r`, stated explicitly and honestly
  rather than swept under a causal-order formalization),
  `τ(p,q) + τ(q,r) ≤ τ(p,r)`: **timelike geodesics maximize proper time on dS₂**.
  This is the curved companion of the flat reverse triangle inequality
  `MinkowskiDiamond.tau_reverse_triangle` (brick L1).

## Non-flatness: what is (and is not) delivered

The L1 flat-uniqueness invariant (`MinkowskiDiamond.tau_midpoint_unique`: flat timelike
midpoints are UNIQUE) does **not** transfer to dS₂ by midpoint multiplication: timelike
geodesics in de Sitter space do not refocus (antipodal points satisfy `B(p,−p) = −1 < 1`
and are NOT timelike-related), so dS₂ has no timelike double-midpoints.  The honest
non-Minkowski witnesses delivered instead:

* **THE CAUSAL HORIZON** (`dS_causal_horizon` / `antipode_horizon`): NO event is
  chronologically related to both an event `p` and its antipode `−p` — de Sitter
  space has causal horizons.  In flat Minkowski space every PAIR of events has a common
  chronological future (`minkowski_common_future`, proved here in the L1 null-coordinate
  model).  This is a genuine global causal-structure separation between dS₂ and ℝ^{1,1}.

* **THE STRICT DEFECT** (`dS_strict_defect`): an explicit non-coplanar timelike chain
  (legs of proper time `1` and `1` in two DIFFERENT timelike planes through
  `q = (0,1,0)`, at rapidity `1`) with `τ(p,q) + τ(q,r) = 2 < τ(p,r)` — the de Sitter
  composition law `cosh τ(p,r) = cosh a·cosh b + sinh a·sinh b·cosh φ` evaluated on
  concrete points.  (Strictness alone also occurs for non-collinear flat chains; the
  full curvature invariant comparing the dS and flat composition laws at equal leg data
  is CITED further work, not claimed here.)

## Scope firewall (MANDATORY, HONEST)

* dS₂ is an **INPUT** — a chosen constant-curvature target space; the ambient form `B`
  and the hyperboloid presuppose the geometry; nothing here is emergence of de Sitter
  space from quantum data.
* Only the **τ-structure** (timelike sector) is formalized; spacelike geodesic distance
  on dS₂ is not treated.
* There is **NO discrete approximation** here: no Lorentzian analogue of
  Gromov–Hausdorff convergence exists in Mathlib (or any proof assistant) — the
  discrete-to-dS₂ rung is a CITED frontier, not this file.
* Everything is `1+1`-dimensional (ambient `1+2`).
* NOT GR (dS is a vacuum solution, but nothing here derives Einstein's equations),
  NOT numerical-G, NOT QG.  No axioms, no `sorry`.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import QIQTH.MinkowskiDiamond

noncomputable section

namespace QIQTH.DeSitterTime

/-! ## Part 1 — the ambient Minkowski form `B` on `ℝ^{1,2}` and its bilinearity -/

/-- **The Minkowski bilinear form** on `ℝ^{1,2}` (signature `(−,+,+)`; the first
coordinate is time): `B(x,y) = −x₀y₀ + x₁y₁ + x₂y₂`. -/
def B (x y : ℝ × ℝ × ℝ) : ℝ := -(x.1 * y.1) + x.2.1 * y.2.1 + x.2.2 * y.2.2

theorem B_symm (x y : ℝ × ℝ × ℝ) : B x y = B y x := by
  simp only [B]; ring

/-- Vector subtraction on explicit triples. -/
def vsub (x y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (x.1 - y.1, x.2.1 - y.2.1, x.2.2 - y.2.2)

/-- Scalar multiplication on explicit triples. -/
def vsmul (a : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (a * x.1, a * x.2.1, a * x.2.2)

theorem B_vsub_left (x y z : ℝ × ℝ × ℝ) : B (vsub x y) z = B x z - B y z := by
  simp only [B, vsub]; ring

theorem B_vsub_right (x y z : ℝ × ℝ × ℝ) : B x (vsub y z) = B x y - B x z := by
  simp only [B, vsub]; ring

theorem B_vsmul_left (a : ℝ) (x y : ℝ × ℝ × ℝ) : B (vsmul a x) y = a * B x y := by
  simp only [B, vsmul]; ring

theorem B_vsmul_right (a : ℝ) (x y : ℝ × ℝ × ℝ) : B x (vsmul a y) = a * B x y := by
  simp only [B, vsmul]; ring

/-! ## Part 2 — THE REVERSED CAUCHY–SCHWARZ INEQUALITY for timelike vectors

The crux engine.  In Euclidean space Cauchy–Schwarz says `⟪w,w'⟫² ≤ ⟪w,w⟫⟪w',w'⟫`; for
TIMELIKE vectors of a Lorentzian space the inequality REVERSES.  The proof mirrors the
orthogonal-decomposition proof of the spherical triangle inequality: decompose `w'`
along `w` plus an orthogonal part; the orthogonal complement of a timelike vector is
SPACELIKE (positive semi-definite) — that positivity, applied to the (denominator-free)
orthogonal part `B(w,w)·w' − B(w,w')·w`, is exactly the reversed inequality. -/

/-- **The orthogonal complement of a timelike vector is spacelike**: if `B(w,w) < 0` and
`B(w,z) = 0` then `B(z,z) ≥ 0`.  Proof: from orthogonality `w₀z₀ = w₁z₁ + w₂z₂`; the
Lagrange-style identity
`w₀²·B(z,z) = (w₀² − w₁² − w₂²)(z₁² + z₂²) + (w₁z₂ − w₂z₁)²`
exhibits `w₀²·B(z,z)` as a sum of two nonnegative terms (timelike `w` gives
`w₀² > w₁² + w₂²`). -/
theorem ortho_spacelike {w z : ℝ × ℝ × ℝ} (hw : B w w < 0) (ho : B w z = 0) :
    0 ≤ B z z := by
  simp only [B] at hw ho ⊢
  have hts : w.1 * z.1 = w.2.1 * z.2.1 + w.2.2 * z.2.2 := by linarith
  have key : w.1 ^ 2 * (-(z.1 * z.1) + z.2.1 * z.2.1 + z.2.2 * z.2.2)
      = (w.1 ^ 2 - w.2.1 ^ 2 - w.2.2 ^ 2) * (z.2.1 ^ 2 + z.2.2 ^ 2)
        + (w.2.1 * z.2.2 - w.2.2 * z.2.1) ^ 2 := by
    linear_combination (-(w.1 * z.1) - (w.2.1 * z.2.1 + w.2.2 * z.2.2)) * hts
  have ht2 : 0 < w.1 ^ 2 := by nlinarith [sq_nonneg w.2.1, sq_nonneg w.2.2]
  have hcone : 0 ≤ w.1 ^ 2 - w.2.1 ^ 2 - w.2.2 ^ 2 := by nlinarith
  have hpos : 0 ≤ w.1 ^ 2 * (-(z.1 * z.1) + z.2.1 * z.2.1 + z.2.2 * z.2.2) := by
    rw [key]
    have h1 : 0 ≤ (w.1 ^ 2 - w.2.1 ^ 2 - w.2.2 ^ 2) * (z.2.1 ^ 2 + z.2.2 ^ 2) :=
      mul_nonneg hcone (by positivity)
    nlinarith [sq_nonneg (w.2.1 * z.2.2 - w.2.2 * z.2.1)]
  nlinarith [hpos, ht2]

/-- **THE REVERSED CAUCHY–SCHWARZ INEQUALITY**: for timelike `w` and ARBITRARY `w'` in
`ℝ^{1,2}`, `B(w,w)·B(w',w') ≤ B(w,w')²` (the classical both-timelike statement is the
special case).  The engine of the reverse triangle inequality — the Lorentzian mirror
(with both signs flipped) of the Cauchy–Schwarz step in Mathlib's spherical triangle
inequality.  Proof: apply `ortho_spacelike` to the denominator-free orthogonal part
`z = B(w,w)·w' − B(w,w')·w` and expand
`B(z,z) = B(w,w)·(B(w,w)B(w',w') − B(w,w')²)`; divide by `B(w,w) < 0`. -/
theorem reversed_cauchy_schwarz {w : ℝ × ℝ × ℝ} (hw : B w w < 0) (w' : ℝ × ℝ × ℝ) :
    B w w * B w' w' ≤ B w w' ^ 2 := by
  have horth : B w (vsub (vsmul (B w w) w') (vsmul (B w w') w)) = 0 := by
    rw [B_vsub_right, B_vsmul_right, B_vsmul_right]; ring
  have hz := ortho_spacelike hw horth
  have hzz : B (vsub (vsmul (B w w) w') (vsmul (B w w') w))
      (vsub (vsmul (B w w) w') (vsmul (B w w') w))
      = B w w * (B w w * B w' w' - B w w' ^ 2) := by
    simp only [B_vsub_left, B_vsub_right, B_vsmul_left, B_vsmul_right]
    rw [B_symm w' w]
    ring
  rw [hzz] at hz
  nlinarith [hz, hw]

/-! ## Part 3 — the de Sitter hyperboloid, causal classification, proper time -/

/-- **2D de Sitter spacetime**: the one-sheeted hyperboloid `B(x,x) = 1` in `ℝ^{1,2}` —
the constant-positive-curvature Lorentzian space form (the Lorentzian sphere). -/
abbrev dS := {x : ℝ × ℝ × ℝ // B x x = 1}

theorem B_self (p : dS) : B p.1 p.1 = 1 := p.2

/-- **Chronological (timelike) relation** on dS₂: `B(p,q) > 1`.  Justified by
`chron_iff_timelike_sep`: the ambient connecting vector is timelike iff `B(p,q) > 1`. -/
def chron (p q : dS) : Prop := 1 < B p.1 q.1

theorem chron_comm {p q : dS} : chron p q ↔ chron q p := by
  unfold chron; rw [B_symm]

/-- The ambient separation vector of two hyperboloid points: `B(p−q, p−q) = 2 − 2·B(p,q)`. -/
theorem sep_sq (p q : dS) : B (vsub p.1 q.1) (vsub p.1 q.1) = 2 - 2 * B p.1 q.1 := by
  simp only [B_vsub_left, B_vsub_right]
  rw [p.2, q.2, B_symm q.1 p.1]
  ring

/-- **The causal classification of dS₂**: two hyperboloid points are timelike-separated
(the connecting vector is ambient-timelike) iff `B(p,q) > 1`. -/
theorem chron_iff_timelike_sep (p q : dS) :
    chron p q ↔ B (vsub p.1 q.1) (vsub p.1 q.1) < 0 := by
  unfold chron
  rw [sep_sq]
  constructor <;> intro h <;> linarith

/-- **The de Sitter proper time** `τ(p,q) = arcosh B(p,q)` — the timelike geodesic
proper time for chronologically related pairs (`B > 1`); total by `Real.arcosh` junk
values (`arcosh x` for `x < 1` is junk); every theorem carries explicit timelike
hypotheses selecting the physical sector. -/
def tauDS (p q : dS) : ℝ := Real.arcosh (B p.1 q.1)

theorem tauDS_self (p : dS) : tauDS p p = 0 := by
  unfold tauDS
  rw [p.2]
  exact Real.arcosh_zero

theorem tauDS_comm (p q : dS) : tauDS p q = tauDS q p := by
  unfold tauDS; rw [B_symm]

theorem tauDS_nonneg {p q : dS} (h : 1 ≤ B p.1 q.1) : 0 ≤ tauDS p q :=
  Real.arcosh_nonneg h

theorem tauDS_pos {p q : dS} (h : chron p q) : 0 < tauDS p q :=
  Real.arcosh_pos h

/-- `cosh τ(p,q) = B(p,q)` on the causal sector — the de Sitter analogue of
`cos(angle) = ⟪p,q⟫` on the sphere. -/
theorem cosh_tauDS {p q : dS} (h : 1 ≤ B p.1 q.1) : Real.cosh (tauDS p q) = B p.1 q.1 :=
  Real.cosh_arcosh h

/-! ## Part 4 — the orthogonal decomposition at a chain vertex -/

/-- **The orthogonal part** of `p` seen from `q`: `w = p − B(p,q)·q`, the component of
`p` orthogonal to `q` (the tangent direction at `q` of the geodesic toward `p`, scaled). -/
def wpart (p q : dS) : ℝ × ℝ × ℝ := vsub p.1 (vsmul (B p.1 q.1) q.1)

/-- The orthogonal part is `B`-orthogonal to the vertex. -/
theorem B_wpart_orth (p q : dS) : B q.1 (wpart p q) = 0 := by
  unfold wpart
  rw [B_vsub_right, B_vsmul_right, q.2, B_symm q.1 p.1]
  ring

/-- `B(w,w) = 1 − B(p,q)²` for the orthogonal part `w = wpart p q`: for a chronological
pair (`B(p,q) > 1`) the orthogonal part is TIMELIKE — the reversed-Cauchy–Schwarz
hypothesis. -/
theorem wpart_B_self (p q : dS) : B (wpart p q) (wpart p q) = 1 - B p.1 q.1 ^ 2 := by
  unfold wpart
  simp only [B_vsub_left, B_vsub_right, B_vsmul_left, B_vsmul_right]
  rw [p.2, q.2, B_symm q.1 p.1]
  ring

/-- The cross term of two orthogonal parts at a common vertex:
`B(wpart p q, wpart r q) = B(p,r) − B(p,q)·B(r,q)`. -/
theorem B_wpart_wpart (p r q : dS) :
    B (wpart p q) (wpart r q) = B p.1 r.1 - B p.1 q.1 * B r.1 q.1 := by
  unfold wpart
  simp only [B_vsub_left, B_vsub_right, B_vsmul_left, B_vsmul_right]
  rw [q.2, B_symm q.1 r.1]
  ring

/-! ## Part 5 — THE REVERSE TRIANGLE INEQUALITY on dS₂

The chain hypothesis `0 ≤ B (wpart p q) (wpart r q)` is the OPPOSITE-TIME-CONE branch:
in signature `(−,+,+)` two co-oriented timelike vectors have `B < 0`, so nonnegativity
says the geodesic tangents at `q` toward `p` and toward `r` point to opposite time-cones
— i.e. `q` lies BETWEEN `p` and `r` (the time-ordering `p ≺ q ≺ r`).  It is stated
explicitly and honestly rather than derived from a causal-order formalization. -/

/-- **The reverse triangle inequality, cosh level**: for a timelike chain `p, q, r` with
the opposite-cone branch hypothesis,
`B(p,q)·B(q,r) + √(B(p,q)² − 1)·√(B(q,r)² − 1) ≤ B(p,r)` —
i.e. `cosh(τ(p,q) + τ(q,r)) ≤ cosh τ(p,r)`, arcosh-free. -/
theorem B_reverse_triangle (p q r : dS)
    (hpq : 1 < B p.1 q.1) (_hqr : 1 < B q.1 r.1)
    (hchain : 0 ≤ B (wpart p q) (wpart r q)) :
    B p.1 q.1 * B q.1 r.1
      + Real.sqrt (B p.1 q.1 ^ 2 - 1) * Real.sqrt (B q.1 r.1 ^ 2 - 1) ≤ B p.1 r.1 := by
  have hww := wpart_B_self p q
  have hww' := wpart_B_self r q
  have hsym : B r.1 q.1 = B q.1 r.1 := B_symm r.1 q.1
  rw [hsym] at hww'
  have h1 : B (wpart p q) (wpart p q) < 0 := by rw [hww]; nlinarith
  have hCS := reversed_cauchy_schwarz h1 (wpart r q)
  rw [hww, hww'] at hCS
  have hprod : (B p.1 q.1 ^ 2 - 1) * (B q.1 r.1 ^ 2 - 1)
      ≤ B (wpart p q) (wpart r q) ^ 2 := by nlinarith [hCS]
  have hs : Real.sqrt ((B p.1 q.1 ^ 2 - 1) * (B q.1 r.1 ^ 2 - 1))
      ≤ B (wpart p q) (wpart r q) := by
    calc Real.sqrt ((B p.1 q.1 ^ 2 - 1) * (B q.1 r.1 ^ 2 - 1))
        ≤ Real.sqrt (B (wpart p q) (wpart r q) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = B (wpart p q) (wpart r q) := Real.sqrt_sq hchain
  have hsplit : Real.sqrt ((B p.1 q.1 ^ 2 - 1) * (B q.1 r.1 ^ 2 - 1))
      = Real.sqrt (B p.1 q.1 ^ 2 - 1) * Real.sqrt (B q.1 r.1 ^ 2 - 1) :=
    Real.sqrt_mul (by nlinarith) _
  have hBpr := B_wpart_wpart p r q
  rw [hsym] at hBpr
  rw [← hsplit]
  linarith [hs, hBpr.symm.le, hBpr.le]

/-- **THE REVERSE TRIANGLE INEQUALITY ON dS₂** — timelike geodesics MAXIMIZE proper
time in de Sitter space: for a timelike chain `p, q, r` (both legs chronological, with
the opposite-cone branch hypothesis = the time-ordering `p ≺ q ≺ r`),
`τ(p,q) + τ(q,r) ≤ τ(p,r)`.
The curved companion of the flat `MinkowskiDiamond.tau_reverse_triangle` (brick L1),
proved from `reversed_cauchy_schwarz` exactly as Mathlib's spherical triangle inequality
follows from Cauchy–Schwarz — with every signature flipped. -/
theorem tauDS_reverse_triangle (p q r : dS)
    (hpq : 1 < B p.1 q.1) (hqr : 1 < B q.1 r.1)
    (hchain : 0 ≤ B (wpart p q) (wpart r q)) :
    tauDS p q + tauDS q r ≤ tauDS p r := by
  have hcosh : Real.cosh (tauDS p q + tauDS q r) ≤ B p.1 r.1 := by
    rw [Real.cosh_add]
    unfold tauDS
    rw [Real.cosh_arcosh hpq.le, Real.cosh_arcosh hqr.le,
      Real.sinh_arcosh hpq.le, Real.sinh_arcosh hqr.le]
    exact B_reverse_triangle p q r hpq hqr hchain
  have h0 : 0 ≤ tauDS p q + tauDS q r :=
    add_nonneg (Real.arcosh_nonneg hpq.le) (Real.arcosh_nonneg hqr.le)
  calc tauDS p q + tauDS q r
      = Real.arcosh (Real.cosh (tauDS p q + tauDS q r)) := (Real.arcosh_cosh h0).symm
    _ ≤ Real.arcosh (B p.1 r.1) :=
        (Real.arcosh_le_arcosh (Real.cosh_pos _)
          (lt_of_lt_of_le (Real.cosh_pos _) hcosh)).mpr hcosh
    _ = tauDS p r := rfl

/-- The endpoints of a timelike chain are chronologically related (`B(p,r) > 1`):
chronology is transitive along correctly ordered chains. -/
theorem chron_of_chain (p q r : dS)
    (hpq : 1 < B p.1 q.1) (hqr : 1 < B q.1 r.1)
    (hchain : 0 ≤ B (wpart p q) (wpart r q)) :
    chron p r := by
  have h := B_reverse_triangle p q r hpq hqr hchain
  have hsq : 0 ≤ Real.sqrt (B p.1 q.1 ^ 2 - 1) * Real.sqrt (B q.1 r.1 ^ 2 - 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  unfold chron
  nlinarith [h, hsq]

/-! ## Part 6 — the explicit timelike geodesic: additivity (the equality case) -/

/-- **The explicit timelike geodesic** through `(0,1,0)`:
`x(t) = (sinh t, cosh t, 0)` — the intersection of dS₂ with the timelike plane
spanned by `(1,0,0)` and `(0,1,0)`. -/
def geoPoint (t : ℝ) : dS :=
  ⟨(Real.sinh t, Real.cosh t, 0), by
    simp only [B]
    linear_combination Real.cosh_sq_sub_sinh_sq t⟩

/-- Along the geodesic, `B(x(s), x(t)) = cosh(s − t)`: distinct parameter values are
always chronologically related, and proper time is the parameter gap. -/
theorem B_geoPoint (s t : ℝ) : B (geoPoint s).1 (geoPoint t).1 = Real.cosh (s - t) := by
  simp only [geoPoint, B]
  rw [Real.cosh_sub]
  ring

theorem chron_geoPoint {s t : ℝ} (h : s ≠ t) : chron (geoPoint s) (geoPoint t) := by
  unfold chron
  rw [B_geoPoint]
  exact Real.one_lt_cosh.mpr (sub_ne_zero.mpr h)

/-- Proper time along the geodesic is the parameter gap: `τ(x(s), x(t)) = t − s`. -/
theorem tauDS_geoPoint {s t : ℝ} (h : s ≤ t) : tauDS (geoPoint s) (geoPoint t) = t - s := by
  unfold tauDS
  rw [B_geoPoint, show s - t = -(t - s) by ring, Real.cosh_neg,
    Real.arcosh_cosh (by linarith)]

/-- **Geodesic additivity — the equality case of the reverse triangle inequality**:
along the timelike geodesic, `τ` is exactly additive for ordered parameter triples. -/
theorem tauDS_geo_additive {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≤ t₂) (h23 : t₂ ≤ t₃) :
    tauDS (geoPoint t₁) (geoPoint t₂) + tauDS (geoPoint t₂) (geoPoint t₃)
      = tauDS (geoPoint t₁) (geoPoint t₃) := by
  rw [tauDS_geoPoint h12, tauDS_geoPoint h23, tauDS_geoPoint (h12.trans h23)]
  ring

/-! ## Part 7 — THE STRICT DEFECT: a non-coplanar chain where the inequality is strict

Legs of proper time `1` and `1` through `q = geoPoint 0 = (0,1,0)`, in two DIFFERENT
timelike planes (the second at rapidity `φ = 1`): the total is
`cosh τ(p,r) = sinh²1·cosh 1 + cosh²1 > cosh 2`, so `τ(p,r) > 2 = τ(p,q) + τ(q,r)`. -/

/-- The third chain point: `r = (sinh 1·cosh 1, cosh 1, sinh 1·sinh 1)` — the point at
proper time `1` from `(0,1,0)` along the geodesic with rapidity-`1` tilted tangent. -/
def defectR : dS :=
  ⟨(Real.sinh 1 * Real.cosh 1, Real.cosh 1, Real.sinh 1 * Real.sinh 1), by
    simp only [B]
    linear_combination (1 - Real.sinh 1 * Real.sinh 1) * Real.cosh_sq_sub_sinh_sq 1⟩

/-- **THE STRICT DEFECT** — the de Sitter composition law beats flat additivity on an
explicit non-coplanar timelike chain: `p = geoPoint (−1)`, `q = geoPoint 0`,
`r = defectR` form a chain satisfying all hypotheses of `tauDS_reverse_triangle`
(both legs chronological, opposite-cone branch), and the inequality is STRICT:
`τ(p,q) + τ(q,r) = 2 < τ(p,r)`.  Contrast `tauDS_geo_additive` (equality on collinear
chains).  (The flat-vs-curved invariant comparison at equal leg data — the true
curvature statement — is cited further work; see the header.) -/
theorem dS_strict_defect :
    1 < B (geoPoint (-1)).1 (geoPoint 0).1 ∧
    1 < B (geoPoint 0).1 defectR.1 ∧
    0 ≤ B (wpart (geoPoint (-1)) (geoPoint 0)) (wpart defectR (geoPoint 0)) ∧
    tauDS (geoPoint (-1)) (geoPoint 0) + tauDS (geoPoint 0) defectR
      < tauDS (geoPoint (-1)) defectR := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
  have hc1 : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr one_ne_zero
  have hc0 : 0 < Real.cosh 1 := Real.cosh_pos 1
  have hBpq : B (geoPoint (-1)).1 (geoPoint 0).1 = Real.cosh 1 := by
    rw [B_geoPoint, show (-1 : ℝ) - 0 = -1 by norm_num, Real.cosh_neg]
  have hBqr : B (geoPoint 0).1 defectR.1 = Real.cosh 1 := by
    simp only [geoPoint, defectR, B, Real.sinh_zero, Real.cosh_zero]
    ring
  have hBpr : B (geoPoint (-1)).1 defectR.1
      = Real.sinh 1 * Real.sinh 1 * Real.cosh 1 + Real.cosh 1 * Real.cosh 1 := by
    simp only [geoPoint, defectR, B, Real.sinh_neg, Real.cosh_neg]
    ring
  have hBrq : B defectR.1 (geoPoint 0).1 = Real.cosh 1 := by
    rw [B_symm]; exact hBqr
  have hchain : 0 ≤ B (wpart (geoPoint (-1)) (geoPoint 0)) (wpart defectR (geoPoint 0)) := by
    rw [B_wpart_wpart, hBpr, hBpq, hBrq]
    nlinarith [mul_pos (mul_pos hs hs) hc0]
  have ht1 : tauDS (geoPoint (-1)) (geoPoint 0) = 1 := by
    unfold tauDS
    rw [hBpq]
    exact Real.arcosh_cosh zero_le_one
  have ht2 : tauDS (geoPoint 0) defectR = 1 := by
    unfold tauDS
    rw [hBqr]
    exact Real.arcosh_cosh zero_le_one
  have hcosh2 : Real.cosh 2 = Real.cosh 1 * Real.cosh 1 + Real.sinh 1 * Real.sinh 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.cosh_add]
  have hlt : Real.cosh 2 < B (geoPoint (-1)).1 defectR.1 := by
    rw [hBpr, hcosh2]
    nlinarith [mul_pos hs hs]
  have htau : (2 : ℝ) < tauDS (geoPoint (-1)) defectR := by
    have h2 : (2 : ℝ) = Real.arcosh (Real.cosh 2) := (Real.arcosh_cosh (by norm_num)).symm
    rw [h2]
    unfold tauDS
    exact (Real.arcosh_lt_arcosh (Real.cosh_pos 2)
      (lt_trans (Real.cosh_pos 2) hlt)).mpr hlt
  exact ⟨by rw [hBpq]; exact hc1, by rw [hBqr]; exact hc1, hchain, by
    rw [ht1, ht2]; linarith⟩

/-! ## Part 8 — THE CAUSAL HORIZON: the honest global non-Minkowski witness

Antipodal de Sitter events share NO chronological future or past — de Sitter space has
causal horizons.  In flat Minkowski space every pair of events has a common
chronological future.  A genuine global causal-structure separation between the curved
target and the flat one, machine-checked on both sides. -/

/-- The antipode `−p` of a hyperboloid point (`B(−x,−x) = B(x,x) = 1`). -/
def antipode (p : dS) : dS :=
  ⟨(-p.1.1, -p.1.2.1, -p.1.2.2), by
    have h := p.2
    simp only [B] at h ⊢
    linear_combination h⟩

theorem B_antipode_left (p q : dS) : B (antipode p).1 q.1 = -B p.1 q.1 := by
  simp only [antipode, B]; ring

theorem B_antipode_right (p q : dS) : B p.1 (antipode q).1 = -B p.1 q.1 := by
  simp only [antipode, B]; ring

/-- **THE DE SITTER CAUSAL HORIZON**: no event is chronologically related to both `p`
and its antipode `−p` (if `B(p,q) > 1` then `B(−p,q) = −B(p,q) < −1 < 1`). -/
theorem antipode_horizon (p q : dS) : ¬(chron p q ∧ chron (antipode p) q) := by
  rintro ⟨h1, h2⟩
  unfold chron at h1 h2
  rw [B_antipode_left] at h2
  linarith

/-- **The flat contrast**: in 1+1 Minkowski space (the L1 null-coordinate model of
`MinkowskiDiamond`), EVERY pair of events has a common chronological future — the
feature whose failure on dS₂ (`antipode_horizon`) is the causal-horizon witness. -/
theorem minkowski_common_future (p p' : ℝ × ℝ) :
    ∃ q : ℝ × ℝ, MinkowskiDiamond.causalLE p q ∧ MinkowskiDiamond.causalLE p' q ∧
      0 < MinkowskiDiamond.tau p q ∧ 0 < MinkowskiDiamond.tau p' q := by
  have h1 : p.1 < max p.1 p'.1 + 1 := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have h2 : p.2 < max p.2 p'.2 + 1 := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have h1' : p'.1 < max p.1 p'.1 + 1 := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have h2' : p'.2 < max p.2 p'.2 + 1 := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hc : MinkowskiDiamond.causalLE p (max p.1 p'.1 + 1, max p.2 p'.2 + 1) :=
    ⟨h1.le, h2.le⟩
  have hc' : MinkowskiDiamond.causalLE p' (max p.1 p'.1 + 1, max p.2 p'.2 + 1) :=
    ⟨h1'.le, h2'.le⟩
  exact ⟨(max p.1 p'.1 + 1, max p.2 p'.2 + 1), hc, hc',
    (MinkowskiDiamond.tau_pos_iff hc).mpr ⟨h1, h2⟩,
    (MinkowskiDiamond.tau_pos_iff hc').mpr ⟨h1', h2'⟩⟩

/-- **THE CAUSAL-HORIZON PACKAGE**: dS₂ contains a pair of distinct events, each with a
nonempty chronological cone, sharing NO chronologically related event — de Sitter
horizons, as a single existence statement (contrast `minkowski_common_future`). -/
theorem dS_causal_horizon :
    ∃ p p' : dS, p ≠ p' ∧ (∃ q, chron p q) ∧ (∃ q, chron p' q) ∧
      ∀ q : dS, ¬(chron p q ∧ chron p' q) := by
  refine ⟨geoPoint 0, antipode (geoPoint 0), ?_,
    ⟨geoPoint 1, chron_geoPoint (by norm_num)⟩,
    ⟨antipode (geoPoint 1), ?_⟩,
    fun q => antipode_horizon (geoPoint 0) q⟩
  · intro h
    have h2 := congrArg (fun p : dS => p.1.2.1) h
    simp only [geoPoint, antipode] at h2
    rw [Real.cosh_zero] at h2
    norm_num at h2
  · unfold chron
    rw [B_antipode_left, B_antipode_right, neg_neg, B_geoPoint]
    exact Real.one_lt_cosh.mpr (by norm_num)

end QIQTH.DeSitterTime
