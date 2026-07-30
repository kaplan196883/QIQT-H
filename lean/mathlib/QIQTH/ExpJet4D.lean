/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4ValFull
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# JET-4 TOWER — the `expJetD4` packaging foundation (J4-4, reachable rungs)

This file lands the reachable, axiom-free foundation of brick **J4-4** of the JET-4 TOWER campaign
(`docs/qg_roadmap/JET4_TOWER_PLAN.md`): the packaging prerequisites that lift the VALUE two-point
Lipschitz estimate `expJet4Val_v_two_pt_diff` (J4-3, `ExpJet4ValFull.lean`) toward the
DERIVATIVE-OPERATOR two-point difference `expJetD4_two_pt_diff` — the faithful mirror one Fréchet order
up of `expJetD3_two_pt_diff` (`ExpMapContDiff3.lean:4585`).

The `expJetD3` packaging (`ExpMapContDiff3.lean`) is assembled from two ingredients that have NO jet-4
analog in the repo yet:
* the genuine **second-variation curve** `expJet2Curve` and its curve-level bilinearity, which feed the
  `Q··` slots of `expJet3ValG`;
* the value form `expJet3Val` with its `Q`-congruence (`expJet3Val_congr`) and matched-`Q`
  multilinearity, which package into the trilinear CLM `expJetD3`.

Here we build the exact one-order-up analogs that are reachable from the already-landed jet-4
fundamental-solution tower (`expJet3Fund`, `expJet3Fund_unique`, `expJet3Rhs_add/smul_*`,
`expJet4Fund`, `expJet4Fund_unique`, `expJet4Rhs_apply`):

* `expJet3Curve` — the genuine **third-variation curve** `t ↦ R^{hkl}_v(t)` (the `expJet3Fund` witness
  kept as a whole curve, not just its `t = 1` value), with `expJet3Curve_continuousOn` and the
  curve-level (`∀ t ∈ [0,1]`) trilinearity `expJet3Curve_{add,smul}_{l,h,k}` (six lemmas) via the SAME
  superposition-via-uniqueness argument as `expJet2Curve_{add,smul}_{left,right}`, one order up.  These
  curves are exactly what the (downstream) genuine triple-variation curve `expJet3CurveG` — the feeder
  of the four triple-`Q···` slots of `expJet4ValG` — is built from.

* `expJet4Val` — the **fourth-variation value** `R^{hklm}_v(1)` (the `expJet4Fund` witness at `t = 1`),
  and its `Q`-congruence `expJet4Val_congr` (the value depends on the ten `Q··`/`Q···` inputs only
  through their values on `[0,1]`, by `expJet4Fund_unique`).  This is the value-only interface into
  which the genuine bilinear/trilinear curves are fed to obtain the matched-`Q` multilinearity of
  `expJet4Val` and hence the genuine quadrilinear CLM datum `expJetD4`.

## Honest firewall (binding)

This does NOT define `expJetD4`, does NOT prove `expJetD4_two_pt_diff`, does NOT discharge
`hfd3` / `ContDiff¹ (fderiv³ exp_p)`, does NOT establish `exp_p ∈ C⁴`, and does NOT reach `κ = 1/6`,
the heat-kernel parametrix, or `a₁ = R/6`.  It is a set of green, axiom-free packaging prerequisites of
brick J4-4.  The remaining chain to `expJetD4_two_pt_diff` is documented at the end of the file.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4

variable {n : ℕ}

/-! ### The genuine third-variation CURVE `expJet3Curve` and its curve-level trilinearity

Mirror of `expJet2Curve` (`ExpMapContDiff3.lean:2315`) one Fréchet order up.  The value at `t = 1` is
`expJet3Val`; here we keep the whole curve, since the Jet₄ source `expJet4Rhs` feeds the triple
variations pointwise.  The curve-level trilinearity is the exact `∀ t`-upgrade of the matched-`Q`
value facts `expJet3Val_{add,smul}_{l,h,k}`, proved by the same `expJet3Fund_unique` superposition. -/

/-- The **genuine third-variation curve** `t ↦ R^{hkl}_v(t)`: the chosen `expJet3Fund` witness for the
    direction triple `(h,k,l)` with `Q··` inputs `Qkl,Qhl,Qhk`. -/
noncomputable def expJet3Curve (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) : ℝ → (Point n × Point n) :=
  (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose

/-- `expJet3Curve` is continuous on `[0,1]` (the `expJet3Fund` witness spec). -/
theorem expJet3Curve_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    ContinuousOn (expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l)
      (Set.Icc (0 : ℝ) 1) :=
  (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec.2.1

/-- The `t = 1` value of `expJet3Curve` is `expJet3Val`. -/
theorem expJet3Curve_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l 1
      = expJet3Val g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l := rfl

/-- **Curve-level additivity of `R^{hkl}` in the `l`-slot, on `[0,1]`.**  The `∀ t`-upgrade of
    `expJet3Val_add_l`: same superposition (`expJet3Rhs_add_l` + `expJet3Fund_unique`), keeping the
    whole-interval uniqueness conclusion. -/
theorem expJet3Curve_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl₁ Qhl₂ Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (h k l₁ l₂ : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
        (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂) t
      = expJet3Curve g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁ t
        + expJet3Curve g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂ t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
      (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂)).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s)
    Qhk hv h k (l₁ + l₂)
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk hv hΦcont
      (hQkl₁.add hQkl₂) (hQhl₁.add hQhl₂) hQhk h k (l₁ + l₂)).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t
      + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₁ Qhl₁ Qhk h k l₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl₂ Qhk h k l₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl₁ Qhk hv hΦcont hQkl₁ hQhl₁ hQhk h k l₁).choose t
                + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl₂ Qhk hv hΦcont hQkl₂ hQhl₂ hQhk h k l₂).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qhl₁ s + Qhl₂ s) Qhk
                h k (l₁ + l₂) t := by
        rw [map_add, expJet3Rhs_add_l]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- **Curve-level `ℝ`-homogeneity of `R^{hkl}` in the `l`-slot, on `[0,1]`.** -/
theorem expJet3Curve_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
        (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l) t
      = c • expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
      (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l)).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv
    h k (c • l)
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk hv hΦcont
      (hQkl.const_smul c) (hQhl.const_smul c) hQhk h k (c • l)).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) (fun s => c • Qhl s) Qhk h k (c • l) t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_l]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- **Curve-level additivity of `R^{hkl}` in the `h`-slot, on `[0,1]`.** -/
theorem expJet3Curve_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl₁ Qhl₂ Qhk₁ Qhk₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
        hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l t
      = expJet3Curve g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l t
        + expJet3Curve g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s)
    (fun s => Qhk₁ s + Qhk₂ s) hv (h₁ + h₂) k l
    (expJet3Fund g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      hQkl (hQhl₁.add hQhl₂) (hQhk₁.add hQhk₂) (h₁ + h₂) k l).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t
      + (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl₁ Qhk₁ h₁ k l t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl₂ Qhk₂ h₂ k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl Qhl₁ Qhk₁ hv hΦcont hQkl hQhl₁ hQhk₁ h₁ k l).choose t
                + (expJet3Fund g gi hC p v Φ Qkl Qhl₂ Qhk₂ hv hΦcont hQkl hQhl₂ hQhk₂ h₂ k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhk₁ s + Qhk₂ s)
                (h₁ + h₂) k l t := by
        rw [map_add, expJet3Rhs_add_h]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- **Curve-level `ℝ`-homogeneity of `R^{hkl}` in the `h`-slot, on `[0,1]`.** -/
theorem expJet3Curve_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
        hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l t
      = c • expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
      hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv
    (c • h) k l
    (expJet3Fund g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) hv hΦcont
      hQkl (hQhl.const_smul c) (hQhk.const_smul c) (c • h) k l).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl (fun s => c • Qhl s) (fun s => c • Qhk s) (c • h) k l t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_h]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- **Curve-level additivity of `R^{hkl}` in the `k`-slot, on `[0,1]`.** -/
theorem expJet3Curve_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl₁ Qkl₂ Qhl Qhk₁ Qhk₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
        (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l t
      = expJet3Curve g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l t
        + expJet3Curve g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl
    (fun s => Qhk₁ s + Qhk₂ s) hv h (k₁ + k₂) l
    (expJet3Fund g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s) hv hΦcont
      (hQkl₁.add hQkl₂) hQhl (hQhk₁.add hQhk₂) h (k₁ + k₂) l).choose
    (fun t => (expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t
      + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₁ Qhl Qhk₁ h k₁ l t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl₂ Qhl Qhk₂ h k₂ l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl₁ Qhl Qhk₁ hv hΦcont hQkl₁ hQhl hQhk₁ h k₁ l).choose t
                + (expJet3Fund g gi hC p v Φ Qkl₂ Qhl Qhk₂ hv hΦcont hQkl₂ hQhl hQhk₂ h k₂ l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => Qkl₁ s + Qkl₂ s) Qhl (fun s => Qhk₁ s + Qhk₂ s)
                h (k₁ + k₂) l t := by
        rw [map_add, expJet3Rhs_add_k]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- **Curve-level `ℝ`-homogeneity of `R^{hkl}` in the `k`-slot, on `[0,1]`.** -/
theorem expJet3Curve_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (c : ℝ) (h k l : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
        (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l t
      = c • expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
      (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv
    h (c • k) l
    (expJet3Fund g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) hv hΦcont
      (hQkl.const_smul c) hQhl (hQhk.const_smul c) h (c • k) l).choose
    (fun t => c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
              + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose t)
            + expJet3Rhs g gi hC p v Φ (fun s => c • Qkl s) Qhl (fun s => c • Qhk s) h (c • k) l t := by
        rw [smul_add, map_smul, expJet3Rhs_smul_k]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-! ### The fourth-variation value `expJet4Val` and its `Q`-congruence

Mirror of `expJet3Val` + `expJet3Val_congr` (`ExpMapContDiff3.lean`) one order up.  `expJet4Val` is the
`expJet4Fund` witness at `t = 1`; `expJet4Val_congr` is the value-only interface (the value depends on
the ten `Q··`/`Q···` inputs only through their values on `[0,1]`, by `expJet4Fund_unique`) that lets us
feed the genuine bilinear/trilinear curves. -/

/-- The **genuine fourth-variation value** `R^{hklm}_v(1)`: the chosen `expJet4Fund` witness at
    `t = 1`. -/
noncomputable def expJet4Val (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) : Point n × Point n :=
  (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
    hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose 1

set_option maxHeartbeats 3200000 in
/-- **`Q`-congruence of `R^{hklm}(1)`.**  If the six second-variation inputs `Qhk,…,Qlm` and the four
    third-variation inputs `Qhkl,…,Qklm` agree on `[0,1]` with their primed counterparts, then
    `expJet4Val` is unchanged: both chosen witnesses solve the same IVP on `[0,1]` (the source
    `expJet4Rhs` at `t` depends on the `Q··`/`Q···` only through their value at `t`), so
    `expJet4Fund_unique` forces the endpoint values to coincide.  The value-only interface that lets us
    feed the genuine bilinear/trilinear curves, whose combined/sum forms agree on `[0,1]` but not
    globally. -/
theorem expJet4Val_congr (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' : ℝ → (Point n × Point n))
    (Qhkl' Qhkm' Qhlm' Qklm' : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQhk' : ContinuousOn Qhk' (Set.Icc (0 : ℝ) 1)) (hQhl' : ContinuousOn Qhl' (Set.Icc (0 : ℝ) 1))
    (hQhm' : ContinuousOn Qhm' (Set.Icc (0 : ℝ) 1)) (hQkl' : ContinuousOn Qkl' (Set.Icc (0 : ℝ) 1))
    (hQkm' : ContinuousOn Qkm' (Set.Icc (0 : ℝ) 1)) (hQlm' : ContinuousOn Qlm' (Set.Icc (0 : ℝ) 1))
    (hQhkl' : ContinuousOn Qhkl' (Set.Icc (0 : ℝ) 1)) (hQhkm' : ContinuousOn Qhkm' (Set.Icc (0 : ℝ) 1))
    (hQhlm' : ContinuousOn Qhlm' (Set.Icc (0 : ℝ) 1)) (hQklm' : ContinuousOn Qklm' (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n)
    (eHk : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhk t = Qhk' t)
    (eHl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhl t = Qhl' t)
    (eHm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhm t = Qhm' t)
    (eKl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qkl t = Qkl' t)
    (eKm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qkm t = Qkm' t)
    (eLm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qlm t = Qlm' t)
    (eHkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhkl t = Qhkl' t)
    (eHkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhkm t = Qhkm' t)
    (eHlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhlm t = Qhlm' t)
    (eKlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qklm t = Qklm' t) :
    expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
        hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m
      = expJet4Val g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont
        hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont
      hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv
    h k l m
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose
    (expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont
      hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose
    hR₁0 hR₂0 hR₁deriv
    (fun t ht => by
      have he : (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv
                hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' h k l m t
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv
                hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
        congr 1
        rw [expJet4Rhs_apply, expJet4Rhs_apply, eHk t ht, eHl t ht, eHm t ht, eKl t ht, eKm t ht,
          eLm t ht, eHkl t ht, eHkm t ht, eHlm t ht, eKlm t ht]
      rw [← he]; exact hR₂deriv t ht)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-! ### Remaining chain to `expJetD4_two_pt_diff` (documentation)

The full lift `expJetD4_two_pt_diff` (`‖expJetD4_v − expJetD4_w‖ ≤ C·‖v−w‖`, mirror of
`expJetD3_two_pt_diff`) still needs, on top of the foundation above:

1. `expJet3CurveG h k l` — the GENUINE third-variation curve = `expJet3Curve` with the three `Q··`
   pair-slots instantiated by the genuine `expJet2Curve` (mirror of `expJet3ValG` at curve level),
   plus its `continuousOn` and curve-level trilinearity (via `expJet3Curve_{add,smul}_*` + a curve
   `Q`-congruence).  Feeds the four triple-`Q···` slots of `expJet4ValG`.

2. `expJet4Rhs_{add,smul}_{h,k,l,m}` — the eight matched-`Q` source-linearity lemmas (ABSENT; the
   one-order-up analog of `expJet3Rhs_{add,smul}_{l,h,k}`).  Each varies the direction together with
   ALL its carrying `Q··`/`Q···` slots and is provable by `simp only [expJet4Rhs_apply, map_add/smul,
   ContinuousLinearMap.add/smul_apply]; abel` — but the 14-term source makes the tandem-slot
   bookkeeping the fiddly part.

3. `expJet4Val_{add,smul}_{h,k,l,m}` (eight matched-`Q` value multilinearity lemmas, via
   `expJet4Rhs_{add,smul}_*` + `expJet4Fund_unique`, using `expJet4Val_congr` above), then
   `expJet4ValG` (genuine, six `expJet2Curve` + four `expJet3CurveG` slots) + `expJet4ValG_norm_le`
   (from `expJet4Fund_value_bound` + `expJet3Fund_value_bound_Icc` + `expJet2Fund_value_bound_Icc`) +
   its multilinearity `expJet4ValG_{add,smul}_{h,k,l,m}`.

4. `expJetD4Inner`/`expJetD4` — the packaged quadrilinear CLM
   `Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n` via three nested
   `mkContinuous₂`/`mkContinuous` layers (mirror of `expJetD3Inner`/`expJetD3`), plus `expJetD4_apply`.

5. `expJetD4_two_pt_diff` — the operator-norm two-point bound, from `expJet4Val_v_two_pt_diff` (J4-3,
   already landed) projected by `expJetPi` and lifted through the four CLM layers by iterated
   `ContinuousLinearMap.opNorm_le_bound` (mirror of `expJetD3_two_pt_diff`, one order up), carrying the
   genuine `hLipD4F`/`Kstar4` data that `expJet4Val_v_two_pt_diff` requires.

Then J4-5 (`expMap_fderiv3_hasFDerivAt` + assemble `ContDiffOn 1 (fderiv³ exp)` = `hfd3` ⟹
`expMap_contDiffOn_four_of_fderiv3_contDiffOn_one` ⟹ `exp ∈ C⁴` UNCONDITIONAL). -/

end QIQTH.ExpMap
