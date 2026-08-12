/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase3
import Mathlib

/-!
# JET-5 TOWER — abstract order-4 curve multilinearity (J5-4 support, brick J4-651)

The abstract-`Q` curve-level congruence and 4-slot multilinearity of `expJet4Curve`
(mirror of `expJet3Curve_congr` / `expJet3Curve_{add,smul}_*` one Fréchet order up), needed to
build the genuine `expJet4CurveG` multilinearity that feeds the `expJet5ValG` bridge.

## Honest firewall (binding)
J5-4 support only.  This does NOT establish `exp_p ∈ C⁵`, does NOT reach `κ = 1/6` or `a₁ = R/6`.
Axiom-free packaging.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1600000

variable {n : ℕ}


theorem expJet4Curve_congr (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm : ℝ → (Point n × Point n))
    (Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (Qhk' Qhl' Qhm' Qkl' Qkm' : ℝ → (Point n × Point n))
    (Qlm' Qhkl' Qhkm' Qhlm' Qklm' : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQhk' : ContinuousOn Qhk' (Set.Icc (0 : ℝ) 1))
    (hQhl' : ContinuousOn Qhl' (Set.Icc (0 : ℝ) 1))
    (hQhm' : ContinuousOn Qhm' (Set.Icc (0 : ℝ) 1))
    (hQkl' : ContinuousOn Qkl' (Set.Icc (0 : ℝ) 1))
    (hQkm' : ContinuousOn Qkm' (Set.Icc (0 : ℝ) 1))
    (hQlm' : ContinuousOn Qlm' (Set.Icc (0 : ℝ) 1))
    (hQhkl' : ContinuousOn Qhkl' (Set.Icc (0 : ℝ) 1))
    (hQhkm' : ContinuousOn Qhkm' (Set.Icc (0 : ℝ) 1))
    (hQhlm' : ContinuousOn Qhlm' (Set.Icc (0 : ℝ) 1))
    (hQklm' : ContinuousOn Qklm' (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n)
    (ehk : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhk t = Qhk' t)
    (ehl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhl t = Qhl' t)
    (ehm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhm t = Qhm' t)
    (ekl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkl t = Qkl' t)
    (ekm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkm t = Qkm' t)
    (elm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qlm t = Qlm' t)
    (ehkl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkl t = Qhkl' t)
    (ehkm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkm t = Qhkm' t)
    (ehlm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhlm t = Qhlm' t)
    (eklm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qklm t = Qklm' t) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m t
      = expJet4Curve g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv h k l m
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose
    (expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose
    hR₁0 hR₂0 hR₁deriv
    (fun t ht => by
      have he : (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' h k l m t
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qkl' Qkm' Qlm' Qhkl' Qhkm' Qhlm' Qklm' hv hΦcont hQhk' hQhl' hQhm' hQkl' hQkm' hQlm' hQhkl' hQhkm' hQhlm' hQklm' h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
        congr 1
        rw [expJet4Rhs_apply, expJet4Rhs_apply, ehk t ht, ehl t ht, ehm t ht, ekl t ht, ekm t ht, elm t ht, ehkl t ht, ehkm t ht, ehlm t ht, eklm t ht]
      rw [← he]; exact hR₂deriv t ht)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl₁ Qhl₂ Qhm₁ : ℝ → (Point n × Point n))
    (Qhm₂ Qkl Qkm Qlm Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ : ℝ → (Point n × Point n))
    (Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m t
      = expJet4Curve g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m t
        + expJet4Curve g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv (h₁ + h₂) k l m
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm h₁ k l m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm h₂ k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm (h₁ + h₂) k l m t := by
        rw [map_add, expJet4Rhs_add_h]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm : ℝ → (Point n × Point n))
    (Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m t
      = c • expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv (c • h) k l m
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm (c • h) k l m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_h]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl Qhm Qkl₁ : ℝ → (Point n × Point n))
    (Qkl₂ Qkm₁ Qkm₂ Qlm Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm₁ Qhkm₂ Qhlm Qklm₁ : ℝ → (Point n × Point n))
    (Qklm₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m t
      = expJet4Curve g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m t
        + expJet4Curve g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv h (k₁ + k₂) l m
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ h k₁ l m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ h k₂ l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) h (k₁ + k₂) l m t := by
        rw [map_add, expJet4Rhs_add_k]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm : ℝ → (Point n × Point n))
    (Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m t
      = c • expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv h (c • k) l m
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) h (c • k) l m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_k]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl₁ Qhl₂ Qhm Qkl₁ : ℝ → (Point n × Point n))
    (Qkl₂ Qkm Qlm₁ Qlm₂ Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm Qhlm₁ Qhlm₂ Qklm₁ : ℝ → (Point n × Point n))
    (Qklm₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm₁ : ContinuousOn Qlm₁ (Set.Icc (0 : ℝ) 1)) (hQlm₂ : ContinuousOn Qlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (h k l₁ l₂ m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k (l₁ + l₂) m t
      = expJet4Curve g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m t
        + expJet4Curve g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k (l₁ + l₂) m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv h k (l₁ + l₂) m
    (expJet4Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k (l₁ + l₂) m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ h k l₁ m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ h k l₂ m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) h k (l₁ + l₂) m t := by
        rw [map_add, expJet4Rhs_add_l]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm : ℝ → (Point n × Point n))
    (Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c) (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m t
      = c • expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c) (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s) hv h k (c • l) m
    (expJet4Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c) (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s) h k (c • l) m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_l]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_add_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm₁ Qhm₂ Qkl : ℝ → (Point n × Point n))
    (Qkm₁ Qkm₂ Qlm₁ Qlm₂ Qhkl : ℝ → (Point n × Point n))
    (Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ Qklm₁ : ℝ → (Point n × Point n))
    (Qklm₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQlm₁ : ContinuousOn Qlm₁ (Set.Icc (0 : ℝ) 1)) (hQlm₂ : ContinuousOn Qlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (h k l m₁ m₂ : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂) (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k l (m₁ + m₂) t
      = expJet4Curve g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁ t
        + expJet4Curve g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂ t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂) (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k l (m₁ + m₂)).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv h k l (m₁ + m₂)
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂) (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂) h k l (m₁ + m₂)).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t
      + (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ h k l m₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ h k l m₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t
                + (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) h k l (m₁ + m₂) t := by
        rw [map_add, expJet4Rhs_add_m]; abel
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

theorem expJet4Curve_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm : ℝ → (Point n × Point n))
    (Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) : ∀ t ∈ (Set.Icc (0 : ℝ) 1),
    expJet4Curve g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s) (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c) hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m) t
      = c • expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m t := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s) (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c) hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m)).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s) (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s) hv h k l (c • m)
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s) (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c) hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m)).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s) (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s) h k l (c • m) t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_m]
      rwa [hval] at hd)
  intro t ht
  simpa only [expJet4Curve] using huniq t ht

end QIQTH.ExpMap
