/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5D5Rhs
import Mathlib

/-!
# JET-5 TOWER — order-5 matched-`Q` value multilinearity `expJet5Val_{add,smul}` (J5-4 support)

The ten matched-`Q` value multilinearity lemmas of `R^{hklmr}_v(1)` (mirror of
`expJet4Val_{add,smul}_*` one Fréchet order up), via `expJet5Rhs_{add,smul}_*` + `expJet5Fund_unique`.

## Honest firewall (binding)
J5-4 support only.  NOT `exp_p ∈ C⁵`, NOT `κ = 1/6`, NOT `a₁ = R/6`.  Axiom-free.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {n : ℕ}


theorem expJet5Val_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl₁ Qhl₂ Qhm₁ : ℝ → (Point n × Point n))
    (Qhm₂ Qhr₁ Qhr₂ Qkl Qkm : ℝ → (Point n × Point n))
    (Qkr Qlm Qlr Qmr Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm₁ Qhkm₂ Qhkr₁ Qhkr₂ : ℝ → (Point n × Point n))
    (Qhlm₁ Qhlm₂ Qhlr₁ Qhlr₂ Qhmr₁ : ℝ → (Point n × Point n))
    (Qhmr₂ Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm₁ Qhklm₂ Qhklr₁ Qhklr₂ Qhkmr₁ : ℝ → (Point n × Point n))
    (Qhkmr₂ Qhlmr₁ Qhlmr₂ Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQhr₁ : ContinuousOn Qhr₁ (Set.Icc (0 : ℝ) 1)) (hQhr₂ : ContinuousOn Qhr₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkr₁ : ContinuousOn Qhkr₁ (Set.Icc (0 : ℝ) 1)) (hQhkr₂ : ContinuousOn Qhkr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlr₁ : ContinuousOn Qhlr₁ (Set.Icc (0 : ℝ) 1)) (hQhlr₂ : ContinuousOn Qhlr₂ (Set.Icc (0 : ℝ) 1))
    (hQhmr₁ : ContinuousOn Qhmr₁ (Set.Icc (0 : ℝ) 1)) (hQhmr₂ : ContinuousOn Qhmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm₁ : ContinuousOn Qhklm₁ (Set.Icc (0 : ℝ) 1)) (hQhklm₂ : ContinuousOn Qhklm₂ (Set.Icc (0 : ℝ) 1))
    (hQhklr₁ : ContinuousOn Qhklr₁ (Set.Icc (0 : ℝ) 1)) (hQhklr₂ : ContinuousOn Qhklr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkmr₁ : ContinuousOn Qhkmr₁ (Set.Icc (0 : ℝ) 1)) (hQhkmr₂ : ContinuousOn Qhkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlmr₁ : ContinuousOn Qhlmr₁ (Set.Icc (0 : ℝ) 1)) (hQhlmr₂ : ContinuousOn Qhlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l m r : Point n) :
    expJet5Val g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) (hQhr₁.add hQhr₂) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm hQklr hQkmr hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) hQklmr (h₁ + h₂) k l m r
      = expJet5Val g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQhr₁ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm₁ hQhlr₁ hQhmr₁ hQklm hQklr hQkmr hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr h₁ k l m r
        + expJet5Val g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQhr₂ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm₂ hQhlr₂ hQhmr₂ hQklm hQklr hQkmr hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr h₂ k l m r := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQhr₁ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm₁ hQhlr₁ hQhmr₁ hQklm hQklr hQkmr hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr h₁ k l m r).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQhr₂ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm₂ hQhlr₂ hQhmr₂ hQklm hQklr hQkmr hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr h₂ k l m r).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet5Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) (hQhr₁.add hQhr₂) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm hQklr hQkmr hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) hQklmr (h₁ + h₂) k l m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr hv (h₁ + h₂) k l m r
    (expJet5Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr hv hΦcont (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) (hQhr₁.add hQhr₂) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm hQklr hQkmr hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) hQklmr (h₁ + h₂) k l m r).choose
    (fun t => (expJet5Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQhr₁ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm₁ hQhlr₁ hQhmr₁ hQklm hQklr hQkmr hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr h₁ k l m r).choose t
      + (expJet5Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQhr₂ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm₂ hQhlr₂ hQhmr₂ hQklm hQklr hQkmr hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr h₂ k l m r).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQhr₁ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm₁ hQhlr₁ hQhmr₁ hQklm hQklr hQkmr hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr h₁ k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr h₁ k l m r t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQhr₂ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm₂ hQhlr₂ hQhmr₂ hQklm hQklr hQkmr hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr h₂ k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr h₂ k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr hv hΦcont hQhk₁ hQhl₁ hQhm₁ hQhr₁ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm₁ hQhlr₁ hQhmr₁ hQklm hQklr hQkmr hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr h₁ k l m r).choose t
                + (expJet5Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr hv hΦcont hQhk₂ hQhl₂ hQhm₂ hQhr₂ hQkl hQkm hQkr hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm₂ hQhlr₂ hQhmr₂ hQklm hQklr hQkmr hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr h₂ k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr (h₁ + h₂) k l m r t := by
        rw [map_add, expJet5Rhs_add_h]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m r : Point n) :
    expJet5Val g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) (hQhr.const_smul c) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) (hQhlm.const_smul c) (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm hQklr hQkmr hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) hQklmr (c • h) k l m r
      = c • expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet5Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) (hQhr.const_smul c) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) (hQhlm.const_smul c) (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm hQklr hQkmr hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) hQklmr (c • h) k l m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr hv (c • h) k l m r
    (expJet5Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr hv hΦcont (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) (hQhr.const_smul c) hQkl hQkm hQkr hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) (hQhlm.const_smul c) (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm hQklr hQkmr hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) hQklmr (c • h) k l m r).choose
    (fun t => c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr (c • h) k l m r t := by
        rw [smul_add, map_smul, expJet5Rhs_smul_h]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl Qhm Qhr : ℝ → (Point n × Point n))
    (Qkl₁ Qkl₂ Qkm₁ Qkm₂ Qkr₁ : ℝ → (Point n × Point n))
    (Qkr₂ Qlm Qlr Qmr Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm₁ Qhkm₂ Qhkr₁ Qhkr₂ : ℝ → (Point n × Point n))
    (Qhlm Qhlr Qhmr Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (Qklr₁ Qklr₂ Qkmr₁ Qkmr₂ Qlmr : ℝ → (Point n × Point n))
    (Qhklm₁ Qhklm₂ Qhklr₁ Qhklr₂ Qhkmr₁ : ℝ → (Point n × Point n))
    (Qhkmr₂ Qhlmr Qklmr₁ Qklmr₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQkr₁ : ContinuousOn Qkr₁ (Set.Icc (0 : ℝ) 1)) (hQkr₂ : ContinuousOn Qkr₂ (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkr₁ : ContinuousOn Qhkr₁ (Set.Icc (0 : ℝ) 1)) (hQhkr₂ : ContinuousOn Qhkr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (hQklr₁ : ContinuousOn Qklr₁ (Set.Icc (0 : ℝ) 1)) (hQklr₂ : ContinuousOn Qklr₂ (Set.Icc (0 : ℝ) 1))
    (hQkmr₁ : ContinuousOn Qkmr₁ (Set.Icc (0 : ℝ) 1)) (hQkmr₂ : ContinuousOn Qkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm₁ : ContinuousOn Qhklm₁ (Set.Icc (0 : ℝ) 1)) (hQhklm₂ : ContinuousOn Qhklm₂ (Set.Icc (0 : ℝ) 1))
    (hQhklr₁ : ContinuousOn Qhklr₁ (Set.Icc (0 : ℝ) 1)) (hQhklr₂ : ContinuousOn Qhklr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkmr₁ : ContinuousOn Qhkmr₁ (Set.Icc (0 : ℝ) 1)) (hQhkmr₂ : ContinuousOn Qhkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr₁ : ContinuousOn Qklmr₁ (Set.Icc (0 : ℝ) 1)) (hQklmr₂ : ContinuousOn Qklmr₂ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l m r : Point n) :
    expJet5Val g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm hQhr (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) (hQkr₁.add hQkr₂) hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) hQhlm hQhlr hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) hQhlmr (hQklmr₁.add hQklmr₂) h (k₁ + k₂) l m r
      = expJet5Val g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ hv hΦcont hQhk₁ hQhl hQhm hQhr hQkl₁ hQkm₁ hQkr₁ hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm hQhlr hQhmr hQklm₁ hQklr₁ hQkmr₁ hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr hQklmr₁ h k₁ l m r
        + expJet5Val g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ hv hΦcont hQhk₂ hQhl hQhm hQhr hQkl₂ hQkm₂ hQkr₂ hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm hQhlr hQhmr hQklm₂ hQklr₂ hQkmr₂ hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr hQklmr₂ h k₂ l m r := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ hv hΦcont hQhk₁ hQhl hQhm hQhr hQkl₁ hQkm₁ hQkr₁ hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm hQhlr hQhmr hQklm₁ hQklr₁ hQkmr₁ hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr hQklmr₁ h k₁ l m r).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ hv hΦcont hQhk₂ hQhl hQhm hQhr hQkl₂ hQkm₂ hQkr₂ hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm hQhlr hQhmr hQklm₂ hQklr₂ hQkmr₂ hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr hQklmr₂ h k₂ l m r).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet5Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm hQhr (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) (hQkr₁.add hQkr₂) hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) hQhlm hQhlr hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) hQhlmr (hQklmr₁.add hQklmr₂) h (k₁ + k₂) l m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) hv h (k₁ + k₂) l m r
    (expJet5Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont (hQhk₁.add hQhk₂) hQhl hQhm hQhr (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) (hQkr₁.add hQkr₂) hQlm hQlr hQmr (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhkr₁.add hQhkr₂) hQhlm hQhlr hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) hQlmr (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) hQhlmr (hQklmr₁.add hQklmr₂) h (k₁ + k₂) l m r).choose
    (fun t => (expJet5Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ hv hΦcont hQhk₁ hQhl hQhm hQhr hQkl₁ hQkm₁ hQkr₁ hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm hQhlr hQhmr hQklm₁ hQklr₁ hQkmr₁ hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr hQklmr₁ h k₁ l m r).choose t
      + (expJet5Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ hv hΦcont hQhk₂ hQhl hQhm hQhr hQkl₂ hQkm₂ hQkr₂ hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm hQhlr hQhmr hQklm₂ hQklr₂ hQkmr₂ hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr hQklmr₂ h k₂ l m r).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ hv hΦcont hQhk₁ hQhl hQhm hQhr hQkl₁ hQkm₁ hQkr₁ hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm hQhlr hQhmr hQklm₁ hQklr₁ hQkmr₁ hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr hQklmr₁ h k₁ l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ h k₁ l m r t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ hv hΦcont hQhk₂ hQhl hQhm hQhr hQkl₂ hQkm₂ hQkr₂ hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm hQhlr hQhmr hQklm₂ hQklr₂ hQkmr₂ hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr hQklmr₂ h k₂ l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ h k₂ l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ hv hΦcont hQhk₁ hQhl hQhm hQhr hQkl₁ hQkm₁ hQkr₁ hQlm hQlr hQmr hQhkl₁ hQhkm₁ hQhkr₁ hQhlm hQhlr hQhmr hQklm₁ hQklr₁ hQkmr₁ hQlmr hQhklm₁ hQhklr₁ hQhkmr₁ hQhlmr hQklmr₁ h k₁ l m r).choose t
                + (expJet5Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ hv hΦcont hQhk₂ hQhl hQhm hQhr hQkl₂ hQkm₂ hQkr₂ hQlm hQlr hQmr hQhkl₂ hQhkm₂ hQhkr₂ hQhlm hQhlr hQhmr hQklm₂ hQklr₂ hQkmr₂ hQlmr hQhklm₂ hQhklr₂ hQhkmr₂ hQhlmr hQklmr₂ h k₂ l m r).choose t)
            + expJet5Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) h (k₁ + k₂) l m r t := by
        rw [map_add, expJet5Rhs_add_k]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m r : Point n) :
    expJet5Val g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) hv hΦcont (hQhk.const_smul c) hQhl hQhm hQhr (hQkl.const_smul c) (hQkm.const_smul c) (hQkr.const_smul c) hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) hQhlm hQhlr hQhmr (hQklm.const_smul c) (hQklr.const_smul c) (hQkmr.const_smul c) hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) hQhlmr (hQklmr.const_smul c) h (c • k) l m r
      = c • expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet5Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) hv hΦcont (hQhk.const_smul c) hQhl hQhm hQhr (hQkl.const_smul c) (hQkm.const_smul c) (hQkr.const_smul c) hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) hQhlm hQhlr hQhmr (hQklm.const_smul c) (hQklr.const_smul c) (hQkmr.const_smul c) hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) hQhlmr (hQklmr.const_smul c) h (c • k) l m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) hv h (c • k) l m r
    (expJet5Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) hv hΦcont (hQhk.const_smul c) hQhl hQhm hQhr (hQkl.const_smul c) (hQkm.const_smul c) (hQkr.const_smul c) hQlm hQlr hQmr (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhkr.const_smul c) hQhlm hQhlr hQhmr (hQklm.const_smul c) (hQklr.const_smul c) (hQkmr.const_smul c) hQlmr (hQhklm.const_smul c) (hQhklr.const_smul c) (hQhkmr.const_smul c) hQhlmr (hQklmr.const_smul c) h (c • k) l m r).choose
    (fun t => c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) h (c • k) l m r t := by
        rw [smul_add, map_smul, expJet5Rhs_smul_k]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl₁ Qhl₂ Qhm Qhr : ℝ → (Point n × Point n))
    (Qkl₁ Qkl₂ Qkm Qkr Qlm₁ : ℝ → (Point n × Point n))
    (Qlm₂ Qlr₁ Qlr₂ Qmr Qhkl₁ : ℝ → (Point n × Point n))
    (Qhkl₂ Qhkm Qhkr Qhlm₁ Qhlm₂ : ℝ → (Point n × Point n))
    (Qhlr₁ Qhlr₂ Qhmr Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (Qklr₁ Qklr₂ Qkmr Qlmr₁ Qlmr₂ : ℝ → (Point n × Point n))
    (Qhklm₁ Qhklm₂ Qhklr₁ Qhklr₂ Qhkmr : ℝ → (Point n × Point n))
    (Qhlmr₁ Qhlmr₂ Qklmr₁ Qklmr₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm₁ : ContinuousOn Qlm₁ (Set.Icc (0 : ℝ) 1)) (hQlm₂ : ContinuousOn Qlm₂ (Set.Icc (0 : ℝ) 1))
    (hQlr₁ : ContinuousOn Qlr₁ (Set.Icc (0 : ℝ) 1)) (hQlr₂ : ContinuousOn Qlr₂ (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlr₁ : ContinuousOn Qhlr₁ (Set.Icc (0 : ℝ) 1)) (hQhlr₂ : ContinuousOn Qhlr₂ (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (hQklr₁ : ContinuousOn Qklr₁ (Set.Icc (0 : ℝ) 1)) (hQklr₂ : ContinuousOn Qklr₂ (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr₁ : ContinuousOn Qlmr₁ (Set.Icc (0 : ℝ) 1)) (hQlmr₂ : ContinuousOn Qlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhklm₁ : ContinuousOn Qhklm₁ (Set.Icc (0 : ℝ) 1)) (hQhklm₂ : ContinuousOn Qhklm₂ (Set.Icc (0 : ℝ) 1))
    (hQhklr₁ : ContinuousOn Qhklr₁ (Set.Icc (0 : ℝ) 1)) (hQhklr₂ : ContinuousOn Qhklr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr₁ : ContinuousOn Qhlmr₁ (Set.Icc (0 : ℝ) 1)) (hQhlmr₂ : ContinuousOn Qhlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklmr₁ : ContinuousOn Qklmr₁ (Set.Icc (0 : ℝ) 1)) (hQklmr₂ : ContinuousOn Qklmr₂ (Set.Icc (0 : ℝ) 1))
    (h k l₁ l₂ m r : Point n) :
    expJet5Val g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm hQhr (hQkl₁.add hQkl₂) hQkm hQkr (hQlm₁.add hQlm₂) (hQlr₁.add hQlr₂) hQmr (hQhkl₁.add hQhkl₂) hQhkm hQhkr (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) hQkmr (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) hQhkmr (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k (l₁ + l₂) m r
      = expJet5Val g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl₁ hQhm hQhr hQkl₁ hQkm hQkr hQlm₁ hQlr₁ hQmr hQhkl₁ hQhkm hQhkr hQhlm₁ hQhlr₁ hQhmr hQklm₁ hQklr₁ hQkmr hQlmr₁ hQhklm₁ hQhklr₁ hQhkmr hQhlmr₁ hQklmr₁ h k l₁ m r
        + expJet5Val g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl₂ hQhm hQhr hQkl₂ hQkm hQkr hQlm₂ hQlr₂ hQmr hQhkl₂ hQhkm hQhkr hQhlm₂ hQhlr₂ hQhmr hQklm₂ hQklr₂ hQkmr hQlmr₂ hQhklm₂ hQhklr₂ hQhkmr hQhlmr₂ hQklmr₂ h k l₂ m r := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl₁ hQhm hQhr hQkl₁ hQkm hQkr hQlm₁ hQlr₁ hQmr hQhkl₁ hQhkm hQhkr hQhlm₁ hQhlr₁ hQhmr hQklm₁ hQklr₁ hQkmr hQlmr₁ hQhklm₁ hQhklr₁ hQhkmr hQhlmr₁ hQklmr₁ h k l₁ m r).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl₂ hQhm hQhr hQkl₂ hQkm hQkr hQlm₂ hQlr₂ hQmr hQhkl₂ hQhkm hQhkr hQhlm₂ hQhlr₂ hQhmr hQklm₂ hQklr₂ hQkmr hQlmr₂ hQhklm₂ hQhklr₂ hQhkmr hQhlmr₂ hQklmr₂ h k l₂ m r).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm hQhr (hQkl₁.add hQkl₂) hQkm hQkr (hQlm₁.add hQlm₂) (hQlr₁.add hQlr₂) hQmr (hQhkl₁.add hQhkl₂) hQhkm hQhkr (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) hQkmr (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) hQhkmr (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k (l₁ + l₂) m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv h k (l₁ + l₂) m r
    (expJet5Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm hQhr (hQkl₁.add hQkl₂) hQkm hQkr (hQlm₁.add hQlm₂) (hQlr₁.add hQlr₂) hQmr (hQhkl₁.add hQhkl₂) hQhkm hQhkr (hQhlm₁.add hQhlm₂) (hQhlr₁.add hQhlr₂) hQhmr (hQklm₁.add hQklm₂) (hQklr₁.add hQklr₂) hQkmr (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) (hQhklr₁.add hQhklr₂) hQhkmr (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k (l₁ + l₂) m r).choose
    (fun t => (expJet5Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl₁ hQhm hQhr hQkl₁ hQkm hQkr hQlm₁ hQlr₁ hQmr hQhkl₁ hQhkm hQhkr hQhlm₁ hQhlr₁ hQhmr hQklm₁ hQklr₁ hQkmr hQlmr₁ hQhklm₁ hQhklr₁ hQhkmr hQhlmr₁ hQklmr₁ h k l₁ m r).choose t
      + (expJet5Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl₂ hQhm hQhr hQkl₂ hQkm hQkr hQlm₂ hQlr₂ hQmr hQhkl₂ hQhkm hQhkr hQhlm₂ hQhlr₂ hQhmr hQklm₂ hQklr₂ hQkmr hQlmr₂ hQhklm₂ hQhklr₂ hQhkmr hQhlmr₂ hQklmr₂ h k l₂ m r).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl₁ hQhm hQhr hQkl₁ hQkm hQkr hQlm₁ hQlr₁ hQmr hQhkl₁ hQhkm hQhkr hQhlm₁ hQhlr₁ hQhmr hQklm₁ hQklr₁ hQkmr hQlmr₁ hQhklm₁ hQhklr₁ hQhkmr hQhlmr₁ hQklmr₁ h k l₁ m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ h k l₁ m r t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl₂ hQhm hQhr hQkl₂ hQkm hQkr hQlm₂ hQlr₂ hQmr hQhkl₂ hQhkm hQhkr hQhlm₂ hQhlr₂ hQhmr hQklm₂ hQklr₂ hQkmr hQlmr₂ hQhklm₂ hQhklr₂ hQhkmr hQhlmr₂ hQklmr₂ h k l₂ m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ h k l₂ m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl₁ hQhm hQhr hQkl₁ hQkm hQkr hQlm₁ hQlr₁ hQmr hQhkl₁ hQhkm hQhkr hQhlm₁ hQhlr₁ hQhmr hQklm₁ hQklr₁ hQkmr hQlmr₁ hQhklm₁ hQhklr₁ hQhkmr hQhlmr₁ hQklmr₁ h k l₁ m r).choose t
                + (expJet5Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl₂ hQhm hQhr hQkl₂ hQkm hQkr hQlm₂ hQlr₂ hQmr hQhkl₂ hQhkm hQhkr hQhlm₂ hQhlr₂ hQhmr hQklm₂ hQklr₂ hQkmr hQlmr₂ hQhklm₂ hQhklr₂ hQhkmr hQhlmr₂ hQklmr₂ h k l₂ m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k (l₁ + l₂) m r t := by
        rw [map_add, expJet5Rhs_add_l]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m r : Point n) :
    expJet5Val g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk (hQhl.const_smul c) hQhm hQhr (hQkl.const_smul c) hQkm hQkr (hQlm.const_smul c) (hQlr.const_smul c) hQmr (hQhkl.const_smul c) hQhkm hQhkr (hQhlm.const_smul c) (hQhlr.const_smul c) hQhmr (hQklm.const_smul c) (hQklr.const_smul c) hQkmr (hQlmr.const_smul c) (hQhklm.const_smul c) (hQhklr.const_smul c) hQhkmr (hQhlmr.const_smul c) (hQklmr.const_smul c) h k (c • l) m r
      = c • expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk (hQhl.const_smul c) hQhm hQhr (hQkl.const_smul c) hQkm hQkr (hQlm.const_smul c) (hQlr.const_smul c) hQmr (hQhkl.const_smul c) hQhkm hQhkr (hQhlm.const_smul c) (hQhlr.const_smul c) hQhmr (hQklm.const_smul c) (hQklr.const_smul c) hQkmr (hQlmr.const_smul c) (hQhklm.const_smul c) (hQhklr.const_smul c) hQhkmr (hQhlmr.const_smul c) (hQklmr.const_smul c) h k (c • l) m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv h k (c • l) m r
    (expJet5Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk (hQhl.const_smul c) hQhm hQhr (hQkl.const_smul c) hQkm hQkr (hQlm.const_smul c) (hQlr.const_smul c) hQmr (hQhkl.const_smul c) hQhkm hQhkr (hQhlm.const_smul c) (hQhlr.const_smul c) hQhmr (hQklm.const_smul c) (hQklr.const_smul c) hQkmr (hQlmr.const_smul c) (hQhklm.const_smul c) (hQhklr.const_smul c) hQhkmr (hQhlmr.const_smul c) (hQklmr.const_smul c) h k (c • l) m r).choose
    (fun t => c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k (c • l) m r t := by
        rw [smul_add, map_smul, expJet5Rhs_smul_l]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_add_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm₁ Qhm₂ Qhr : ℝ → (Point n × Point n))
    (Qkl Qkm₁ Qkm₂ Qkr Qlm₁ : ℝ → (Point n × Point n))
    (Qlm₂ Qlr Qmr₁ Qmr₂ Qhkl : ℝ → (Point n × Point n))
    (Qhkm₁ Qhkm₂ Qhkr Qhlm₁ Qhlm₂ : ℝ → (Point n × Point n))
    (Qhlr Qhmr₁ Qhmr₂ Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (Qklr Qkmr₁ Qkmr₂ Qlmr₁ Qlmr₂ : ℝ → (Point n × Point n))
    (Qhklm₁ Qhklm₂ Qhklr Qhkmr₁ Qhkmr₂ : ℝ → (Point n × Point n))
    (Qhlmr₁ Qhlmr₂ Qklmr₁ Qklmr₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm₁ : ContinuousOn Qlm₁ (Set.Icc (0 : ℝ) 1)) (hQlm₂ : ContinuousOn Qlm₂ (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr₁ : ContinuousOn Qmr₁ (Set.Icc (0 : ℝ) 1)) (hQmr₂ : ContinuousOn Qmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr₁ : ContinuousOn Qhmr₁ (Set.Icc (0 : ℝ) 1)) (hQhmr₂ : ContinuousOn Qhmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr₁ : ContinuousOn Qkmr₁ (Set.Icc (0 : ℝ) 1)) (hQkmr₂ : ContinuousOn Qkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQlmr₁ : ContinuousOn Qlmr₁ (Set.Icc (0 : ℝ) 1)) (hQlmr₂ : ContinuousOn Qlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhklm₁ : ContinuousOn Qhklm₁ (Set.Icc (0 : ℝ) 1)) (hQhklm₂ : ContinuousOn Qhklm₂ (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr₁ : ContinuousOn Qhkmr₁ (Set.Icc (0 : ℝ) 1)) (hQhkmr₂ : ContinuousOn Qhkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlmr₁ : ContinuousOn Qhlmr₁ (Set.Icc (0 : ℝ) 1)) (hQhlmr₂ : ContinuousOn Qhlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklmr₁ : ContinuousOn Qklmr₁ (Set.Icc (0 : ℝ) 1)) (hQklmr₂ : ContinuousOn Qklmr₂ (Set.Icc (0 : ℝ) 1))
    (h k l m₁ m₂ r : Point n) :
    expJet5Val g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQhr hQkl (hQkm₁.add hQkm₂) hQkr (hQlm₁.add hQlm₂) hQlr (hQmr₁.add hQmr₂) hQhkl (hQhkm₁.add hQhkm₂) hQhkr (hQhlm₁.add hQhlm₂) hQhlr (hQhmr₁.add hQhmr₂) (hQklm₁.add hQklm₂) hQklr (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) hQhklr (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l (m₁ + m₂) r
      = expJet5Val g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm₁ hQhr hQkl hQkm₁ hQkr hQlm₁ hQlr hQmr₁ hQhkl hQhkm₁ hQhkr hQhlm₁ hQhlr hQhmr₁ hQklm₁ hQklr hQkmr₁ hQlmr₁ hQhklm₁ hQhklr hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m₁ r
        + expJet5Val g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm₂ hQhr hQkl hQkm₂ hQkr hQlm₂ hQlr hQmr₂ hQhkl hQhkm₂ hQhkr hQhlm₂ hQhlr hQhmr₂ hQklm₂ hQklr hQkmr₂ hQlmr₂ hQhklm₂ hQhklr hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m₂ r := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm₁ hQhr hQkl hQkm₁ hQkr hQlm₁ hQlr hQmr₁ hQhkl hQhkm₁ hQhkr hQhlm₁ hQhlr hQhmr₁ hQklm₁ hQklr hQkmr₁ hQlmr₁ hQhklm₁ hQhklr hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m₁ r).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm₂ hQhr hQkl hQkm₂ hQkr hQlm₂ hQlr hQmr₂ hQhkl hQhkm₂ hQhkr hQhlm₂ hQhlr hQhmr₂ hQklm₂ hQklr hQkmr₂ hQlmr₂ hQhklm₂ hQhklr hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m₂ r).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQhr hQkl (hQkm₁.add hQkm₂) hQkr (hQlm₁.add hQlm₂) hQlr (hQmr₁.add hQmr₂) hQhkl (hQhkm₁.add hQhkm₂) hQhkr (hQhlm₁.add hQhlm₂) hQhlr (hQhmr₁.add hQhmr₂) (hQklm₁.add hQklm₂) hQklr (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) hQhklr (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l (m₁ + m₂) r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv h k l (m₁ + m₂) r
    (expJet5Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQhr hQkl (hQkm₁.add hQkm₂) hQkr (hQlm₁.add hQlm₂) hQlr (hQmr₁.add hQmr₂) hQhkl (hQhkm₁.add hQhkm₂) hQhkr (hQhlm₁.add hQhlm₂) hQhlr (hQhmr₁.add hQhmr₂) (hQklm₁.add hQklm₂) hQklr (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) (hQhklm₁.add hQhklm₂) hQhklr (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l (m₁ + m₂) r).choose
    (fun t => (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm₁ hQhr hQkl hQkm₁ hQkr hQlm₁ hQlr hQmr₁ hQhkl hQhkm₁ hQhkr hQhlm₁ hQhlr hQhmr₁ hQklm₁ hQklr hQkmr₁ hQlmr₁ hQhklm₁ hQhklr hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m₁ r).choose t
      + (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm₂ hQhr hQkl hQkm₂ hQkr hQlm₂ hQlr hQmr₂ hQhkl hQhkm₂ hQhkr hQhlm₂ hQhlr hQhmr₂ hQklm₂ hQklr hQkmr₂ hQlmr₂ hQhklm₂ hQhklr hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m₂ r).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm₁ hQhr hQkl hQkm₁ hQkr hQlm₁ hQlr hQmr₁ hQhkl hQhkm₁ hQhkr hQhlm₁ hQhlr hQhmr₁ hQklm₁ hQklr hQkmr₁ hQlmr₁ hQhklm₁ hQhklr hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m₁ r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ h k l m₁ r t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm₂ hQhr hQkl hQkm₂ hQkr hQlm₂ hQlr hQmr₂ hQhkl hQhkm₂ hQhkr hQhlm₂ hQhlr hQhmr₂ hQklm₂ hQklr hQkmr₂ hQlmr₂ hQhklm₂ hQhklr hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m₂ r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ h k l m₂ r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm₁ hQhr hQkl hQkm₁ hQkr hQlm₁ hQlr hQmr₁ hQhkl hQhkm₁ hQhkr hQhlm₁ hQhlr hQhmr₁ hQklm₁ hQklr hQkmr₁ hQlmr₁ hQhklm₁ hQhklr hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m₁ r).choose t
                + (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm₂ hQhr hQkl hQkm₂ hQkr hQlm₂ hQlr hQmr₂ hQhkl hQhkm₂ hQhkr hQhlm₂ hQhlr hQhmr₂ hQklm₂ hQklr hQkmr₂ hQlmr₂ hQhklm₂ hQhklr hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m₂ r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k l (m₁ + m₂) r t := by
        rw [map_add, expJet5Rhs_add_m]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m r : Point n) :
    expJet5Val g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQhr hQkl (hQkm.const_smul c) hQkr (hQlm.const_smul c) hQlr (hQmr.const_smul c) hQhkl (hQhkm.const_smul c) hQhkr (hQhlm.const_smul c) hQhlr (hQhmr.const_smul c) (hQklm.const_smul c) hQklr (hQkmr.const_smul c) (hQlmr.const_smul c) (hQhklm.const_smul c) hQhklr (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l (c • m) r
      = c • expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQhr hQkl (hQkm.const_smul c) hQkr (hQlm.const_smul c) hQlr (hQmr.const_smul c) hQhkl (hQhkm.const_smul c) hQhkr (hQhlm.const_smul c) hQhlr (hQhmr.const_smul c) (hQklm.const_smul c) hQklr (hQkmr.const_smul c) (hQlmr.const_smul c) (hQhklm.const_smul c) hQhklr (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l (c • m) r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv h k l (c • m) r
    (expJet5Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl (hQhm.const_smul c) hQhr hQkl (hQkm.const_smul c) hQkr (hQlm.const_smul c) hQlr (hQmr.const_smul c) hQhkl (hQhkm.const_smul c) hQhkr (hQhlm.const_smul c) hQhlr (hQhmr.const_smul c) (hQklm.const_smul c) hQklr (hQkmr.const_smul c) (hQlmr.const_smul c) (hQhklm.const_smul c) hQhklr (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l (c • m) r).choose
    (fun t => c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k l (c • m) r t := by
        rw [smul_add, map_smul, expJet5Rhs_smul_m]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_add_r (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr₁ Qhr₂ : ℝ → (Point n × Point n))
    (Qkl Qkm Qkr₁ Qkr₂ Qlm : ℝ → (Point n × Point n))
    (Qlr₁ Qlr₂ Qmr₁ Qmr₂ Qhkl : ℝ → (Point n × Point n))
    (Qhkm Qhkr₁ Qhkr₂ Qhlm Qhlr₁ : ℝ → (Point n × Point n))
    (Qhlr₂ Qhmr₁ Qhmr₂ Qklm Qklr₁ : ℝ → (Point n × Point n))
    (Qklr₂ Qkmr₁ Qkmr₂ Qlmr₁ Qlmr₂ : ℝ → (Point n × Point n))
    (Qhklm Qhklr₁ Qhklr₂ Qhkmr₁ Qhkmr₂ : ℝ → (Point n × Point n))
    (Qhlmr₁ Qhlmr₂ Qklmr₁ Qklmr₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr₁ : ContinuousOn Qhr₁ (Set.Icc (0 : ℝ) 1)) (hQhr₂ : ContinuousOn Qhr₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr₁ : ContinuousOn Qkr₁ (Set.Icc (0 : ℝ) 1)) (hQkr₂ : ContinuousOn Qkr₂ (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr₁ : ContinuousOn Qlr₁ (Set.Icc (0 : ℝ) 1)) (hQlr₂ : ContinuousOn Qlr₂ (Set.Icc (0 : ℝ) 1))
    (hQmr₁ : ContinuousOn Qmr₁ (Set.Icc (0 : ℝ) 1)) (hQmr₂ : ContinuousOn Qmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr₁ : ContinuousOn Qhkr₁ (Set.Icc (0 : ℝ) 1)) (hQhkr₂ : ContinuousOn Qhkr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr₁ : ContinuousOn Qhlr₁ (Set.Icc (0 : ℝ) 1)) (hQhlr₂ : ContinuousOn Qhlr₂ (Set.Icc (0 : ℝ) 1))
    (hQhmr₁ : ContinuousOn Qhmr₁ (Set.Icc (0 : ℝ) 1)) (hQhmr₂ : ContinuousOn Qhmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr₁ : ContinuousOn Qklr₁ (Set.Icc (0 : ℝ) 1)) (hQklr₂ : ContinuousOn Qklr₂ (Set.Icc (0 : ℝ) 1))
    (hQkmr₁ : ContinuousOn Qkmr₁ (Set.Icc (0 : ℝ) 1)) (hQkmr₂ : ContinuousOn Qkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQlmr₁ : ContinuousOn Qlmr₁ (Set.Icc (0 : ℝ) 1)) (hQlmr₂ : ContinuousOn Qlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr₁ : ContinuousOn Qhklr₁ (Set.Icc (0 : ℝ) 1)) (hQhklr₂ : ContinuousOn Qhklr₂ (Set.Icc (0 : ℝ) 1))
    (hQhkmr₁ : ContinuousOn Qhkmr₁ (Set.Icc (0 : ℝ) 1)) (hQhkmr₂ : ContinuousOn Qhkmr₂ (Set.Icc (0 : ℝ) 1))
    (hQhlmr₁ : ContinuousOn Qhlmr₁ (Set.Icc (0 : ℝ) 1)) (hQhlmr₂ : ContinuousOn Qhlmr₂ (Set.Icc (0 : ℝ) 1))
    (hQklmr₁ : ContinuousOn Qklmr₁ (Set.Icc (0 : ℝ) 1)) (hQklmr₂ : ContinuousOn Qklmr₂ (Set.Icc (0 : ℝ) 1))
    (h k l m r₁ r₂ : Point n) :
    expJet5Val g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl hQhm (hQhr₁.add hQhr₂) hQkl hQkm (hQkr₁.add hQkr₂) hQlm (hQlr₁.add hQlr₂) (hQmr₁.add hQmr₂) hQhkl hQhkm (hQhkr₁.add hQhkr₂) hQhlm (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) hQhklm (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l m (r₁ + r₂)
      = expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm hQhr₁ hQkl hQkm hQkr₁ hQlm hQlr₁ hQmr₁ hQhkl hQhkm hQhkr₁ hQhlm hQhlr₁ hQhmr₁ hQklm hQklr₁ hQkmr₁ hQlmr₁ hQhklm hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m r₁
        + expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm hQhr₂ hQkl hQkm hQkr₂ hQlm hQlr₂ hQmr₂ hQhkl hQhkm hQhkr₂ hQhlm hQhlr₂ hQhmr₂ hQklm hQklr₂ hQkmr₂ hQlmr₂ hQhklm hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m r₂ := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm hQhr₁ hQkl hQkm hQkr₁ hQlm hQlr₁ hQmr₁ hQhkl hQhkm hQhkr₁ hQhlm hQhlr₁ hQhmr₁ hQklm hQklr₁ hQkmr₁ hQlmr₁ hQhklm hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m r₁).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm hQhr₂ hQkl hQkm hQkr₂ hQlm hQlr₂ hQmr₂ hQhkl hQhkm hQhkr₂ hQhlm hQhlr₂ hQhmr₂ hQklm hQklr₂ hQkmr₂ hQlmr₂ hQhklm hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m r₂).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl hQhm (hQhr₁.add hQhr₂) hQkl hQkm (hQkr₁.add hQkr₂) hQlm (hQlr₁.add hQlr₂) (hQmr₁.add hQmr₂) hQhkl hQhkm (hQhkr₁.add hQhkr₂) hQhlm (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) hQhklm (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l m (r₁ + r₂)).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv h k l m (r₁ + r₂)
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) hv hΦcont hQhk hQhl hQhm (hQhr₁.add hQhr₂) hQkl hQkm (hQkr₁.add hQkr₂) hQlm (hQlr₁.add hQlr₂) (hQmr₁.add hQmr₂) hQhkl hQhkm (hQhkr₁.add hQhkr₂) hQhlm (hQhlr₁.add hQhlr₂) (hQhmr₁.add hQhmr₂) hQklm (hQklr₁.add hQklr₂) (hQkmr₁.add hQkmr₂) (hQlmr₁.add hQlmr₂) hQhklm (hQhklr₁.add hQhklr₂) (hQhkmr₁.add hQhkmr₂) (hQhlmr₁.add hQhlmr₂) (hQklmr₁.add hQklmr₂) h k l m (r₁ + r₂)).choose
    (fun t => (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm hQhr₁ hQkl hQkm hQkr₁ hQlm hQlr₁ hQmr₁ hQhkl hQhkm hQhkr₁ hQhlm hQhlr₁ hQhmr₁ hQklm hQklr₁ hQkmr₁ hQlmr₁ hQhklm hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m r₁).choose t
      + (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm hQhr₂ hQkl hQkm hQkr₂ hQlm hQlr₂ hQmr₂ hQhkl hQhkm hQhkr₂ hQhlm hQhlr₂ hQhmr₂ hQklm hQklr₂ hQkmr₂ hQlmr₂ hQhklm hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m r₂).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm hQhr₁ hQkl hQkm hQkr₁ hQlm hQlr₁ hQmr₁ hQhkl hQhkm hQhkr₁ hQhlm hQhlr₁ hQhmr₁ hQklm hQklr₁ hQkmr₁ hQlmr₁ hQhklm hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m r₁).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ h k l m r₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm hQhr₂ hQkl hQkm hQkr₂ hQlm hQlr₂ hQmr₂ hQhkl hQhkm hQhkr₂ hQhlm hQhlr₂ hQhmr₂ hQklm hQklr₂ hQkmr₂ hQlmr₂ hQhklm hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m r₂).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ h k l m r₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ hv hΦcont hQhk hQhl hQhm hQhr₁ hQkl hQkm hQkr₁ hQlm hQlr₁ hQmr₁ hQhkl hQhkm hQhkr₁ hQhlm hQhlr₁ hQhmr₁ hQklm hQklr₁ hQkmr₁ hQlmr₁ hQhklm hQhklr₁ hQhkmr₁ hQhlmr₁ hQklmr₁ h k l m r₁).choose t
                + (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ hv hΦcont hQhk hQhl hQhm hQhr₂ hQkl hQkm hQkr₂ hQlm hQlr₂ hQmr₂ hQhkl hQhkm hQhkr₂ hQhlm hQhlr₂ hQhmr₂ hQklm hQklr₂ hQkmr₂ hQlmr₂ hQhklm hQhklr₂ hQhkmr₂ hQhlmr₂ hQklmr₂ h k l m r₂).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k l m (r₁ + r₂) t := by
        rw [map_add, expJet5Rhs_add_r]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

theorem expJet5Val_smul_r (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQhr : ContinuousOn Qhr (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQkr : ContinuousOn Qkr (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQlr : ContinuousOn Qlr (Set.Icc (0 : ℝ) 1))
    (hQmr : ContinuousOn Qmr (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhkr : ContinuousOn Qhkr (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQhlr : ContinuousOn Qhlr (Set.Icc (0 : ℝ) 1))
    (hQhmr : ContinuousOn Qhmr (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (hQklr : ContinuousOn Qklr (Set.Icc (0 : ℝ) 1))
    (hQkmr : ContinuousOn Qkmr (Set.Icc (0 : ℝ) 1))
    (hQlmr : ContinuousOn Qlmr (Set.Icc (0 : ℝ) 1))
    (hQhklm : ContinuousOn Qhklm (Set.Icc (0 : ℝ) 1))
    (hQhklr : ContinuousOn Qhklr (Set.Icc (0 : ℝ) 1))
    (hQhkmr : ContinuousOn Qhkmr (Set.Icc (0 : ℝ) 1))
    (hQhlmr : ContinuousOn Qhlmr (Set.Icc (0 : ℝ) 1))
    (hQklmr : ContinuousOn Qklmr (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m r : Point n) :
    expJet5Val g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl hQhm (hQhr.const_smul c) hQkl hQkm (hQkr.const_smul c) hQlm (hQlr.const_smul c) (hQmr.const_smul c) hQhkl hQhkm (hQhkr.const_smul c) hQhlm (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm (hQklr.const_smul c) (hQkmr.const_smul c) (hQlmr.const_smul c) hQhklm (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l m (c • r)
      = c • expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl hQhm (hQhr.const_smul c) hQkl hQkm (hQkr.const_smul c) hQlm (hQlr.const_smul c) (hQmr.const_smul c) hQhkl hQhkm (hQhkr.const_smul c) hQhlm (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm (hQklr.const_smul c) (hQkmr.const_smul c) (hQlmr.const_smul c) hQhklm (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l m (c • r)).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv h k l m (c • r)
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) hv hΦcont hQhk hQhl hQhm (hQhr.const_smul c) hQkl hQkm (hQkr.const_smul c) hQlm (hQlr.const_smul c) (hQmr.const_smul c) hQhkl hQhkm (hQhkr.const_smul c) hQhlm (hQhlr.const_smul c) (hQhmr.const_smul c) hQklm (hQklr.const_smul c) (hQkmr.const_smul c) (hQlmr.const_smul c) hQhklm (hQhklr.const_smul c) (hQhkmr.const_smul c) (hQhlmr.const_smul c) (hQklmr.const_smul c) h k l m (c • r)).choose
    (fun t => c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
              + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k l m (c • r) t := by
        rw [smul_add, map_smul, expJet5Rhs_smul_r]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

end QIQTH.ExpMap
