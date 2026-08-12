/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase3
import Mathlib

/-!
# JET-5 TOWER — order-5 source linearity + value congruence (J5-4 support, brick J4-651)

The ten matched-`Q` source-linearity lemmas `expJet5Rhs_{add,smul}_{h,k,l,m,r}` and the 25-slot
value congruence `expJet5Val_congr` (mirrors `expJet4Rhs_*` / `expJet4Val_congr` one order up).

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


theorem expJet5Rhs_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (c : ℝ) (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s) (fun s => c • Qhr s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) (fun s => c • Qhlm s) (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm Qklr Qkmr Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) Qklmr (c • h) k l m r t
      = c • expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
  simp only [expJet5Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem expJet5Rhs_add_h (g gi : Point n → Fin n → Fin n → ℝ)
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
    (h₁ h₂ k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s) (fun s => Qhm₁ s + Qhm₂ s) (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm Qkr Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm Qklr Qkmr Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) Qklmr (h₁ + h₂) k l m r t
      = expJet5Rhs g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qhr₁ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm₁ Qhlr₁ Qhmr₁ Qklm Qklr Qkmr Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr h₁ k l m r t
        + expJet5Rhs g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qhr₂ Qkl Qkm Qkr Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm₂ Qhlr₂ Qhmr₂ Qklm Qklr Qkmr Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr h₂ k l m r t := by
  simp only [expJet5Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

theorem expJet5Rhs_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (c : ℝ) (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm Qhr (fun s => c • Qkl s) (fun s => c • Qkm s) (fun s => c • Qkr s) Qlm Qlr Qmr (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhkr s) Qhlm Qhlr Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) (fun s => c • Qkmr s) Qlmr (fun s => c • Qhklm s) (fun s => c • Qhklr s) (fun s => c • Qhkmr s) Qhlmr (fun s => c • Qklmr s) h (c • k) l m r t
      = c • expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
  simp only [expJet5Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem expJet5Rhs_add_k (g gi : Point n → Fin n → Fin n → ℝ)
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
    (h k₁ k₂ l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qkr₁ s + Qkr₂ s) Qlm Qlr Qmr (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm Qhlr Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) Qlmr (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) Qhlmr (fun s => Qklmr₁ s + Qklmr₂ s) h (k₁ + k₂) l m r t
      = expJet5Rhs g gi hC p v Φ Qhk₁ Qhl Qhm Qhr Qkl₁ Qkm₁ Qkr₁ Qlm Qlr Qmr Qhkl₁ Qhkm₁ Qhkr₁ Qhlm Qhlr Qhmr Qklm₁ Qklr₁ Qkmr₁ Qlmr Qhklm₁ Qhklr₁ Qhkmr₁ Qhlmr Qklmr₁ h k₁ l m r t
        + expJet5Rhs g gi hC p v Φ Qhk₂ Qhl Qhm Qhr Qkl₂ Qkm₂ Qkr₂ Qlm Qlr Qmr Qhkl₂ Qhkm₂ Qhkr₂ Qhlm Qhlr Qhmr Qklm₂ Qklr₂ Qkmr₂ Qlmr Qhklm₂ Qhklr₂ Qhkmr₂ Qhlmr Qklmr₂ h k₂ l m r t := by
  simp only [expJet5Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

theorem expJet5Rhs_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (c : ℝ) (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm Qhr (fun s => c • Qkl s) Qkm Qkr (fun s => c • Qlm s) (fun s => c • Qlr s) Qmr (fun s => c • Qhkl s) Qhkm Qhkr (fun s => c • Qhlm s) (fun s => c • Qhlr s) Qhmr (fun s => c • Qklm s) (fun s => c • Qklr s) Qkmr (fun s => c • Qlmr s) (fun s => c • Qhklm s) (fun s => c • Qhklr s) Qhkmr (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k (c • l) m r t
      = c • expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
  simp only [expJet5Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem expJet5Rhs_add_l (g gi : Point n → Fin n → Fin n → ℝ)
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
    (h k l₁ l₂ m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm Qhr (fun s => Qkl₁ s + Qkl₂ s) Qkm Qkr (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qlr₁ s + Qlr₂ s) Qmr (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qhlr₁ s + Qhlr₂ s) Qhmr (fun s => Qklm₁ s + Qklm₂ s) (fun s => Qklr₁ s + Qklr₂ s) Qkmr (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) (fun s => Qhklr₁ s + Qhklr₂ s) Qhkmr (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k (l₁ + l₂) m r t
      = expJet5Rhs g gi hC p v Φ Qhk Qhl₁ Qhm Qhr Qkl₁ Qkm Qkr Qlm₁ Qlr₁ Qmr Qhkl₁ Qhkm Qhkr Qhlm₁ Qhlr₁ Qhmr Qklm₁ Qklr₁ Qkmr Qlmr₁ Qhklm₁ Qhklr₁ Qhkmr Qhlmr₁ Qklmr₁ h k l₁ m r t
        + expJet5Rhs g gi hC p v Φ Qhk Qhl₂ Qhm Qhr Qkl₂ Qkm Qkr Qlm₂ Qlr₂ Qmr Qhkl₂ Qhkm Qhkr Qhlm₂ Qhlr₂ Qhmr Qklm₂ Qklr₂ Qkmr Qlmr₂ Qhklm₂ Qhklr₂ Qhkmr Qhlmr₂ Qklmr₂ h k l₂ m r t := by
  simp only [expJet5Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

theorem expJet5Rhs_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (c : ℝ) (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qhr Qkl (fun s => c • Qkm s) Qkr (fun s => c • Qlm s) Qlr (fun s => c • Qmr s) Qhkl (fun s => c • Qhkm s) Qhkr (fun s => c • Qhlm s) Qhlr (fun s => c • Qhmr s) (fun s => c • Qklm s) Qklr (fun s => c • Qkmr s) (fun s => c • Qlmr s) (fun s => c • Qhklm s) Qhklr (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k l (c • m) r t
      = c • expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
  simp only [expJet5Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem expJet5Rhs_add_m (g gi : Point n → Fin n → Fin n → ℝ)
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
    (h k l m₁ m₂ r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qhr Qkl (fun s => Qkm₁ s + Qkm₂ s) Qkr (fun s => Qlm₁ s + Qlm₂ s) Qlr (fun s => Qmr₁ s + Qmr₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) Qhkr (fun s => Qhlm₁ s + Qhlm₂ s) Qhlr (fun s => Qhmr₁ s + Qhmr₂ s) (fun s => Qklm₁ s + Qklm₂ s) Qklr (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) (fun s => Qhklm₁ s + Qhklm₂ s) Qhklr (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k l (m₁ + m₂) r t
      = expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm₁ Qhr Qkl Qkm₁ Qkr Qlm₁ Qlr Qmr₁ Qhkl Qhkm₁ Qhkr Qhlm₁ Qhlr Qhmr₁ Qklm₁ Qklr Qkmr₁ Qlmr₁ Qhklm₁ Qhklr Qhkmr₁ Qhlmr₁ Qklmr₁ h k l m₁ r t
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm₂ Qhr Qkl Qkm₂ Qkr Qlm₂ Qlr Qmr₂ Qhkl Qhkm₂ Qhkr Qhlm₂ Qhlr Qhmr₂ Qklm₂ Qklr Qkmr₂ Qlmr₂ Qhklm₂ Qhklr Qhkmr₂ Qhlmr₂ Qklmr₂ h k l m₂ r t := by
  simp only [expJet5Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

theorem expJet5Rhs_smul_r (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (c : ℝ) (h k l m r : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm (fun s => c • Qhr s) Qkl Qkm (fun s => c • Qkr s) Qlm (fun s => c • Qlr s) (fun s => c • Qmr s) Qhkl Qhkm (fun s => c • Qhkr s) Qhlm (fun s => c • Qhlr s) (fun s => c • Qhmr s) Qklm (fun s => c • Qklr s) (fun s => c • Qkmr s) (fun s => c • Qlmr s) Qhklm (fun s => c • Qhklr s) (fun s => c • Qhkmr s) (fun s => c • Qhlmr s) (fun s => c • Qklmr s) h k l m (c • r) t
      = c • expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
  simp only [expJet5Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem expJet5Rhs_add_r (g gi : Point n → Fin n → Fin n → ℝ)
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
    (h k l m r₁ r₂ : Point n) (t : ℝ) :
    expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm (fun s => Qhr₁ s + Qhr₂ s) Qkl Qkm (fun s => Qkr₁ s + Qkr₂ s) Qlm (fun s => Qlr₁ s + Qlr₂ s) (fun s => Qmr₁ s + Qmr₂ s) Qhkl Qhkm (fun s => Qhkr₁ s + Qhkr₂ s) Qhlm (fun s => Qhlr₁ s + Qhlr₂ s) (fun s => Qhmr₁ s + Qhmr₂ s) Qklm (fun s => Qklr₁ s + Qklr₂ s) (fun s => Qkmr₁ s + Qkmr₂ s) (fun s => Qlmr₁ s + Qlmr₂ s) Qhklm (fun s => Qhklr₁ s + Qhklr₂ s) (fun s => Qhkmr₁ s + Qhkmr₂ s) (fun s => Qhlmr₁ s + Qhlmr₂ s) (fun s => Qklmr₁ s + Qklmr₂ s) h k l m (r₁ + r₂) t
      = expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr₁ Qkl Qkm Qkr₁ Qlm Qlr₁ Qmr₁ Qhkl Qhkm Qhkr₁ Qhlm Qhlr₁ Qhmr₁ Qklm Qklr₁ Qkmr₁ Qlmr₁ Qhklm Qhklr₁ Qhkmr₁ Qhlmr₁ Qklmr₁ h k l m r₁ t
        + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr₂ Qkl Qkm Qkr₂ Qlm Qlr₂ Qmr₂ Qhkl Qhkm Qhkr₂ Qhlm Qhlr₂ Qhmr₂ Qklm Qklr₂ Qkmr₂ Qlmr₂ Qhklm Qhklr₂ Qhkmr₂ Qhlmr₂ Qklmr₂ h k l m r₂ t := by
  simp only [expJet5Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

theorem expJet5Val_congr (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qhr Qkl : ℝ → (Point n × Point n))
    (Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr : ℝ → (Point n × Point n))
    (Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr : ℝ → (Point n × Point n))
    (Qhk' Qhl' Qhm' Qhr' Qkl' : ℝ → (Point n × Point n))
    (Qkm' Qkr' Qlm' Qlr' Qmr' : ℝ → (Point n × Point n))
    (Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' : ℝ → (Point n × Point n))
    (Qhmr' Qklm' Qklr' Qkmr' Qlmr' : ℝ → (Point n × Point n))
    (Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' : ℝ → (Point n × Point n))
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
    (hQhk' : ContinuousOn Qhk' (Set.Icc (0 : ℝ) 1))
    (hQhl' : ContinuousOn Qhl' (Set.Icc (0 : ℝ) 1))
    (hQhm' : ContinuousOn Qhm' (Set.Icc (0 : ℝ) 1))
    (hQhr' : ContinuousOn Qhr' (Set.Icc (0 : ℝ) 1))
    (hQkl' : ContinuousOn Qkl' (Set.Icc (0 : ℝ) 1))
    (hQkm' : ContinuousOn Qkm' (Set.Icc (0 : ℝ) 1))
    (hQkr' : ContinuousOn Qkr' (Set.Icc (0 : ℝ) 1))
    (hQlm' : ContinuousOn Qlm' (Set.Icc (0 : ℝ) 1))
    (hQlr' : ContinuousOn Qlr' (Set.Icc (0 : ℝ) 1))
    (hQmr' : ContinuousOn Qmr' (Set.Icc (0 : ℝ) 1))
    (hQhkl' : ContinuousOn Qhkl' (Set.Icc (0 : ℝ) 1))
    (hQhkm' : ContinuousOn Qhkm' (Set.Icc (0 : ℝ) 1))
    (hQhkr' : ContinuousOn Qhkr' (Set.Icc (0 : ℝ) 1))
    (hQhlm' : ContinuousOn Qhlm' (Set.Icc (0 : ℝ) 1))
    (hQhlr' : ContinuousOn Qhlr' (Set.Icc (0 : ℝ) 1))
    (hQhmr' : ContinuousOn Qhmr' (Set.Icc (0 : ℝ) 1))
    (hQklm' : ContinuousOn Qklm' (Set.Icc (0 : ℝ) 1))
    (hQklr' : ContinuousOn Qklr' (Set.Icc (0 : ℝ) 1))
    (hQkmr' : ContinuousOn Qkmr' (Set.Icc (0 : ℝ) 1))
    (hQlmr' : ContinuousOn Qlmr' (Set.Icc (0 : ℝ) 1))
    (hQhklm' : ContinuousOn Qhklm' (Set.Icc (0 : ℝ) 1))
    (hQhklr' : ContinuousOn Qhklr' (Set.Icc (0 : ℝ) 1))
    (hQhkmr' : ContinuousOn Qhkmr' (Set.Icc (0 : ℝ) 1))
    (hQhlmr' : ContinuousOn Qhlmr' (Set.Icc (0 : ℝ) 1))
    (hQklmr' : ContinuousOn Qklmr' (Set.Icc (0 : ℝ) 1))
    (h k l m r : Point n)
    (ehk : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhk t = Qhk' t)
    (ehl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhl t = Qhl' t)
    (ehm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhm t = Qhm' t)
    (ehr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhr t = Qhr' t)
    (ekl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkl t = Qkl' t)
    (ekm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkm t = Qkm' t)
    (ekr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkr t = Qkr' t)
    (elm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qlm t = Qlm' t)
    (elr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qlr t = Qlr' t)
    (emr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qmr t = Qmr' t)
    (ehkl : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkl t = Qhkl' t)
    (ehkm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkm t = Qhkm' t)
    (ehkr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkr t = Qhkr' t)
    (ehlm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhlm t = Qhlm' t)
    (ehlr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhlr t = Qhlr' t)
    (ehmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhmr t = Qhmr' t)
    (eklm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qklm t = Qklm' t)
    (eklr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qklr t = Qklr' t)
    (ekmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qkmr t = Qkmr' t)
    (elmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qlmr t = Qlmr' t)
    (ehklm : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhklm t = Qhklm' t)
    (ehklr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhklr t = Qhklr' t)
    (ehkmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhkmr t = Qhkmr' t)
    (ehlmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qhlmr t = Qhlmr' t)
    (eklmr : ∀ t ∈ (Set.Icc (0 : ℝ) 1), Qklmr t = Qklmr' t) :
    expJet5Val g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r
      = expJet5Val g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' hv hΦcont hQhk' hQhl' hQhm' hQhr' hQkl' hQkm' hQkr' hQlm' hQlr' hQmr' hQhkl' hQhkm' hQhkr' hQhlm' hQhlr' hQhmr' hQklm' hQklr' hQkmr' hQlmr' hQhklm' hQhklr' hQhkmr' hQhlmr' hQklmr' h k l m r := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet5Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' hv hΦcont hQhk' hQhl' hQhm' hQhr' hQkl' hQkm' hQkr' hQlm' hQlr' hQmr' hQhkl' hQhkm' hQhkr' hQhlm' hQhlr' hQhmr' hQklm' hQklr' hQkmr' hQlmr' hQhklm' hQhklr' hQhkmr' hQhlmr' hQklmr' h k l m r).choose_spec
  have huniq := expJet5Fund_unique g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv h k l m r
    (expJet5Fund g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr hv hΦcont hQhk hQhl hQhm hQhr hQkl hQkm hQkr hQlm hQlr hQmr hQhkl hQhkm hQhkr hQhlm hQhlr hQhmr hQklm hQklr hQkmr hQlmr hQhklm hQhklr hQhkmr hQhlmr hQklmr h k l m r).choose
    (expJet5Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' hv hΦcont hQhk' hQhl' hQhm' hQhr' hQkl' hQkm' hQkr' hQlm' hQlr' hQmr' hQhkl' hQhkm' hQhkr' hQhlm' hQhlr' hQhmr' hQklm' hQklr' hQkmr' hQlmr' hQhklm' hQhklr' hQhkmr' hQhlmr' hQklmr' h k l m r).choose
    hR₁0 hR₂0 hR₁deriv
    (fun t ht => by
      have he : (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' hv hΦcont hQhk' hQhl' hQhm' hQhr' hQkl' hQkm' hQkr' hQlm' hQlr' hQmr' hQhkl' hQhkm' hQhkr' hQhlm' hQhlr' hQhmr' hQklm' hQklr' hQkmr' hQlmr' hQhklm' hQhklr' hQhkmr' hQhlmr' hQklmr' h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' h k l m r t
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet5Fund g gi hC p v Φ Qhk' Qhl' Qhm' Qhr' Qkl' Qkm' Qkr' Qlm' Qlr' Qmr' Qhkl' Qhkm' Qhkr' Qhlm' Qhlr' Qhmr' Qklm' Qklr' Qkmr' Qlmr' Qhklm' Qhklr' Qhkmr' Qhlmr' Qklmr' hv hΦcont hQhk' hQhl' hQhm' hQhr' hQkl' hQkm' hQkr' hQlm' hQlr' hQmr' hQhkl' hQhkm' hQhkr' hQhlm' hQhlr' hQhmr' hQklm' hQklr' hQkmr' hQlmr' hQhklm' hQhklr' hQhkmr' hQhlmr' hQklmr' h k l m r).choose t)
            + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t := by
        congr 1
        rw [expJet5Rhs_apply, expJet5Rhs_apply, ehk t ht, ehl t ht, ehm t ht, ehr t ht, ekl t ht, ekm t ht, ekr t ht, elm t ht, elr t ht, emr t ht, ehkl t ht, ehkm t ht, ehkr t ht, ehlm t ht, ehlr t ht, ehmr t ht, eklm t ht, eklr t ht, ekmr t ht, elmr t ht, ehklm t ht, ehklr t ht, ehkmr t ht, ehlmr t ht, eklmr t ht]
      rw [← he]; exact hR₂deriv t ht)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet5Val] using h1

end QIQTH.ExpMap
