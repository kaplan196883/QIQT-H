/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4D
import QIQTH.ExpJet4ValFull
import QIQTH.ExpMapContDiff3
import Mathlib

/-!
# JET-4 TOWER — the `expJetD4` packaging chain (J4-4b)

Faithful mirror, one Fréchet order up, of the jet-3 `expJetD3` packaging chain in
`ExpMapContDiff3.lean`.  Builds on the J4-4 foundation (`ExpJet4D.lean`: `expJet3Curve` + curve-level
trilinearity, `expJet4Val` + `expJet4Val_congr`) and the J4-3 value two-point estimate
(`ExpJet4ValFull.lean`: `expJet4Val_v_two_pt_diff`).

Chain landed here:
1. `expJet4Rhs_{add,smul}_{h,k,l,m}` — the eight matched-`Q` source-linearity lemmas.
2. `expJet3CurveG` (genuine third-variation curve, pair-slots := `expJet2Curve`) + its `continuousOn`
   and curve-level trilinearity; `expJet4Val_{add,smul}_{h,k,l,m}` (matched-`Q` value multilinearity);
   `expJet4ValG` (six `expJet2Curve` + four `expJet3CurveG` slots) + `expJet4ValG_norm_le` + its
   4-linearity.
3. `expJetD4Inner`/`expJetD4` — the packaged quadrilinear continuous map + `expJetD4_apply`.
4. `expJetD4_two_pt_diff` — the operator-norm two-point bound.

## Honest firewall (binding)
This does NOT establish `exp_p ∈ C⁴`, does NOT discharge `hfd3`, does NOT reach `κ = 1/6` or
`a₁ = R/6`.  It is the green, axiom-free packaging brick J4-4b.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ### (1) The eight matched-`Q` source-linearity lemmas for `expJet4Rhs`

`expJet4Rhs` is 4-linear in `(h,k,l,m)` jointly with its ten second/third-variation inputs, but ONLY
when each direction varies together with exactly the `Q··`/`Q···` slots that name it.  Since the
fourth mixed variation partitions `{h,k,l,m}`, EVERY one of the fourteen source terms carries each
direction exactly once, so each direction's scale/split threads through all fourteen terms.  Mirror of
`expJet3Rhs_{add,smul}_{h,k,l}` one order up. -/

/-- **Source `ℝ`-homogeneity in the `h`-slot.**  Scaling `h` (and the six `h`-carrying inputs
    `Qhk,Qhl,Qhm,Qhkl,Qhkm,Qhlm`) by `c` scales `Θ₄` by `c`. -/
theorem expJet4Rhs_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (c : ℝ) (h k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s)
        Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm
        (c • h) k l m t
      = c • expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
  simp only [expJet4Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `h`-slot.** -/
theorem expJet4Rhs_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl₁ Qhl₂ Qhm₁ Qhm₂ Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ Qklm : ℝ → (Point n × Point n))
    (h₁ h₂ k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
        (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
        (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm (h₁ + h₂) k l m t
      = expJet4Rhs g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm h₁ k l m t
        + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm h₂ k l m t := by
  simp only [expJet4Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-- **Source `ℝ`-homogeneity in the `k`-slot.** -/
theorem expJet4Rhs_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (c : ℝ) (h k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s)
        Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) h (c • k) l m t
      = c • expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
  simp only [expJet4Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `k`-slot.** -/
theorem expJet4Rhs_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl Qhm Qkl₁ Qkl₂ Qkm₁ Qkm₂ Qlm : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm₁ Qhkm₂ Qhlm Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (h k₁ k₂ l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s)
        (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
        Qhlm (fun s => Qklm₁ s + Qklm₂ s) h (k₁ + k₂) l m t
      = expJet4Rhs g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ h k₁ l m t
        + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ h k₂ l m t := by
  simp only [expJet4Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-- **Source `ℝ`-homogeneity in the `l`-slot.** -/
theorem expJet4Rhs_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (c : ℝ) (h k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm
        (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s)
        h k (c • l) m t
      = c • expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
  simp only [expJet4Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `l`-slot.** -/
theorem expJet4Rhs_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl₁ Qhl₂ Qhm Qkl₁ Qkl₂ Qkm Qlm₁ Qlm₂ : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm Qhlm₁ Qhlm₂ Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (h k l₁ l₂ m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm
        (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s)
        (fun s => Qklm₁ s + Qklm₂ s) h k (l₁ + l₂) m t
      = expJet4Rhs g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ h k l₁ m t
        + expJet4Rhs g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ h k l₂ m t := by
  simp only [expJet4Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-- **Source `ℝ`-homogeneity in the `m`-slot.** -/
theorem expJet4Rhs_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (c : ℝ) (h k l m : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
        (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s)
        h k l (c • m) t
      = c • expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t := by
  simp only [expJet4Rhs_apply, map_smul, ContinuousLinearMap.smul_apply, smul_add]

/-- **Source additivity in the `m`-slot.** -/
theorem expJet4Rhs_add_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm₁ Qhm₂ Qkl Qkm₁ Qkm₂ Qlm₁ Qlm₂ : ℝ → (Point n × Point n))
    (Qhkl Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (h k l m₁ m₂ : Point n) (t : ℝ) :
    expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s)
        (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s)
        (fun s => Qklm₁ s + Qklm₂ s) h k l (m₁ + m₂) t
      = expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ h k l m₁ t
        + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ h k l m₂ t := by
  simp only [expJet4Rhs_apply, map_add, ContinuousLinearMap.add_apply]; abel

/-! ### (2a) The matched-`Q` value multilinearity of `expJet4Val`

`R^{hklm}(1)` is 4-linear in `(h,k,l,m)` jointly with the carrying `Q··`/`Q···` inputs.  Mirror of
`expJet3Val_{add,smul}_{h,k,l}` one order up, via the `expJet4Rhs_{add,smul}_*` source-linearity
lemmas + `expJet4Fund_unique`. -/

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hklm}(1)` in the `h`-slot.** -/
theorem expJet4Val_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4Val g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s)
        Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont
        (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm
        (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m
      = c • expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
        hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s)
      Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont
      (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm
      (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s)
    (fun s => c • Qhm s) Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s)
    Qklm hv (c • h) k l m
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s)
      Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm hv hΦcont
      (hQhk.const_smul c) (hQhl.const_smul c) (hQhm.const_smul c) hQkl hQkm hQlm
      (hQhkl.const_smul c) (hQhkm.const_smul c) (hQhlm.const_smul c) hQklm (c • h) k l m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) (fun s => c • Qhl s) (fun s => c • Qhm s)
                Qkl Qkm Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) (fun s => c • Qhlm s) Qklm
                (c • h) k l m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_h]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` additivity of `R^{hklm}(1)` in the `h`-slot.** -/
theorem expJet4Val_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl₁ Qhl₂ Qhm₁ Qhm₂ Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl₁ : ContinuousOn Qhl₁ (Set.Icc (0 : ℝ) 1)) (hQhl₂ : ContinuousOn Qhl₂ (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1)) (h₁ h₂ k l m : Point n) :
    expJet4Val g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
        (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
        (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont
        (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm
        (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m
      = expJet4Val g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont
          hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m
        + expJet4Val g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont
          hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont
      hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont
      hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
      (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
      (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont
      (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm
      (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
    (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
    (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv (h₁ + h₂) k l m
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
      (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
      (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm hv hΦcont
      (hQhk₁.add hQhk₂) (hQhl₁.add hQhl₂) (hQhm₁.add hQhm₂) hQkl hQkm hQlm
      (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) hQklm (h₁ + h₂) k l m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont
        hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont
        hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont
                hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm h₁ k l m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv hΦcont
                hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm h₂ k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl₁ Qhm₁ Qkl Qkm Qlm Qhkl₁ Qhkm₁ Qhlm₁ Qklm hv hΦcont
                  hQhk₁ hQhl₁ hQhm₁ hQkl hQkm hQlm hQhkl₁ hQhkm₁ hQhlm₁ hQklm h₁ k l m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl₂ Qhm₂ Qkl Qkm Qlm Qhkl₂ Qhkm₂ Qhlm₂ Qklm hv
                  hΦcont hQhk₂ hQhl₂ hQhm₂ hQkl hQkm hQlm hQhkl₂ hQhkm₂ hQhlm₂ hQklm h₂ k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) (fun s => Qhl₁ s + Qhl₂ s)
                (fun s => Qhm₁ s + Qhm₂ s) Qkl Qkm Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
                (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s) Qklm (h₁ + h₂) k l m t := by
        rw [map_add, expJet4Rhs_add_h]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hklm}(1)` in the `k`-slot.** -/
theorem expJet4Val_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4Val g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s)
        Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont
        (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm
        (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m
      = c • expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
        hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s)
      Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont
      (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm
      (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s)
    (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s)
    hv h (c • k) l m
    (expJet4Fund g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s) (fun s => c • Qkm s)
      Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm (fun s => c • Qklm s) hv hΦcont
      (hQhk.const_smul c) hQhl hQhm (hQkl.const_smul c) (hQkm.const_smul c) hQlm
      (hQhkl.const_smul c) (hQhkm.const_smul c) hQhlm (hQklm.const_smul c) h (c • k) l m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => c • Qhk s) Qhl Qhm (fun s => c • Qkl s)
                (fun s => c • Qkm s) Qlm (fun s => c • Qhkl s) (fun s => c • Qhkm s) Qhlm
                (fun s => c • Qklm s) h (c • k) l m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_k]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` additivity of `R^{hklm}(1)` in the `k`-slot.** -/
theorem expJet4Val_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk₁ Qhk₂ Qhl Qhm Qkl₁ Qkl₂ Qkm₁ Qkm₂ Qlm : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm₁ Qhkm₂ Qhlm Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk₁ : ContinuousOn Qhk₁ (Set.Icc (0 : ℝ) 1)) (hQhk₂ : ContinuousOn Qhk₂ (Set.Icc (0 : ℝ) 1))
    (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1)) (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1))
    (hQkl₁ : ContinuousOn Qkl₁ (Set.Icc (0 : ℝ) 1)) (hQkl₂ : ContinuousOn Qkl₂ (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl₁ : ContinuousOn Qhkl₁ (Set.Icc (0 : ℝ) 1)) (hQhkl₂ : ContinuousOn Qhkl₂ (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l m : Point n) :
    expJet4Val g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s)
        (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
        Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont
        (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm
        (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m
      = expJet4Val g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont
          hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m
        + expJet4Val g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont
          hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont
      hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont
      hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s)
      (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
      Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont
      (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm
      (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm
    (fun s => Qkl₁ s + Qkl₂ s) (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s)
    (fun s => Qhkm₁ s + Qhkm₂ s) Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv h (k₁ + k₂) l m
    (expJet4Fund g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s)
      (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
      Qhlm (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont
      (hQhk₁.add hQhk₂) hQhl hQhm (hQkl₁.add hQkl₂) (hQkm₁.add hQkm₂) hQlm
      (hQhkl₁.add hQhkl₂) (hQhkm₁.add hQhkm₂) hQhlm (hQklm₁.add hQklm₂) h (k₁ + k₂) l m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont
        hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont
        hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont
                hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ h k₁ l m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv hΦcont
                hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ h k₂ l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk₁ Qhl Qhm Qkl₁ Qkm₁ Qlm Qhkl₁ Qhkm₁ Qhlm Qklm₁ hv hΦcont
                  hQhk₁ hQhl hQhm hQkl₁ hQkm₁ hQlm hQhkl₁ hQhkm₁ hQhlm hQklm₁ h k₁ l m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk₂ Qhl Qhm Qkl₂ Qkm₂ Qlm Qhkl₂ Qhkm₂ Qhlm Qklm₂ hv
                  hΦcont hQhk₂ hQhl hQhm hQkl₂ hQkm₂ hQlm hQhkl₂ hQhkm₂ hQhlm hQklm₂ h k₂ l m).choose t)
            + expJet4Rhs g gi hC p v Φ (fun s => Qhk₁ s + Qhk₂ s) Qhl Qhm (fun s => Qkl₁ s + Qkl₂ s)
                (fun s => Qkm₁ s + Qkm₂ s) Qlm (fun s => Qhkl₁ s + Qhkl₂ s) (fun s => Qhkm₁ s + Qhkm₂ s)
                Qhlm (fun s => Qklm₁ s + Qklm₂ s) h (k₁ + k₂) l m t := by
        rw [map_add, expJet4Rhs_add_k]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hklm}(1)` in the `l`-slot.** -/
theorem expJet4Val_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4Val g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm
        (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s)
        hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c)
        (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m
      = c • expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
        hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm
      (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s)
      hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c)
      (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s)
    Qkm (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s)
    hv h k (c • l) m
    (expJet4Fund g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm
      (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s) (fun s => c • Qklm s)
      hv hΦcont hQhk (hQhl.const_smul c) hQhm (hQkl.const_smul c) hQkm (hQlm.const_smul c)
      (hQhkl.const_smul c) hQhkm (hQhlm.const_smul c) (hQklm.const_smul c) h k (c • l) m).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk (fun s => c • Qhl s) Qhm (fun s => c • Qkl s) Qkm
                (fun s => c • Qlm s) (fun s => c • Qhkl s) Qhkm (fun s => c • Qhlm s)
                (fun s => c • Qklm s) h k (c • l) m t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_l]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` additivity of `R^{hklm}(1)` in the `l`-slot.** -/
theorem expJet4Val_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl₁ Qhl₂ Qhm Qkl₁ Qkl₂ Qkm Qlm₁ Qlm₂ : ℝ → (Point n × Point n))
    (Qhkl₁ Qhkl₂ Qhkm Qhlm₁ Qhlm₂ Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
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
    (h k l₁ l₂ m : Point n) :
    expJet4Val g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm
        (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s)
        (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm
        (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
        h k (l₁ + l₂) m
      = expJet4Val g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont
          hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m
        + expJet4Val g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont
          hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont
      hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont
      hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm
      (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s)
      (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm
      (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
      h k (l₁ + l₂) m).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm
    (fun s => Qkl₁ s + Qkl₂ s) Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm
    (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv h k (l₁ + l₂) m
    (expJet4Fund g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s) Qkm
      (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm (fun s => Qhlm₁ s + Qhlm₂ s)
      (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk (hQhl₁.add hQhl₂) hQhm (hQkl₁.add hQkl₂) hQkm
      (hQlm₁.add hQlm₂) (hQhkl₁.add hQhkl₂) hQhkm (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
      h k (l₁ + l₂) m).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont
        hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t
      + (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont
        hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont
                hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ h k l₁ m t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv hΦcont
                hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ h k l₂ m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl₁ Qhm Qkl₁ Qkm Qlm₁ Qhkl₁ Qhkm Qhlm₁ Qklm₁ hv hΦcont
                  hQhk hQhl₁ hQhm hQkl₁ hQkm hQlm₁ hQhkl₁ hQhkm hQhlm₁ hQklm₁ h k l₁ m).choose t
                + (expJet4Fund g gi hC p v Φ Qhk Qhl₂ Qhm Qkl₂ Qkm Qlm₂ Qhkl₂ Qhkm Qhlm₂ Qklm₂ hv
                  hΦcont hQhk hQhl₂ hQhm hQkl₂ hQkm hQlm₂ hQhkl₂ hQhkm hQhlm₂ hQklm₂ h k l₂ m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk (fun s => Qhl₁ s + Qhl₂ s) Qhm (fun s => Qkl₁ s + Qkl₂ s)
                Qkm (fun s => Qlm₁ s + Qlm₂ s) (fun s => Qhkl₁ s + Qhkl₂ s) Qhkm
                (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) h k (l₁ + l₂) m t := by
        rw [map_add, expJet4Rhs_add_l]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` `ℝ`-homogeneity of `R^{hklm}(1)` in the `m`-slot.** -/
theorem expJet4Val_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm : ContinuousOn Qhm (Set.Icc (0 : ℝ) 1)) (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm : ContinuousOn Qkm (Set.Icc (0 : ℝ) 1)) (hQlm : ContinuousOn Qlm (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1)) (hQhkm : ContinuousOn Qhkm (Set.Icc (0 : ℝ) 1))
    (hQhlm : ContinuousOn Qhlm (Set.Icc (0 : ℝ) 1)) (hQklm : ContinuousOn Qklm (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4Val g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
        (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s)
        hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c)
        hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m)
      = c • expJet4Val g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
        hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose_spec
  obtain ⟨hRc0, -, -, hRcderiv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
      (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s)
      hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c)
      hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m)).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
    (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s)
    hv h k l (c • m)
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
      (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s) (fun s => c • Qklm s)
      hv hΦcont hQhk hQhl (hQhm.const_smul c) hQkl (hQkm.const_smul c) (hQlm.const_smul c)
      hQhkl (hQhkm.const_smul c) (hQhlm.const_smul c) (hQklm.const_smul c) h k l (c • m)).choose
    (fun t => c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
      hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
    hRc0 (by simp only [hR0, smul_zero]) hRcderiv
    (fun t ht => by
      have hd := (hRderiv t ht).const_smul c
      have hval :
          c • ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
                ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
              + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              (c • (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont
                  hQhk hQhl hQhm hQkl hQkm hQlm hQhkl hQhkm hQhlm hQklm h k l m).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => c • Qhm s) Qkl (fun s => c • Qkm s)
                (fun s => c • Qlm s) Qhkl (fun s => c • Qhkm s) (fun s => c • Qhlm s)
                (fun s => c • Qklm s) h k l (c • m) t := by
        rw [smul_add, map_smul, expJet4Rhs_smul_m]
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-- **Matched-`Q` additivity of `R^{hklm}(1)` in the `m`-slot.** -/
theorem expJet4Val_add_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qhk Qhl Qhm₁ Qhm₂ Qkl Qkm₁ Qkm₂ Qlm₁ Qlm₂ : ℝ → (Point n × Point n))
    (Qhkl Qhkm₁ Qhkm₂ Qhlm₁ Qhlm₂ Qklm₁ Qklm₂ : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhm₁ : ContinuousOn Qhm₁ (Set.Icc (0 : ℝ) 1)) (hQhm₂ : ContinuousOn Qhm₂ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1))
    (hQkm₁ : ContinuousOn Qkm₁ (Set.Icc (0 : ℝ) 1)) (hQkm₂ : ContinuousOn Qkm₂ (Set.Icc (0 : ℝ) 1))
    (hQlm₁ : ContinuousOn Qlm₁ (Set.Icc (0 : ℝ) 1)) (hQlm₂ : ContinuousOn Qlm₂ (Set.Icc (0 : ℝ) 1))
    (hQhkl : ContinuousOn Qhkl (Set.Icc (0 : ℝ) 1))
    (hQhkm₁ : ContinuousOn Qhkm₁ (Set.Icc (0 : ℝ) 1)) (hQhkm₂ : ContinuousOn Qhkm₂ (Set.Icc (0 : ℝ) 1))
    (hQhlm₁ : ContinuousOn Qhlm₁ (Set.Icc (0 : ℝ) 1)) (hQhlm₂ : ContinuousOn Qhlm₂ (Set.Icc (0 : ℝ) 1))
    (hQklm₁ : ContinuousOn Qklm₁ (Set.Icc (0 : ℝ) 1)) (hQklm₂ : ContinuousOn Qklm₂ (Set.Icc (0 : ℝ) 1))
    (h k l m₁ m₂ : Point n) :
    expJet4Val g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s)
        (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s)
        (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂)
        (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
        h k l (m₁ + m₂)
      = expJet4Val g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont
          hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁
        + expJet4Val g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont
          hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂ := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont
      hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont
      hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose_spec
  obtain ⟨hR₃0, -, -, hR₃deriv⟩ :=
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s)
      (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s)
      (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂)
      (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
      h k l (m₁ + m₂)).choose_spec
  have huniq := expJet4Fund_unique g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl
    (fun s => Qkm₁ s + Qkm₂ s) (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s)
    (fun s => Qhlm₁ s + Qhlm₂ s) (fun s => Qklm₁ s + Qklm₂ s) hv h k l (m₁ + m₂)
    (expJet4Fund g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s)
      (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s)
      (fun s => Qklm₁ s + Qklm₂ s) hv hΦcont hQhk hQhl (hQhm₁.add hQhm₂) hQkl (hQkm₁.add hQkm₂)
      (hQlm₁.add hQlm₂) hQhkl (hQhkm₁.add hQhkm₂) (hQhlm₁.add hQhlm₂) (hQklm₁.add hQklm₂)
      h k l (m₁ + m₂)).choose
    (fun t => (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont
        hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t
      + (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont
        hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
    hR₃0 (by simp only [hR₁0, hR₂0, add_zero]) hR₃deriv
    (fun t ht => by
      have hd := (hR₁deriv t ht).add (hR₂deriv t ht)
      have hval :
          ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont
                hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ h k l m₁ t)
          + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv hΦcont
                hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ h k l m₂ t)
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₁ Qkl Qkm₁ Qlm₁ Qhkl Qhkm₁ Qhlm₁ Qklm₁ hv hΦcont
                  hQhk hQhl hQhm₁ hQkl hQkm₁ hQlm₁ hQhkl hQhkm₁ hQhlm₁ hQklm₁ h k l m₁).choose t
                + (expJet4Fund g gi hC p v Φ Qhk Qhl Qhm₂ Qkl Qkm₂ Qlm₂ Qhkl Qhkm₂ Qhlm₂ Qklm₂ hv
                  hΦcont hQhk hQhl hQhm₂ hQkl hQkm₂ hQlm₂ hQhkl hQhkm₂ hQhlm₂ hQklm₂ h k l m₂).choose t)
            + expJet4Rhs g gi hC p v Φ Qhk Qhl (fun s => Qhm₁ s + Qhm₂ s) Qkl (fun s => Qkm₁ s + Qkm₂ s)
                (fun s => Qlm₁ s + Qlm₂ s) Qhkl (fun s => Qhkm₁ s + Qhkm₂ s) (fun s => Qhlm₁ s + Qhlm₂ s)
                (fun s => Qklm₁ s + Qklm₂ s) h k l (m₁ + m₂) t := by
        rw [map_add, expJet4Rhs_add_m]; abel
      rwa [hval] at hd)
  have h1 := huniq 1 (by norm_num [Set.mem_Icc])
  simpa only [expJet4Val] using h1

/-! ### (2b) The genuine third-variation curve `expJet3CurveG` and its curve-level trilinearity

`expJet3CurveG` = `expJet3Curve` with the three pair-`Q··` slots instantiated by the genuine
second-variation curves `expJet2Curve`; this is plain-trilinear in `(h,k,l)` at every `t ∈ [0,1]`
(the four triple-slot feeders of `expJet4ValG`).  Mirror of `expJet3ValG` + its trilinearity at
curve level, using `expJet3Curve_{add,smul}_*` (`ExpJet4D.lean`) and `expJet2Curve_{add,smul}_*`
bridged through the curve `Q`-congruence `expJet3Curve_congr`. -/

/-- **Curve `Q`-congruence of `R^{hkl}`.**  If the pair inputs `Qkl,Qhl,Qhk` agree on `[0,1]` with
    their primes, `expJet3Curve` is unchanged on `[0,1]` (`expJet3Fund_unique`).  The ∀`t`-upgrade of
    `expJet3Val_congr`. -/
theorem expJet3Curve_congr (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qkl Qhl Qhk Qkl' Qhl' Qhk' : ℝ → (Point n × Point n))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hQkl : ContinuousOn Qkl (Set.Icc (0 : ℝ) 1)) (hQhl : ContinuousOn Qhl (Set.Icc (0 : ℝ) 1))
    (hQhk : ContinuousOn Qhk (Set.Icc (0 : ℝ) 1))
    (hQkl' : ContinuousOn Qkl' (Set.Icc (0 : ℝ) 1)) (hQhl' : ContinuousOn Qhl' (Set.Icc (0 : ℝ) 1))
    (hQhk' : ContinuousOn Qhk' (Set.Icc (0 : ℝ) 1)) (h k l : Point n)
    (eKl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qkl t = Qkl' t)
    (eHl : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhl t = Qhl' t)
    (eHk : ∀ t ∈ Set.Icc (0 : ℝ) 1, Qhk t = Qhk' t) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l t
      = expJet3Curve g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l t := by
  obtain ⟨hR₁0, -, -, hR₁deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose_spec
  obtain ⟨hR₂0, -, -, hR₂deriv⟩ :=
    (expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose_spec
  have huniq := expJet3Fund_unique g gi hC p v Φ Qkl Qhl Qhk hv h k l
    (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont hQkl hQhl hQhk h k l).choose
    (expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose
    hR₁0 hR₂0 hR₁deriv
    (fun t ht => by
      have he : (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl' Qhl' Qhk' h k l t
          = (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
              ((expJet3Fund g gi hC p v Φ Qkl' Qhl' Qhk' hv hΦcont hQkl' hQhl' hQhk' h k l).choose t)
            + expJet3Rhs g gi hC p v Φ Qkl Qhl Qhk h k l t := by
        congr 1
        rw [expJet3Rhs_apply, expJet3Rhs_apply, eKl t ht, eHl t ht, eHk t ht]
      rw [← he]; exact hR₂deriv t ht)
  intro t ht
  simpa only [expJet3Curve] using huniq t ht

/-- The **genuine third-variation curve** `t ↦ R^{hkl}_v(t)` with the pair-`Q··` slots instantiated by
    the genuine second-variation curves `expJet2Curve k l`, `expJet2Curve h l`, `expJet2Curve h k`. -/
noncomputable def expJet3CurveG (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l : Point n) : ℝ → (Point n × Point n) :=
  expJet3Curve g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    h k l

/-- `expJet3CurveG` is continuous on `[0,1]`. -/
theorem expJet3CurveG_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (h k l : Point n) :
    ContinuousOn (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (Set.Icc (0 : ℝ) 1) :=
  expJet3Curve_continuousOn g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l

/-- **Curve-level additivity of `expJet3CurveG` in the `l`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l₁ l₂ : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont h k (l₁ + l₂) t
      = expJet3CurveG g gi hC p v Φ hv hΦcont h k l₁ t
        + expJet3CurveG g gi hC p v Φ hv hΦcont h k l₂ t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k (l₁ + l₂))
      (expJet2Curve g gi hC p v Φ hv hΦcont h (l₁ + l₂))
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k l₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont k l₂ s)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h l₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont h l₂ s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (l₁ + l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (l₁ + l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      h k (l₁ + l₂)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont k l₁ l₂)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h l₁ l₂)
      (fun _ _ => rfl) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_add_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l₁) (expJet2Curve g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l₁) (expJet2Curve g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l₁ l₂ t ht

/-- **Curve-level `ℝ`-homogeneity of `expJet3CurveG` in the `l`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont h k (c • l) t
      = c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k (c • l))
      (expJet2Curve g gi hC p v Φ hv hΦcont h (c • l))
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (c • l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      h k (c • l)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c k l)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h l)
      (fun _ _ => rfl) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_smul_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l t ht

/-- **Curve-level additivity of `expJet3CurveG` in the `h`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont (h₁ + h₂) k l t
      = expJet3CurveG g gi hC p v Φ hv hΦcont h₁ k l t
        + expJet3CurveG g gi hC p v Φ hv hΦcont h₂ k l t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ l s
        + expJet2Curve g gi hC p v Φ hv hΦcont h₂ l s)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ k s
        + expJet2Curve g gi hC p v Φ hv hΦcont h₂ k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k))
      (h₁ + h₂) k l
      (fun _ _ => rfl)
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ l)
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ k) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_add_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ k) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ k)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k) h₁ h₂ k l t ht

/-- **Curve-level `ℝ`-homogeneity of `expJet3CurveG` in the `h`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont (c • h) k l t
      = c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) k)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
      (c • h) k l
      (fun _ _ => rfl)
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h l)
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h k) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_smul_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l t ht

/-- **Curve-level additivity of `expJet3CurveG` in the `k`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont h (k₁ + k₂) l t
      = expJet3CurveG g gi hC p v Φ hv hΦcont h k₁ l t
        + expJet3CurveG g gi hC p v Φ hv hΦcont h k₂ l t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h (k₁ + k₂))
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k₁ l s
        + expJet2Curve g gi hC p v Φ hv hΦcont k₂ l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h k₁ s
        + expJet2Curve g gi hC p v Φ hv hΦcont h k₂ s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (k₁ + k₂))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l))
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁).add
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂))
      h (k₁ + k₂) l
      (expJet2Curve_add_left g gi hC p v Φ hv hΦcont k₁ k₂ l)
      (fun _ _ => rfl)
      (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h k₁ k₂) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_add_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k₁) (expJet2Curve g gi hC p v Φ hv hΦcont h k₂)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂) h k₁ k₂ l t ht

/-- **Curve-level `ℝ`-homogeneity of `expJet3CurveG` in the `k`-slot, on `[0,1]`.** -/
theorem expJet3CurveG_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l : Point n) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    expJet3CurveG g gi hC p v Φ hv hΦcont h (c • k) l t
      = c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l t := by
  intro t ht
  have hbridge := expJet3Curve_congr g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont (c • k) l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h (c • k))
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • k) l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • k))
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
      h (c • k) l
      (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c k l)
      (fun _ _ => rfl)
      (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h k) t ht
  simp only [expJet3CurveG]
  rw [hbridge]
  exact expJet3Curve_smul_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) c h k l t ht

/-! ### (2c) The genuine fourth-variation value `expJet4ValG`, its uniform bound and 4-linearity -/

/-- **`D⁴F` is uniformly tube-bounded on `[0,1]`.**  Mirror of `expJet_fderiv3_tube_bddAbove_unif` one
    order up: `q ↦ ‖D⁴F q‖` is continuous (`contDiff_fderiv3_geodesicField.continuous_fderiv`), the
    confined tube ball is compact, so a single `Kstar4` dominates `‖D⁴F(Y_v t)‖` for all admissible
    `v` and `t ∈ [0,1]`. -/
theorem expJet_fderiv4_tube_bddAbove_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧ ∀ v : Point n, ‖v‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  have hdFcont :
      Continuous (fun q => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) q‖) :=
    ((contDiff_fderiv3_geodesicField g gi hC).continuous_fderiv (by simp)).norm
  obtain ⟨C, hC'⟩ :=
    (isCompact_closedBall ((p, 0) : Point n × Point n) Rb).exists_bound_of_continuousOn
      hdFcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v hv t ht => ?_⟩
  have hmem : expTube g gi hC p v t ∈ Metric.closedBall ((p, 0) : Point n × Point n) Rb := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    obtain ⟨_, _, hconf⟩ := expTube_spec g gi hC p v hv
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconf t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  have hbnd := hC' _ hmem
  calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
      ≤ C := le_trans (le_abs_self _) (by simpa using hbnd)
    _ ≤ max C 0 := le_max_left _ _

/-- **The genuine fourth-variation value** `R^{hklm}_v(1)` with the six pair-`Q··` slots instantiated
    by `expJet2Curve` and the four triple-`Q···` slots by `expJet3CurveG`.  Plain 4-linear in
    `(h,k,l,m)` (below); the datum packaged into `expJetD4`. -/
noncomputable def expJet4ValG (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m : Point n) : Point n × Point n :=
  expJet4Val g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    h k l m

set_option maxHeartbeats 3200000 in
/-- **Uniform 4-linear value bound for `expJet4ValG`.**  A single `M ≥ 0` with
    `‖expJet4ValG h k l m‖ ≤ M·‖h‖·‖k‖·‖l‖·‖m‖` for all `(h,k,l,m)`, from the `[0,1]` tube bounds
    `Kstar/Kstar4/Kstar3/Kstar2`, the `Φ` compactness bound `Cphi`, the pair-curve bounds
    (`expJet2Fund_value_bound_Icc`) and the triple-curve bounds (`expJet3Fund_value_bound_Icc`) fed into
    the fourteen-term `expJet4Fund_value_bound`.  Mirror of `expJet3ValG_norm_le` one order up. -/
theorem expJet4ValG_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h k l m : Point n,
      ‖expJet4ValG g gi hC p v Φ hv hΦcont h k l m‖ ≤ M * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kstar4, hKstar40, hKstar4u⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hKstar3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hKstar2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  have hKstar4 := hKstar4u v hv
  have hKstar3 := hKstar3u v hv
  have hKstar2 := hKstar2u v hv
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc).exists_bound_of_continuousOn hΦcont
  set Cphi : ℝ := max Cb 0 with hCphidef
  have hCphi0 : 0 ≤ Cphi := le_max_right _ _
  have hCphi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ Cphi :=
    fun t ht => (hCb t ht).trans (le_max_left _ _)
  refine ⟨(Kstar4 * Cphi ^ 4
      + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar))
      + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2)
      + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3
          + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar)))
      * Real.exp Kstar, by positivity, fun h k l m => ?_⟩
  -- pair-curve bounds on `[0,1]`
  have pb : ∀ a b : Point n,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet2Curve g gi hC p v Φ hv hΦcont a b t‖
        ≤ (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖b‖ := by
    intro a b
    obtain ⟨-, -, -, hderiv⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont a b).choose_spec
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ a b Kstar Kstar2 Cphi hKstar0 hKstar20 hCphi0
      hKstar hKstar2 hCphi (expJet2Curve g gi hC p v Φ hv hΦcont a b)
      ((expJet2Fund g gi hC p v Φ hv hΦcont a b).choose_spec).1 hderiv
  -- triple-curve bounds on `[0,1]`
  have tb : ∀ a b c : Point n,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖expJet3CurveG g gi hC p v Φ hv hΦcont a b c t‖
        ≤ ((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
            * Real.exp Kstar) * ‖a‖ * ‖b‖ * ‖c‖ := by
    intro a b c t ht
    obtain ⟨hR0, -, -, hRderiv⟩ :=
      (expJet3Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve g gi hC p v Φ hv hΦcont a b) hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont b c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a c)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont a b) a b c).choose_spec
    exact (expJet3Fund_value_bound_Icc g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont b c)
      (expJet2Curve g gi hC p v Φ hv hΦcont a c)
      (expJet2Curve g gi hC p v Φ hv hΦcont a b) a b c
      Kstar Kstar3 Kstar2 Cphi
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖b‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖c‖)
      ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖a‖ * ‖b‖)
      hKstar0 hKstar30 hKstar20 hCphi0 hKstar hKstar3 hKstar2 hCphi
      (pb b c) (pb a c) (pb a b)
      (expJet3CurveG g gi hC p v Φ hv hΦcont a b c) hR0 hRderiv t ht).trans (le_of_eq (by ring))
  obtain ⟨hRt0, -, -, hRtderiv⟩ :=
    (expJet4Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
      (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
      h k l m).choose_spec
  have hbd := expJet4Fund_value_bound g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    h k l m Kstar Kstar4 Kstar3 Kstar2 Cphi
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖k‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖h‖ * ‖m‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖l‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖k‖ * ‖m‖)
    ((Kstar2 * Cphi ^ 2 * Real.exp Kstar) * ‖l‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
        * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖l‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
        * Real.exp Kstar) * ‖h‖ * ‖k‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
        * Real.exp Kstar) * ‖h‖ * ‖l‖ * ‖m‖)
    (((Kstar3 * Cphi ^ 3 + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi))
        * Real.exp Kstar) * ‖k‖ * ‖l‖ * ‖m‖)
    hKstar0 hKstar40 hKstar30 hKstar20 hCphi0 hKstar hKstar4 hKstar3 hKstar2 hCphi
    (pb h k) (pb h l) (pb h m) (pb k l) (pb k m) (pb l m)
    (tb h k l) (tb h k m) (tb h l m) (tb k l m)
    _ hRt0 hRtderiv
  calc ‖expJet4ValG g gi hC p v Φ hv hΦcont h k l m‖
      ≤ _ := hbd
    _ = (Kstar4 * Cphi ^ 4
          + 6 * (Kstar3 * Cphi ^ 2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar))
          + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) ^ 2)
          + 4 * (Kstar2 * Cphi * ((Kstar3 * Cphi ^ 3
              + 3 * (Kstar2 * (Kstar2 * Cphi ^ 2 * Real.exp Kstar) * Cphi)) * Real.exp Kstar)))
          * Real.exp Kstar * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by ring

/-- **Additivity of `expJet4ValG` in the `h`-slot.** -/
theorem expJet4ValG_add_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h₁ h₂ k l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont (h₁ + h₂) k l m
      = expJet4ValG g gi hC p v Φ hv hΦcont h₁ k l m
        + expJet4ValG g gi hC p v Φ hv hΦcont h₂ k l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
    (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
    (expJet2Curve g gi hC p v Φ hv hΦcont (h₁ + h₂) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (h₁ + h₂) k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (h₁ + h₂) k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (h₁ + h₂) l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ k s
      + expJet2Curve g gi hC p v Φ hv hΦcont h₂ k s)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ l s
      + expJet2Curve g gi hC p v Φ hv hΦcont h₂ l s)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h₁ m s
      + expJet2Curve g gi hC p v Φ hv hΦcont h₂ m s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h₁ k l s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h₂ k l s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h₁ k m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h₂ k m s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h₁ l m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h₂ l m s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (h₁ + h₂) l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k))
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l))
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ m).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ m))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ k l).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ k l))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ k m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ k m))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ l m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ l m))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    (h₁ + h₂) k l m
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ k)
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ l)
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont h₁ h₂ m)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet3CurveG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ k l)
    (expJet3CurveG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ k m)
    (expJet3CurveG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ l m)
    (fun _ _ => rfl)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_add_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ k) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h₁ m) (expJet2Curve g gi hC p v Φ hv hΦcont h₂ m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h₁ k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h₂ k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h₁ k m) (expJet3CurveG g gi hC p v Φ hv hΦcont h₂ k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h₁ l m) (expJet3CurveG g gi hC p v Φ hv hΦcont h₂ l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₁ m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h₂ m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₁ l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h₂ l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m) h₁ h₂ k l m

/-- **ℝ-homogeneity of `expJet4ValG` in the `h`-slot.** -/
theorem expJet4ValG_smul_h (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont (c • h) k l m
      = c • expJet4ValG g gi hC p v Φ hv hΦcont h k l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) k)
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) l)
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • h) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (c • h) k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (c • h) k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (c • h) l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h m s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k m s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h l m s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • h) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (c • h) k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (c • h) k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (c • h) l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m).const_smul c)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m)
    (c • h) k l m
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h k)
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h l)
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c h m)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet3CurveG_smul_h g gi hC p v Φ hv hΦcont c h k l)
    (expJet3CurveG_smul_h g gi hC p v Φ hv hΦcont c h k m)
    (expJet3CurveG_smul_h g gi hC p v Φ hv hΦcont c h l m)
    (fun _ _ => rfl)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_smul_h g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m) c h k l m

/-- **Additivity of `expJet4ValG` in the `k`-slot.** -/
theorem expJet4ValG_add_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k₁ k₂ l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h (k₁ + k₂) l m
      = expJet4ValG g gi hC p v Φ hv hΦcont h k₁ l m
        + expJet4ValG g gi hC p v Φ hv hΦcont h k₂ l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h (k₁ + k₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
    (expJet2Curve g gi hC p v Φ hv hΦcont (k₁ + k₂) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (k₁ + k₂) l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (k₁ + k₂) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (k₁ + k₂) l m)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h k₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont h k₂ s)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k₁ l s
      + expJet2Curve g gi hC p v Φ hv hΦcont k₂ l s)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k₁ m s
      + expJet2Curve g gi hC p v Φ hv hΦcont k₂ m s)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h k₁ l s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h k₂ l s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h k₁ m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h k₂ m s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont k₁ l m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont k₂ l m s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (k₁ + k₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (k₁ + k₂) l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (k₁ + k₂) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (k₁ + k₂) l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (k₁ + k₂) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (k₁ + k₂) l m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l))
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ m).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ m))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₁ l).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₂ l))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₁ m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₂ m))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k₁ l m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k₂ l m))
    h (k₁ + k₂) l m
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h k₁ k₂)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont k₁ k₂ l)
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont k₁ k₂ m)
    (fun _ _ => rfl)
    (expJet3CurveG_add_k g gi hC p v Φ hv hΦcont h k₁ k₂ l)
    (expJet3CurveG_add_k g gi hC p v Φ hv hΦcont h k₁ k₂ m)
    (fun _ _ => rfl)
    (expJet3CurveG_add_h g gi hC p v Φ hv hΦcont k₁ k₂ l m)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_add_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k₁) (expJet2Curve g gi hC p v Φ hv hΦcont h k₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k₁ l) (expJet2Curve g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k₁ m) (expJet2Curve g gi hC p v Φ hv hΦcont k₂ m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k₁ l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k₂ l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k₁ m) (expJet3CurveG g gi hC p v Φ hv hΦcont h k₂ m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k₁ l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k₂ l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₁ m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k₂ m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₁ l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₂ l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₁ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k₂ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k₁ l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k₂ l m) h k₁ k₂ l m

/-- **ℝ-homogeneity of `expJet4ValG` in the `k`-slot.** -/
theorem expJet4ValG_smul_k (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h (c • k) l m
      = c • expJet4ValG g gi hC p v Φ hv hΦcont h k l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h (c • k))
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • k) l)
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • k) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (c • k) l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (c • k) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont (c • k) l m)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h k s)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k m s)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k m s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont k l m s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • k))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • k) l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • k) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (c • k) l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (c • k) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont (c • k) l m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m).const_smul c)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m).const_smul c)
    h (c • k) l m
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h k)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c k l)
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c k m)
    (fun _ _ => rfl)
    (expJet3CurveG_smul_k g gi hC p v Φ hv hΦcont c h k l)
    (expJet3CurveG_smul_k g gi hC p v Φ hv hΦcont c h k m)
    (fun _ _ => rfl)
    (expJet3CurveG_smul_h g gi hC p v Φ hv hΦcont c k l m)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_smul_k g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m) c h k l m

/-- **Additivity of `expJet4ValG` in the `l`-slot.** -/
theorem expJet4ValG_add_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l₁ l₂ m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h k (l₁ + l₂) m
      = expJet4ValG g gi hC p v Φ hv hΦcont h k l₁ m
        + expJet4ValG g gi hC p v Φ hv hΦcont h k l₂ m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h (l₁ + l₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k (l₁ + l₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont (l₁ + l₂) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k (l₁ + l₂))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (l₁ + l₂) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k (l₁ + l₂) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h l₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont h l₂ s)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k l₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont k l₂ s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont l₁ m s
      + expJet2Curve g gi hC p v Φ hv hΦcont l₂ m s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h k l₁ s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h k l₂ s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h l₁ m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h l₂ m s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont k l₁ m s
      + expJet3CurveG g gi hC p v Φ hv hΦcont k l₂ m s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (l₁ + l₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (l₁ + l₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (l₁ + l₂) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k (l₁ + l₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (l₁ + l₂) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k (l₁ + l₂) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l₁ m).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l₂ m))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l₁).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l₁ m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l₂ m))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l₁ m).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l₂ m))
    h k (l₁ + l₂) m
    (fun _ _ => rfl)
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h l₁ l₂)
    (fun _ _ => rfl)
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont k l₁ l₂)
    (fun _ _ => rfl)
    (expJet2Curve_add_left g gi hC p v Φ hv hΦcont l₁ l₂ m)
    (expJet3CurveG_add_l g gi hC p v Φ hv hΦcont h k l₁ l₂)
    (fun _ _ => rfl)
    (expJet3CurveG_add_k g gi hC p v Φ hv hΦcont h l₁ l₂ m)
    (expJet3CurveG_add_k g gi hC p v Φ hv hΦcont k l₁ l₂ m)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_add_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l₁) (expJet2Curve g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l₁) (expJet2Curve g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l₁ m) (expJet2Curve g gi hC p v Φ hv hΦcont l₂ m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l₁) (expJet3CurveG g gi hC p v Φ hv hΦcont h k l₂)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l₁ m) (expJet3CurveG g gi hC p v Φ hv hΦcont h l₂ m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l₁ m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l₂ m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l₁ m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l₂ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l₁)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l₂)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l₁ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l₂ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l₁ m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l₂ m) h k l₁ l₂ m

/-- **ℝ-homogeneity of `expJet4ValG` in the `l`-slot.** -/
theorem expJet4ValG_smul_l (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h k (c • l) m
      = c • expJet4ValG g gi hC p v Φ hv hΦcont h k l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h (c • l))
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k (c • l))
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont (c • l) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k (c • l))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h (c • l) m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k (c • l) m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h l s)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k l s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont l m s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k l s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h l m s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont k l m s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • l))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (c • l))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont (c • l) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k (c • l))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h (c • l) m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k (c • l) m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l).const_smul c)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m).const_smul c)
    h k (c • l) m
    (fun _ _ => rfl)
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h l)
    (fun _ _ => rfl)
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c k l)
    (fun _ _ => rfl)
    (expJet2Curve_smul_left g gi hC p v Φ hv hΦcont c l m)
    (expJet3CurveG_smul_l g gi hC p v Φ hv hΦcont c h k l)
    (fun _ _ => rfl)
    (expJet3CurveG_smul_k g gi hC p v Φ hv hΦcont c h l m)
    (expJet3CurveG_smul_k g gi hC p v Φ hv hΦcont c k l m)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_smul_l g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m) c h k l m

/-- **Additivity of `expJet4ValG` in the `m`-slot.** -/
theorem expJet4ValG_add_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l m₁ m₂ : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h k l (m₁ + m₂)
      = expJet4ValG g gi hC p v Φ hv hΦcont h k l m₁
        + expJet4ValG g gi hC p v Φ hv hΦcont h k l m₂ := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h (m₁ + m₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k (m₁ + m₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont l (m₁ + m₂))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k (m₁ + m₂))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l (m₁ + m₂))
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l (m₁ + m₂))
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont h m₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont h m₂ s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont k m₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont k m₂ s)
    (fun s => expJet2Curve g gi hC p v Φ hv hΦcont l m₁ s
      + expJet2Curve g gi hC p v Φ hv hΦcont l m₂ s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h k m₁ s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h k m₂ s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont h l m₁ s
      + expJet3CurveG g gi hC p v Φ hv hΦcont h l m₂ s)
    (fun s => expJet3CurveG g gi hC p v Φ hv hΦcont k l m₁ s
      + expJet3CurveG g gi hC p v Φ hv hΦcont k l m₂ s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (m₁ + m₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (m₁ + m₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l (m₁ + m₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k (m₁ + m₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l (m₁ + m₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l (m₁ + m₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m₂))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m₂))
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m₁).add
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m₂))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m₁).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m₂))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m₁).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m₂))
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m₁).add
      (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m₂))
    h k l (m₁ + m₂)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont h m₁ m₂)
    (fun _ _ => rfl)
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont k m₁ m₂)
    (expJet2Curve_add_right g gi hC p v Φ hv hΦcont l m₁ m₂)
    (fun _ _ => rfl)
    (expJet3CurveG_add_l g gi hC p v Φ hv hΦcont h k m₁ m₂)
    (expJet3CurveG_add_l g gi hC p v Φ hv hΦcont h l m₁ m₂)
    (expJet3CurveG_add_l g gi hC p v Φ hv hΦcont k l m₁ m₂)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_add_m g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m₁) (expJet2Curve g gi hC p v Φ hv hΦcont h m₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m₁) (expJet2Curve g gi hC p v Φ hv hΦcont k m₂)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m₁) (expJet2Curve g gi hC p v Φ hv hΦcont l m₂)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k m₁) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m₂)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m₁) (expJet3CurveG g gi hC p v Φ hv hΦcont h l m₂)
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l m₁) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m₂)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m₂)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m₁)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m₂)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m₁)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m₂)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m₁)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m₂)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m₁)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m₂) h k l m₁ m₂

/-- **ℝ-homogeneity of `expJet4ValG` in the `m`-slot.** -/
theorem expJet4ValG_smul_m (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (c : ℝ) (h k l m : Point n) :
    expJet4ValG g gi hC p v Φ hv hΦcont h k l (c • m)
      = c • expJet4ValG g gi hC p v Φ hv hΦcont h k l m := by
  have hbridge := expJet4Val_congr g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h (c • m))
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k (c • m))
    (expJet2Curve g gi hC p v Φ hv hΦcont l (c • m))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k (c • m))
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l (c • m))
    (expJet3CurveG g gi hC p v Φ hv hΦcont k l (c • m))
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont h m s)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont k m s)
    (fun s => c • expJet2Curve g gi hC p v Φ hv hΦcont l m s)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h k m s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont h l m s)
    (fun s => c • expJet3CurveG g gi hC p v Φ hv hΦcont k l m s)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h (c • m))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k (c • m))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l (c • m))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k (c • m))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l (c • m))
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l (c • m))
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m).const_smul c)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m).const_smul c)
    ((expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m).const_smul c)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m).const_smul c)
    ((expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m).const_smul c)
    h k l (c • m)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c h m)
    (fun _ _ => rfl)
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c k m)
    (expJet2Curve_smul_right g gi hC p v Φ hv hΦcont c l m)
    (fun _ _ => rfl)
    (expJet3CurveG_smul_l g gi hC p v Φ hv hΦcont c h k m)
    (expJet3CurveG_smul_l g gi hC p v Φ hv hΦcont c h l m)
    (expJet3CurveG_smul_l g gi hC p v Φ hv hΦcont c k l m)
  simp only [expJet4ValG]
  rw [hbridge]
  exact expJet4Val_smul_m g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h k l) (expJet3CurveG g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG g gi hC p v Φ hv hΦcont h l m) (expJet3CurveG g gi hC p v Φ hv hΦcont k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k l)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h k m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont h l m)
    (expJet3CurveG_continuousOn g gi hC p v Φ hv hΦcont k l m) c h k l m

/-! ### (3) The packaged quadrilinear continuous map `expJetD4`

Three nested `mkContinuous`/`mkContinuous₂` layers mirroring `expJetD3Inner`/`expJetD3` one order up:
`expJetD4Inner l m` is the inner `(k,h)`-bilinear slice, `expJetD4Mid m` wraps the `l`-slot, and
`expJetD4` wraps the `m`-slot, giving `expJetD4 m l k h = π(R^{hklm}_v(1))` (genuine curves). -/

/-- **The inner `(k,h)`-bilinear slice `D⁴_v(l,m)`.**  `π(R^{hklm}_v(1))` as a genuine continuous
    BILINEAR map in `(k,h)`, from the `k`/`h` linearity of `expJet4ValG` and the uniform bound
    `expJet4ValG_norm_le`, with bound constant `M·‖l‖·‖m‖`. -/
noncomputable def expJetD4Inner (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun k h => expJetPi (expJet4ValG g gi hC p v Φ hv hΦcont h k l m))
      (fun k₁ k₂ h => by
        simp only [expJet4ValG_add_k g gi hC p v Φ hv hΦcont h k₁ k₂ l m, map_add])
      (fun c k h => by
        simp only [expJet4ValG_smul_k g gi hC p v Φ hv hΦcont c h k l m, map_smul])
      (fun k h₁ h₂ => by
        simp only [expJet4ValG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ k l m, map_add])
      (fun c k h => by
        simp only [expJet4ValG_smul_h g gi hC p v Φ hv hΦcont c h k l m, map_smul]))
    ((expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖)
    (fun k h => by
      have hb := (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.2 h k l m
      simp only [LinearMap.mk₂_apply]
      calc ‖expJetPi (expJet4ValG g gi hC p v Φ hv hΦcont h k l m)‖
          ≤ ‖expJetPi (n := n)‖ * ‖expJet4ValG g gi hC p v Φ hv hΦcont h k l m‖ :=
            (expJetPi (n := n)).le_opNorm _
        _ ≤ 1 * ‖expJet4ValG g gi hC p v Φ hv hΦcont h k l m‖ :=
            mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
        _ = ‖expJet4ValG g gi hC p v Φ hv hΦcont h k l m‖ := one_mul _
        _ ≤ (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := hb
        _ = (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖ * ‖k‖ * ‖h‖ := by ring)

@[simp] theorem expJetD4Inner_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m k h : Point n) :
    expJetD4Inner g gi hC p v Φ hv hΦcont l m k h
      = expJetPi (expJet4ValG g gi hC p v Φ hv hΦcont h k l m) := rfl

/-- Operator-norm bound for the inner slice: `‖D⁴_v(l,m)‖ ≤ M·‖l‖·‖m‖`. -/
theorem expJetD4Inner_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m : Point n) :
    ‖expJetD4Inner g gi hC p v Φ hv hΦcont l m‖
      ≤ (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖ := by
  unfold expJetD4Inner
  exact LinearMap.mkContinuous₂_norm_le _
    (mul_nonneg (mul_nonneg (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1
      (norm_nonneg _)) (norm_nonneg _)) _

/-- **The `l`-wrapped trilinear slice `D⁴_v(m)`.** -/
noncomputable def expJetD4Mid (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun l => expJetD4Inner g gi hC p v Φ hv hΦcont l m
      map_add' := fun l₁ l₂ => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD4Inner_apply,
          expJet4ValG_add_l g gi hC p v Φ hv hΦcont h k l₁ l₂ m, map_add]
      map_smul' := fun c l => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD4Inner_apply,
          expJet4ValG_smul_l g gi hC p v Φ hv hΦcont c h k l m, map_smul] }
    ((expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖m‖)
    (fun l => (expJetD4Inner_norm_le g gi hC p v Φ hv hΦcont l m).trans (le_of_eq (by ring)))

@[simp] theorem expJetD4Mid_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m l k h : Point n) :
    expJetD4Mid g gi hC p v Φ hv hΦcont m l k h
      = expJetPi (expJet4ValG g gi hC p v Φ hv hΦcont h k l m) := by
  simp only [expJetD4Mid, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD4Inner_apply]

/-- Operator-norm bound for the `l`-wrapped slice: `‖D⁴_v(m)‖ ≤ M·‖m‖`. -/
theorem expJetD4Mid_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m : Point n) :
    ‖expJetD4Mid g gi hC p v Φ hv hΦcont m‖
      ≤ (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖m‖ := by
  unfold expJetD4Mid
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1 (norm_nonneg _)) _

/-- **(4-datum) The packaged fourth-derivative operator**
    `D⁴_v : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n`,
    `D⁴_v(m)(l)(k)(h) = π(R^{hklm}_v(1))` with the genuine second/third-variation curves in the
    `Q··`/`Q···` slots.  Mirror of `expJetD3` one Fréchet order up. -/
noncomputable def expJetD4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun m => expJetD4Mid g gi hC p v Φ hv hΦcont m
      map_add' := fun m₁ m₂ => by
        refine ContinuousLinearMap.ext fun l => ContinuousLinearMap.ext fun k =>
          ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD4Mid_apply,
          expJet4ValG_add_m g gi hC p v Φ hv hΦcont h k l m₁ m₂, map_add]
      map_smul' := fun c m => by
        refine ContinuousLinearMap.ext fun l => ContinuousLinearMap.ext fun k =>
          ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD4Mid_apply,
          expJet4ValG_smul_m g gi hC p v Φ hv hΦcont c h k l m, map_smul] }
    (expJet4ValG_norm_le g gi hC p v Φ hv hΦcont).choose
    (fun m => expJetD4Mid_norm_le g gi hC p v Φ hv hΦcont m)

/-- **`expJetD4` application form.**  `D⁴_v(m)(l)(k)(h) = π(R^{hklm}_v(1))` (genuine curves). -/
@[simp] theorem expJetD4_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m l k h : Point n) :
    expJetD4 g gi hC p v Φ hv hΦcont m l k h
      = expJetPi (expJet4ValG g gi hC p v Φ hv hΦcont h k l m) := by
  simp only [expJetD4, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD4Mid_apply]

/-! ### (4) The operator-norm two-point difference `expJetD4_two_pt_diff` -/

set_option maxHeartbeats 6400000 in
/-- **`expJetD4` is `v`-Lipschitz.**  `‖expJetD4_v − expJetD4_w‖ ≤ C·‖v−w‖` with
    `C = expJet4VtpConst …`, from the J4-3 value two-point Lipschitz bound
    `expJet4Val_v_two_pt_diff` projected by `π` and lifted through the four CLM layers by iterated
    `ContinuousLinearMap.opNorm_le_bound`.  Mirror of `expJetD3_two_pt_diff` one Fréchet order up. -/
theorem expJetD4_two_pt_diff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f Ld3f Ld4f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD3F : LipschitzOnWith Ld3f (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD4F : LipschitzOnWith Ld4f
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar2f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar2)
    (hKstar3f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p u t)‖ ≤ Kstar3)
    (hKstar4f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p u t)‖
        ≤ Kstar4)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1))
    (hΦwcont : ContinuousOn Φw (Set.Icc (0 : ℝ) 1)) :
    ‖expJetD4 g gi hC p v Φv hv hΦvcont - expJetD4 g gi hC p w Φw hw hΦwcont‖
      ≤ expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ)
          Kstar Kstar2 Kstar3 Kstar4 * ‖v - w‖ := by
  set C : ℝ := expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ)
    Kstar Kstar2 Kstar3 Kstar4 with hCdef
  have hC0 : 0 ≤ C :=
    expJet4VtpConst_nonneg _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 hKstar20 hKstar30 hKstar40
  have hval : ∀ m l k h : Point n,
      ‖expJetPi (expJet4ValG g gi hC p v Φv hv hΦvcont h k l m)
          - expJetPi (expJet4ValG g gi hC p w Φw hw hΦwcont h k l m)‖
        ≤ C * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
    intro m l k h
    obtain ⟨hQhkv0, -, -, hQhkvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h k).choose_spec
    obtain ⟨hQhlv0, -, -, hQhlvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h l).choose_spec
    obtain ⟨hQhmv0, -, -, hQhmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h m).choose_spec
    obtain ⟨hQklv0, -, -, hQklvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont k l).choose_spec
    obtain ⟨hQkmv0, -, -, hQkmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont k m).choose_spec
    obtain ⟨hQlmv0, -, -, hQlmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont l m).choose_spec
    obtain ⟨hQhkw0, -, -, hQhkwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h k).choose_spec
    obtain ⟨hQhlw0, -, -, hQhlwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h l).choose_spec
    obtain ⟨hQhmw0, -, -, hQhmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h m).choose_spec
    obtain ⟨hQklw0, -, -, hQklwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont k l).choose_spec
    obtain ⟨hQkmw0, -, -, hQkmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont k m).choose_spec
    obtain ⟨hQlmw0, -, -, hQlmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont l m).choose_spec
    obtain ⟨hQhklv0, -, -, hQhklvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h k)
        hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) h k l).choose_spec
    obtain ⟨hQhkmv0, -, -, hQhkmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k m)
        (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h k)
        hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) h k m).choose_spec
    obtain ⟨hQhlmv0, -, -, hQhlmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
        (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h l)
        hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) h l m).choose_spec
    obtain ⟨hQklmv0, -, -, hQklmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
        (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
        hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) k l m).choose_spec
    obtain ⟨hQhklw0, -, -, hQhklwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h k)
        hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) h k l).choose_spec
    obtain ⟨hQhkmw0, -, -, hQhkmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k m)
        (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h k)
        hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) h k m).choose_spec
    obtain ⟨hQhlmw0, -, -, hQhlmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
        (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h l)
        hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) h l m).choose_spec
    obtain ⟨hQklmw0, -, -, hQklmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
        (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
        hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) k l m).choose_spec
    obtain ⟨hRv0, -, -, hRvd⟩ :=
      (expJet4Fund g gi hC p v Φv
        (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l)
        (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) hv hΦvcont
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) h k l m).choose_spec
    obtain ⟨hRw0, -, -, hRwd⟩ :=
      (expJet4Fund g gi hC p w Φw
        (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l)
        (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) hw hΦwcont
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) h k l m).choose_spec
    have hb := expJet4Val_v_two_pt_diff g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f
      Kstar Kstar2 Kstar3 Kstar4 hKstar0 hKstar20 hKstar30 hKstar40
      hLipF hLipDF hLipD2F hLipD3F hLipD4F hKstar hKstar2f hKstar3f hKstar4f
      Φv Φw hΦv0 hΦw0 hΦvd hΦwd
      (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l)
      (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
      (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
      (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l)
      (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
      (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
      (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l)
      (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m)
      (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m)
      (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m)
      (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l)
      (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m)
      (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m)
      (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m)
      ((expJet4Fund g gi hC p v Φv
        (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l)
        (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m)
        (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) hv hΦvcont
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) h k l m).choose)
      ((expJet4Fund g gi hC p w Φw
        (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l)
        (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m)
        (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) hw hΦwcont
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m)
        (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m)
        (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) h k l m).choose)
      h k l m
      hQhkv0 hQhlv0 hQhmv0 hQklv0 hQkmv0 hQlmv0 hQhkw0 hQhlw0 hQhmw0 hQklw0 hQkmw0 hQlmw0
      hQhklv0 hQhkmv0 hQhlmv0 hQklmv0 hQhklw0 hQhkmw0 hQhlmw0 hQklmw0 hRv0 hRw0
      hQhkvd hQhlvd hQhmvd hQklvd hQkmvd hQlmvd hQhkwd hQhlwd hQhmwd hQklwd hQkmwd hQlmwd
      hQhklvd hQhkmvd hQhlmvd hQklmvd hQhklwd hQhkmwd hQhlmwd hQklmwd hRvd hRwd
    have hπ : expJetPi (expJet4ValG g gi hC p v Φv hv hΦvcont h k l m)
          - expJetPi (expJet4ValG g gi hC p w Φw hw hΦwcont h k l m)
        = expJetPi ((expJet4Fund g gi hC p v Φv
            (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l)
            (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l)
            (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont l m)
            (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l)
            (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m)
            (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m)
            (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) hv hΦvcont
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k)
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l)
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m)
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l)
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m)
            (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m)
            (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l)
            (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m)
            (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m)
            (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) h k l m).choose 1
          - (expJet4Fund g gi hC p w Φw
            (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l)
            (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l)
            (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont l m)
            (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l)
            (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m)
            (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m)
            (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) hw hΦwcont
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k)
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l)
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m)
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l)
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m)
            (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m)
            (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l)
            (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m)
            (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m)
            (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) h k l m).choose 1) := by
      rw [map_sub]; rfl
    rw [hπ]
    refine ((expJetPi (n := n)).le_opNorm _).trans ?_
    refine (mul_le_mul expJetPi_opNorm_le hb (norm_nonneg _) (by norm_num)).trans ?_
    exact le_of_eq (by ring)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun m => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun l => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, expJetD4_apply, expJetD4_apply]
  calc ‖expJetPi (expJet4ValG g gi hC p v Φv hv hΦvcont h k l m)
          - expJetPi (expJet4ValG g gi hC p w Φw hw hΦwcont h k l m)‖
      ≤ C * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := hval m l k h
    _ = C * ‖v - w‖ * ‖m‖ * ‖l‖ * ‖k‖ * ‖h‖ := by ring

end QIQTH.ExpMap
