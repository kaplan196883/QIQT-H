/-
# Global sections of the record presheaf (Prize Stage 2: sheaf / gluing layer)

Stage 2 of `PRIZE_EXECUTION_PLAN.md`: existence and classification of global sections `λ ∈ Γ(X)`
— the foliation-free actuality selectors — and the gluing/cohomology obstruction.

For a record presheaf over a poset **directed to a greatest element `⊤`** (the product / finite-
mode case: every diamond sits inside one total region), gluing is UNOBSTRUCTED: every record of
`⊤` extends to a global section by restriction (`topSection`), and conversely every global section
is DETERMINED by its `⊤`-value (`globalSection_eq_top`).  So `Γ(X) ≃ X ⊤` — the Roberts–DHR
gluing cocycle vanishes trivially because the top chart is already global.  (This is the honest
finite/product case; the genuinely-nontrivial cohomology arises only for posets WITHOUT a global
chart, the continuum target — see `PRIZE_EXECUTION_PLAN.md` Stage 2.3.)

Instantiated on the diamond net (`DiamondSwapNet`): the selectors `λ` are EXACTLY the joint
2-mode records (the top fibre `Fin m × Fin m`), unobstructed.  Axiom-free (standard three only).
-/
import QIQTH.DiamondSwapNet

namespace QIQTH.SheafSection

open LorentzSelection

variable {Diam : Type*} [Preorder Diam]

/-- **Gluing is unobstructed (existence).**  Any record `x` of a greatest diamond `⊤` extends to a
    global section by restriction — the foliation-free section is built from the top chart. -/
def topSection (P : RecordPresheaf Diam) (T : Diam) (htop : ∀ D, D ≤ T) (x : P.X T) :
    GlobalSection P where
  val := fun D => P.restrict (htop D) x
  consistent := fun {_ _} h => by rw [P.restrict_comp h (htop _) x]

/-- **Classification (uniqueness).**  Every global section is determined by its value on `⊤`:
    `λ_D = ρ_{⊤,D}(λ_⊤)`. -/
theorem globalSection_eq_top {P : RecordPresheaf Diam} {T : Diam} (htop : ∀ D, D ≤ T)
    (lam : GlobalSection P) (D : Diam) : lam.val D = P.restrict (htop D) (lam.val T) :=
  (lam.consistent (htop D)).symm

/-- The constructed section recovers its top record. -/
theorem topSection_val_top {P : RecordPresheaf Diam} {T : Diam} (htop : ∀ D, D ≤ T) (x : P.X T) :
    (topSection P T htop x).val T = x := P.restrict_id x

/- ── Instantiation on the diamond net: λ = the joint 2-mode records ─────────── -/

open DiamondSwapNet

/-- The diamond poset is directed to `top`. -/
theorem D3_le_top : ∀ D : D3, D ≤ D3.top := by
  rintro (_ | _ | _) <;> exact Or.inr rfl

/-- **The selectors over the diamond net are exactly the joint 2-mode records.**  Each joint
    record `x : Fin m × Fin m` of the full region `top` is a global section `λ` (its sub-region
    values are the marginals `x.1`, `x.2`); gluing is unobstructed. -/
def diamondSelector (m : ℕ) (x : Fin m × Fin m) : GlobalSection (Prec3 m) :=
  topSection (Prec3 m) D3.top D3_le_top x

/-- **Classification on the diamond net:** every selector `λ` is determined by its joint record
    `λ_top : Fin m × Fin m` — the foliation-free global section is the top record, and the sub-
    diamond values are its marginals.  Gluing/cohomology is trivial because `top` is a global
    chart. -/
theorem diamondSelector_classifies (m : ℕ) (lam : GlobalSection (Prec3 m)) (D : D3) :
    lam.val D = (Prec3 m).restrict (D3_le_top D) (lam.val D3.top) :=
  globalSection_eq_top D3_le_top lam D

end QIQTH.SheafSection
