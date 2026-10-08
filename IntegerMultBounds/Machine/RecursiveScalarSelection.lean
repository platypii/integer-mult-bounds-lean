import IntegerMultBounds.Machine.RecursiveViewedAction
import IntegerMultBounds.Machine.Shared50NonrecursiveCoordinates

/-! Static routing of the actual ordered scalar descriptions to paid recursive
coordinate views. The selected fields retain the original H-before-D numbering;
no runtime descriptor, dimension or replacement schedule enters the selection. -/
namespace IntegerMultBounds.Machine.RecursiveScalarSelection
noncomputable section
open Networks
open RecursiveViewRoleBank (Selection)
open RecursiveViewedAction (Action)
open AffineFieldCoordinates (hIndex dIndex)
variable {m t : ℕ}

/-- Original field exposed as the first variable field of a view. -/
def first : Selection m → Fin (m+m)
  | .cross i _ => hIndex i
  | .within .h j _ _ => hIndex j
  | .within .d j _ _ => dIndex j

/-- Original field exposed as the second variable field of a view. -/
def second : Selection m → Fin (m+m)
  | .cross _ j => dIndex j
  | .within .h _ i _ => hIndex i
  | .within .d _ i _ => dIndex i

structure Plan (m t : ℕ) where
  selection : Selection m
  action : Action t

def Plan.rational (p : Plan m t) : OrderedAffine.Op (Fin (m+m)) ℚ :=
  match p.action with
  | .shift _ r _ => .shift (second p.selection) (first p.selection) r
  | .scale _ r _ .h => .scale (first p.selection) r
  | .scale _ r _ .d => .scale (second p.selection) r

/-- Every earlier-control operation has one of precisely three admissible
locations. Scale operations use the same-index field in the opposite group as
an unchanged spectator. -/
def compile (wire : Fin t) : FlatCoordinateSchedule.Op (m+m) → Plan m t
  | .scale target r hr =>
    if ht : target.val < m then
      ⟨.cross ⟨target.val,ht⟩ ⟨target.val,ht⟩,.scale wire r hr .h⟩
    else
      let i : Fin m := ⟨target.val-m,by omega⟩
      ⟨.cross i i,.scale wire r hr .d⟩
  | .shift target control earlier r hr =>
    if ht : target.val < m then
      let i : Fin m := ⟨target.val,ht⟩
      let j : Fin m := ⟨control.val,by have := control.isLt; change control.val < target.val at earlier; omega⟩
      ⟨.within .h j i earlier,.shift wire r (Shared50AffineCoefficients.denominator_bound hr)⟩
    else if hk : control.val < m then
      ⟨.cross ⟨control.val,hk⟩ ⟨target.val-m,by omega⟩,
        .shift wire r (Shared50AffineCoefficients.denominator_bound hr)⟩
    else
      let i : Fin m := ⟨target.val-m,by omega⟩
      let j : Fin m := ⟨control.val-m,by omega⟩
      ⟨.within .d j i (by change control.val-m < target.val-m; change control.val < target.val at earlier; omega),
        .shift wire r (Shared50AffineCoefficients.denominator_bound hr)⟩

/-- Routing changes neither the coefficient nor either original field index. -/
theorem compile_rational (wire : Fin t) (op : FlatCoordinateSchedule.Op (m+m)) :
    (compile wire op).rational = op.rational := by
  cases op with
  | scale target r hr =>
    simp only [compile]
    split
    · congr 1
    · rename_i ht
      dsimp only [Plan.rational,second,FlatCoordinateSchedule.Op.rational]
      congr 1
      apply Fin.ext
      simp only [dIndex,Fin.val_natAdd]
      omega
  | shift target control earlier r hr =>
    simp only [compile]
    split
    · congr 1
    · rename_i ht
      split
      · dsimp only [Plan.rational,first,second,FlatCoordinateSchedule.Op.rational]
        congr 1
        apply Fin.ext
        simp only [dIndex,Fin.val_natAdd]
        omega
      · rename_i hk
        dsimp only [Plan.rational,first,second,FlatCoordinateSchedule.Op.rational]
        congr 1 <;> apply Fin.ext <;> simp only [dIndex,Fin.val_natAdd] <;> omega

/-- The actual scalar description, including the two-step reflected subtraction,
is routed in its existing order. -/
theorem description_rational (wire : Fin t)
    (p : List (AffineFieldProgram.Op Shared50ModularSchedule.Index ℚ))
    (hp : p ∈ Shared50AffineControl.rationalSchedules)
    (op : AffineFieldProgram.Op Shared50ModularSchedule.Index ℚ)
    (hop : op ∈ p) (hn : AffineFieldCoordinates.Nonrecursive op) :
    ((Shared50NonrecursiveCoordinates.description p hp op hop hn).map (compile wire)).map Plan.rational =
      AffineFieldCoordinates.expand op := by
  simp only [List.map_map,Function.comp_def,compile_rational]
  exact Shared50NonrecursiveCoordinates.description_rational p hp op hop hn

end
end IntegerMultBounds.Machine.RecursiveScalarSelection
