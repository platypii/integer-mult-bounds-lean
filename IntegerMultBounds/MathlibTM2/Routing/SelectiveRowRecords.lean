module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRows
public import IntegerMultBounds.MathlibTM2.Node.Rect

/-! The complete selective record endpoint decomposes into identical row-local
permutations. No tape execution or row extraction cost is assumed here. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-- Reassemble independently routed rows in their original outer order. -/
theorem moveRecs_selective_rows {p : Par} {X : ℕ} {α : Type*}
    (hK : 0 < p.K) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hs : ∀ c, (s c).Allowed active) (R : ℕ) (l : List (List α)) :
    moveRecs (selectiveIdealPerm hK active s R hs) l =
      (List.ofFn fun row : Fin R => List.ofFn fun i : Fin (2 ^ fieldsLen (selectiveLen p X)) =>
        l.getD (row.val * 2 ^ fieldsLen (selectiveLen p X) +
          selectiveIdealIdx p X active s i.val) []).flatten := by
  unfold moveRecs
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  apply congrArg List.ofFn
  funext i
  change l.getD (selectiveIdealIdx p X active s
    (row.val * 2 ^ fieldsLen (selectiveLen p X) + i.val)) [] = _
  rw [selectiveIdealIdx_row_offset active s row.val i.val i.isLt]

end IntegerMultBounds.MathlibTM2.Routing
