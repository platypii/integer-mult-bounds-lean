import IntegerMultBounds.Machine.BinaryAddressOffsetData

/-! Project a contiguous runtime field from every full-width address, in
integer order. Zero-width fields and zero-width addresses are included. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableData
open BinaryAddressTableData

def shape (W start d : ℕ) (h : start+d≤W) : Gather.Shape := ⟨W,start,d,d,0,h,by omega⟩
def dummy (W : ℕ) := List.replicate (2^W) false
def word (W start d : ℕ) (h : start+d≤W) :=
  Gather.gather (fun x _ => x) (shape W start d h) (table W (2^W)) (dummy W) (2^W)

theorem digit_eq (W start d i : ℕ) (h : start+d≤W) (hi : i<2^W) :
    Gather.digitWord (fun x _ => x) (shape W start d h) (table W (2^W)) (dummy W) i =
      Gather.field (row W i) start d := by
  simp only [Gather.digitWord,shape,List.replicate_zero,List.nil_append,Nat.sub_zero,Nat.sub_self,
    List.append_nil ]
  unfold Gather.field
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' : j<d := List.mem_range.mp hj
  change (table W (2^W)).getD (i*W+start+j) false=(row W i).getD (start+j) false
  rw [Nat.add_assoc]
  exact BinaryAddressOffsetData.table_entry W (2^W) i (start+j) hi (by omega)

theorem word_rows (W start d : ℕ) (h : start+d≤W) :
    word W start d h = ((List.range (2^W)).map (fun i => Gather.field (row W i) start d)).flatten := by
  rw [word,Compact.PowerTwo.gather_flatten]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact digit_eq W start d i h (List.mem_range.mp hi)

@[simp] theorem word_length (W start d : ℕ) (h : start+d≤W) : (word W start d h).length=2^W*d :=
  Gather.gather_length _ _ _ _ _

end IntegerMultBounds.Machine.BinaryPrefixFieldTableData
