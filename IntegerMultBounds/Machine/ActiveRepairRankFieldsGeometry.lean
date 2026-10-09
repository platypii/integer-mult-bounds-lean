import IntegerMultBounds.Machine.ActiveRepairRankFieldsRun
import IntegerMultBounds.Machine.VaryingControlRepairLayoutRank
import IntegerMultBounds.Machine.CountedPackedGuarded

/-! Physical extraction offsets for actual RECORD address ranks. Payload is
one in this address geometry; the physical R-bit record is separate. No
padding or source word is assumed, and original array bits are not reordered. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout CompactActiveTargetGeometry
open VaryingControlRepairLayoutRank
open BinaryAddressTableData (row)

def tailBits (s : Shape) := s.H+s.B
def targetStart (s : Shape) (after : ℕ) := after+tailBits s
def prefixStart (s : Shape) (m after : ℕ) := m+targetStart s after
def tStart (s : Shape) (w m before after : ℕ) := prefixStart s m after+((s.H-w)+s.F+before)
def uStart (s : Shape) (w m before after : ℕ) := prefixStart s m after+((s.H-w)+w+(s.H-w)+s.F+before)

theorem suffix_one (s : Shape) (after : ℕ) (hp : s.payload=1) :
    targetSuffix s after=2^(targetStart s after) := by
  unfold targetSuffix targetStart tailBits
  rw [hp,mul_one,←pow_add]

theorem prefix_one (s : Shape) (m after : ℕ) (hp : s.payload=1) :
    2^m*targetSuffix s after=2^(prefixStart s m after) := by
  rw [suffix_one s after hp,←pow_add]
  rfl

theorem t_copies_pow (s : Shape) (w before : ℕ) : tCopies s w before=2^((s.H-w)+s.F+before) := by
  unfold tCopies
  rw [←pow_add,←pow_add]

theorem u_copies_pow (s : Shape) (w before : ℕ) : uCopies s w before=2^((s.H-w)+w+(s.H-w)+s.F+before) := by
  unfold uCopies
  rw [←pow_add,←pow_add,←pow_add,←pow_add]

private theorem word_eq_row (cs : List Bool) (start width v : ℕ) (hv : v<2^width)
    (hvalue : Counter.value (Gather.field cs start width)=v) :
    Gather.field cs start width=row width v := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp
  · rw [BinaryAddressTableData.row_rank width v hv]
    exact hvalue

variable (s : Shape) (w m before after rows : ℕ) (hw : w≤s.H)
variable (hactive : before+m+after=s.active*s.chunk) (hp : s.payload=1)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hc : Counter.value cs=(index s w m before after rows hw hactive x).val)

include hc hp in
theorem target_word : Gather.field cs (targetStart s after) m=row m x.target.val := by
  apply word_eq_row cs _ _ _ x.target.isLt
  rw [CountedRankSplitData.value_middle,hc]
  have h := target_from_rank s w m before after rows hw hactive x
  rw [suffix_one s after hp] at h
  exact h

include hc hp in
theorem t_word : Gather.field cs (tStart s w m before after) w=row w x.t.val := by
  apply word_eq_row cs _ _ _ x.t.isLt
  rw [CountedRankSplitData.value_middle,hc]
  have h := t_from_rank s w m before after rows hw hactive x
  rw [prefix_one s m after hp,t_copies_pow,Nat.div_div_eq_div_mul,←pow_add] at h
  exact h

include hc hp in
theorem u_word : Gather.field cs (uStart s w m before after) w=row w x.u.val := by
  apply word_eq_row cs _ _ _ x.u.isLt
  rw [CountedRankSplitData.value_middle,hc]
  have h := u_from_rank s w m before after rows hw hactive x
  rw [prefix_one s m after hp,u_copies_pow,Nat.div_div_eq_div_mul,←pow_add] at h
  exact h

include hc hp in
theorem before_word : Gather.field cs (prefixStart s m after) before=row before x.activeBefore.val := by
  apply word_eq_row cs _ _ _ x.activeBefore.isLt
  rw [CountedRankSplitData.value_middle,hc]
  have h := before_from_rank s w m before after rows hw hactive x
  rw [prefix_one s m after hp] at h
  exact h

include hc hp in
theorem after_word : Gather.field cs (tailBits s) after=row after x.activeAfter.val := by
  apply word_eq_row cs _ _ _ x.activeAfter.isLt
  rw [CountedRankSplitData.value_middle,hc]
  have h := after_from_rank s w m before after rows hw hactive x
  rw [suffix_one s after hp,hp,mul_one] at h
  change ((index s w m before after rows hw hactive x).val%2^(after+tailBits s))/2^(tailBits s)=_ at h
  rw [pow_add,Nat.mod_mul_left_div_self] at h
  exact h

private theorem field_getD (xs : List Bool) (start width j : ℕ) (hj : j<width) :
    (Gather.field xs start width).getD j false=xs.getD (start+j) false := by
  simp only [Gather.field,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some]

private theorem field_field (xs : List Bool) (start count offset width : ℕ) (hp : offset+width≤count) :
    Gather.field (Gather.field xs start count) offset width=Gather.field xs (start+offset) width := by
  change (List.range width).map (fun j => (Gather.field xs start count).getD (offset+j) false)=
    (List.range width).map (fun j => xs.getD (start+offset+j) false)
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  rw [field_getD xs start count (offset+j) (by omega)]
  congr 1
  omega

/- The complete earlier source slot, at its actual little-endian offset
inside activeBefore, is copied directly from the short original rank. -/
include hc hp in
theorem before_source (offset width : ℕ) (hplace : offset+width≤before) :
    Gather.field cs (prefixStart s m after+offset) width=
      Gather.field (row before x.activeBefore.val) offset width := by
  rw [←before_word s w m before after rows hw hactive hp x cs hc]
  exact (field_field cs (prefixStart s m after) before offset width hplace).symm

include hc hp in
theorem after_source (offset width : ℕ) (hplace : offset+width≤after) :
    Gather.field cs (tailBits s+offset) width=
      Gather.field (row after x.activeAfter.val) offset width := by
  rw [←after_word s w m before after rows hw hactive hp x cs hc]
  exact (field_field cs (tailBits s) after offset width hplace).symm

end
end IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry
