import IntegerMultBounds.Machine.ActiveRepairRankFieldsGeometry
import IntegerMultBounds.Machine.ActivePrefixSelectedOffsetData
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue

/-! Low prefix ranks retain every field wholly inside the generated prefix.
The outer row count is unrestricted; repeated tables use rank modulo 2^W. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutFields
open BinaryAddressTableData (row)
open RecursiveInterchangeRows (pack pack_val)

def prefixWord (W rank : ℕ) := row W (rank%2^W)

theorem field_value (W rank start width : ℕ) (hfit : start+width≤W) :
    Counter.value (Gather.field (prefixWord W rank) start width)=rank/2^start%2^width := by
  rw [CountedRankSplitData.value_middle,prefixWord,BinaryAddressTableData.row_rank W _ (Nat.mod_lt _ (by positivity))]
  have hW : W=start+(W-start) := by omega
  rw [hW,pow_add,Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))

theorem field_eq_row (W rank start width value : ℕ) (hfit : start+width≤W)
    (hv : value<2^width) (he : rank/2^start%2^width=value) :
    Gather.field (prefixWord W rank) start width=row width value := by
  apply CountedPackedGuarded.word_eq_of_length_value
  · simp
  · rw [field_value W rank start width hfit,BinaryAddressTableData.row_rank width value hv,he]

theorem packed_high {P B : ℕ} (p : Fin P) (j : Fin B) : (pack p j).val/B=p.val := by
  have hB : 0<B := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  rw [pack_val,Nat.add_comm,Nat.add_mul_div_right _ _ hB,Nat.div_eq_of_lt j.isLt,zero_add]
theorem packed_low {P B : ℕ} (p : Fin P) (j : Fin B) : (pack p j).val%B=j.val := by
  rw [pack_val,Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]

theorem field_field (xs : List Bool) (start count offset width : ℕ) (hfit : offset+width≤count) :
    Gather.field (Gather.field xs start count) offset width=Gather.field xs (start+offset) width := by
  unfold Gather.field
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  have he := ActivePrefixSelectedOffsetData.field_bit xs start count (offset+j) (by omega)
  simpa only [Gather.field,Nat.add_assoc] using he

theorem repeated_field (xs : List Bool) (N width rows rank : ℕ) (hN : 0<N)
    (hlen : xs.length=N*width) (hrank : rank<rows*N) :
    Gather.field (BinaryAddressOffsetRepeatData.copies xs rows) (rank*width) width=
      Gather.field xs ((rank%N)*width) width := by
  have hk : rank/N<rows := (Nat.div_lt_iff_lt_mul hN).mpr hrank
  have hi := Nat.mod_lt rank hN
  have hsplit : rank/N*N+rank%N=rank := by simpa only [Nat.mul_comm] using Nat.div_add_mod rank N
  unfold Gather.field
  apply List.map_congr_left
  intro j hj
  have hjw := List.mem_range.mp hj
  have he := BinaryAddressOffsetRepeatValue.copies_entry xs rows (rank/N) ((rank%N)*width+j) hk (by rw [hlen]; nlinarith)
  rw [hlen] at he
  have hp : rank/N*(N*width)+((rank%N)*width+j)=rank*width+j := by nlinarith [hsplit]
  rw [hp] at he
  simpa only [List.getD_eq_getElem?_getD] using congrArg (fun x : Option Bool => x.getD false) he

end IntegerMultBounds.Machine.ActivePrefixLayoutFields
