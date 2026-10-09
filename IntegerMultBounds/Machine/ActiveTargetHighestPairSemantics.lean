import IntegerMultBounds.Machine.ActiveTargetHighestPairBudget
import IntegerMultBounds.Machine.ActivePrefixLayoutFields

/-! Exact XOR of the two physical one-bit fields. The source bit, arbitrary
outer rows, intervening bits and suffix remain literal spectators. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairSemantics
noncomputable section
open ActiveTargetHighestPairData
open ActiveTargetHighestLaterValue (xorBit)
open RecursiveInterchangeRows (pack pack_val)

variable (g : Geometry)

theorem prefix_size : P g*2*gap g=g.rows*2^W g := by
  unfold P gap W
  simp only [pow_add,pow_one]
  ring

def prefixIndex (p : Fin (P g)) (source : Fin 2) (gapBit : Fin (gap g)) : Fin (g.rows*2^W g) :=
  Fin.cast (prefix_size g) (pack (pack p source) gapBit)

theorem prefix_val (p : Fin (P g)) (source : Fin 2) (gapBit : Fin (gap g)) :
    (prefixIndex g p source gapBit).val=(p.val*2+source.val)*2^g.G+gapBit.val := by
  change (pack (pack p source) gapBit).val=_
  rw [pack_val (pack p source) gapBit,pack_val p source]
  rfl

theorem source_value (p : Fin (P g)) (source : Fin 2) (gapBit : Fin (gap g)) :
    (prefixIndex g p source gapBit).val/2^g.G%2=source.val := by
  rw [prefix_val,Nat.add_comm,Nat.add_mul_div_right _ _ (by positivity),Nat.div_eq_of_lt (show gapBit.val<2^g.G from gapBit.isLt)]
  have := source.isLt
  omega

theorem offset (i : Fin (g.rows*2^W g)) :
    PackedOffsetPayloadValue.offset (ActivePrefixDirtyControlLoadData.offsets (m := .pure) (loadShape g) g.rows)
      1 i.val=i.val/2^g.G%2 := by
  unfold PackedOffsetPayloadValue.offset
  change Counter.value (Gather.field (BinaryAddressOffsetRepeatData.copies
    (ActivePrefixDirtyControlPureBank.offsetWord (loadShape g)) g.rows) (i.val*1) 1)=_
  rw [ActivePrefixLayoutFields.repeated_field _ (2^W g) 1 g.rows i.val (by positivity)
    (ActivePrefixDirtyControlPureBank.offset_length (loadShape g)) i.isLt]
  have hh := ActivePrefixDirtyControlPureSemantics.offset_bits (loadShape g) (i.val%2^W g) (Nat.mod_lt _ (by positivity))
  change Gather.field _ ((i.val%2^W g)*1) 1=_ at hh
  rw [hh]
  have hG : g.G<W g := by unfold W; omega
  simp only [loadShape,Nat.sub_self,List.replicate_zero,List.range_one,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,Nat.zero_mul,Nat.add_zero,
    Nat.testBit_mod_two_pow,show decide (g.G<W g)=true from decide_eq_true hG,Bool.true_and]
  change (ActiveTargetHighestValue.bit (Nat.testBit i.val g.G)).val=_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  exact ActiveTargetHighestValue.sourceBit_value g.G i.val

theorem full_index (p : Fin (P g)) (source target : Fin 2) (gapBit : Fin (gap g)) (j : Fin (suffix g)) :
    Fin.cast (load_volume g).symm (FiberLayoutData.index (prefixIndex g p source gapBit) target j)=
      RadixRangePadding.index p source gapBit target j := by
  apply Fin.ext
  change (FiberLayoutData.index (prefixIndex g p source gapBit) target j).val=
    (RadixRangePadding.index p source gapBit target j).val
  simp [FiberLayoutData.index,prefixIndex,RadixRangePadding.index,RecursiveInterchangeRows.pack,finProdFinEquiv]
  ring

theorem earlier_entry (array : Array g) (p : Fin (P g)) (source target : Fin 2)
    (gapBit : Fin (gap g)) (j : Fin (suffix g)) :
    result g array (RadixRangePadding.index p source gapBit (xorBit target source) j)=
      array (RadixRangePadding.index p source gapBit target j) := by
  have h := ActivePrefixDirtyControlLoad.entry (m := .pure) (loadShape g) g.rows (suffix g)
    (view (load_volume g) array) (prefixIndex g p source gapBit) target j
  have ho := (offset g (prefixIndex g p source gapBit)).trans (source_value g p source gapBit)
  change PackedOffsetPayloadValue.offset _ (ActivePrefixDirtyControlLoadProducer.width (m := .pure) (loadShape g))
    (prefixIndex g p source gapBit).val=source.val at ho
  rw [ho] at h
  have hd := full_index g p source (xorBit target source) gapBit j
  have hi := full_index g p source target gapBit j
  rw [←hd,←hi]
  exact h

theorem result_eq_earlier (array : Array g) : result g array=ActiveTargetHighestLaterValue.earlier array := by
  funext z
  let c := RadixRangePadding.coordinates z
  have h := earlier_entry g array c.1 c.2.1 (xorBit c.2.2.2.1 c.2.1) c.2.2.1 c.2.2.2.2
  rw [ActiveTargetHighestLaterValue.xorBit_twice] at h
  calc
    _ = result g array (RadixRangePadding.index c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2) :=
      congrArg (result g array) (RadixRangePadding.index_coordinates z).symm
    _ = _ := h

theorem later_eq (array : Array g) : later g array=ActiveTargetHighestLaterValue.later array := by
  unfold later
  rw [result_eq_earlier g (RadixRangePadding.transpose array)]
  exact ActiveTargetHighestLaterValue.conjugation array

theorem later_entry (array : Array g) (p : Fin (P g)) (target source : Fin 2)
    (gapBit : Fin (gap g)) (j : Fin (suffix g)) :
    later g array (RadixRangePadding.index p (xorBit target source) gapBit source j)=
      array (RadixRangePadding.index p target gapBit source j) := by
  rw [later_eq]
  exact ActiveTargetHighestLaterValue.later_entry array p target source gapBit j

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairSemantics
