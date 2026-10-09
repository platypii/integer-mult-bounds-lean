import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationDestination
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginal
import IntegerMultBounds.Machine.ActiveRepairLateKeyOriginal

/-! Original geometric descriptors decode exactly the global permutation's
current target/T/U and varying retained source. No computed field starts or
control word is supplied to this identification. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutKeysFields
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairRankHeadersData ActiveRepairRankHeadersEndpoint
open ActiveRepairRankFieldsBank (offsetSlot widthSlot)
open ActiveRepairLayoutPermutationFiber

variable (s : Shape) (w m before after rows offset width rowBits : ℕ)
variable (side : SourceSide) (hw : w≤s.H) (ha : before+m+after=s.active*s.chunk) (hp : s.payload=1)
variable (hf : sourceFits side before after offset width)
variable (x : Address s w m before after rows) (cs : List Bool)
variable (hc : Counter.value cs=(index s w m before after rows hw ha x).val)

include hw ha hp hf hc in
theorem parsed_fields :
    Gather.field cs (parserValues side (geometry s w m before after offset width rowBits) (offsetSlot 0))
      (parserValues side (geometry s w m before after offset width rowBits) (widthSlot 0))=
        BinaryAddressTableData.row m x.target.val ∧
    Gather.field cs (parserValues side (geometry s w m before after offset width rowBits) (offsetSlot 1))
      (parserValues side (geometry s w m before after offset width rowBits) (widthSlot 1))=
        BinaryAddressTableData.row w x.t.val ∧
    Gather.field cs (parserValues side (geometry s w m before after offset width rowBits) (offsetSlot 2))
      (parserValues side (geometry s w m before after offset width rowBits) (widthSlot 2))=
        BinaryAddressTableData.row w x.u.val ∧
    Gather.field cs (parserValues side (geometry s w m before after offset width rowBits) (offsetSlot 3))
      (parserValues side (geometry s w m before after offset width rowBits) (widthSlot 3))=
        sourceWord before after offset width side (x.activeBefore,x.activeAfter) := by
  cases side with
  | before =>
    have h i := parser_before_values s w m before after offset width rowBits hw i
    refine ⟨?_,?_,?_,?_⟩
    · rw [(h 0).1,(h 0).2]
      exact ActiveRepairRankFieldsGeometry.target_word s w m before after rows hw ha hp x cs hc
    · rw [(h 1).1,(h 1).2]
      exact ActiveRepairRankFieldsGeometry.t_word s w m before after rows hw ha hp x cs hc
    · rw [(h 2).1,(h 2).2]
      exact ActiveRepairRankFieldsGeometry.u_word s w m before after rows hw ha hp x cs hc
    · rw [(h 3).1,(h 3).2]
      exact ActiveRepairRankFieldsGeometry.before_source s w m before after rows hw ha hp x cs hc
        offset width hf
  | after =>
    have h i := parser_after_values s w m before after offset width rowBits hw i
    refine ⟨?_,?_,?_,?_⟩
    · rw [(h 0).1,(h 0).2]
      exact ActiveRepairRankFieldsGeometry.target_word s w m before after rows hw ha hp x cs hc
    · rw [(h 1).1,(h 1).2]
      exact ActiveRepairRankFieldsGeometry.t_word s w m before after rows hw ha hp x cs hc
    · rw [(h 2).1,(h 2).2]
      exact ActiveRepairRankFieldsGeometry.u_word s w m before after rows hw ha hp x cs hc
    · rw [(h 3).1,(h 3).2]
      exact ActiveRepairRankFieldsGeometry.after_source s w m before after rows hw ha hp x cs hc
        offset width hf

open IntegerMultBounds.Compact

private theorem word_bit (xs : List Bool) (i : ℕ) (hi : i<xs.length) :
    xs[i]=Nat.testBit (Counter.value xs) i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons b xs ih =>
    have hv : Counter.value (b::xs)=Nat.bit b (Counter.value xs) := by
      cases b
      · simp [Counter.value]
      · simp [Counter.value,Nat.add_comm]
    rw [hv]
    cases i with
    | zero => simp only [List.getElem_cons_zero,Nat.testBit_bit_zero]
    | succ i => simpa only [List.getElem_cons_succ,Nat.testBit_bit_succ] using ih i (by simpa using hi)
theorem rankBits_row (w i : ℕ) : rankBits w i=BinaryAddressTableData.row w i := by
  apply List.ext_getElem (by simp [rankBits])
  intro j hj hr
  rw [word_bit _ _ hr,BinaryAddressTableData.row_value]
  simp only [rankBits,List.getElem_ofFn]
  have h : j<w := by simpa [rankBits] using hj
  simp [Nat.testBit_mod_two_pow,h]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutKeysFields
