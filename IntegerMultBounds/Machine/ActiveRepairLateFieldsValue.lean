import IntegerMultBounds.Machine.ActiveRepairLateFieldsPlaced
import IntegerMultBounds.Machine.CountedLateRepairKeyValue

/-! Identify the actual later guard and recovered destination with rankFlag
and rankKey using only genuine extracted lengths. The concatenated local
word is mathematical notation and is never supplied to the physical machine. -/
namespace IntegerMultBounds.Machine.ActiveRepairLateFieldsValue
noncomputable section
open IntegerMultBounds.Compact
open IntegerMultBounds.Compact.PowerTwo

private theorem low_field (V W : List Bool) : Gather.field (V++W) 0 V.length=V := by
  apply List.ext_getElem
  · simp
  · intro j _ hj
    simp only [Gather.field,List.getElem_map,List.getElem_range,zero_add]
    rw [List.getD_append V W false j hj]
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]

private theorem middle_field (V W U : List Bool) :
    Gather.field (V++W++U) V.length W.length=W := by
  apply List.ext_getElem
  · simp
  · intro j _ hj
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    rw [List.getD_append (V++W) U false (V.length+j) (by simp; omega)]
    rw [List.getD_append_right V W false (V.length+j) (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj,Option.getD_some]

private theorem high_field (V W : List Bool) : Gather.field (V++W) V.length W.length=W := by
  apply List.ext_getElem
  · simp
  · intro j _ hj
    simp only [Gather.field,List.getElem_map,List.getElem_range]
    rw [List.getD_append_right V W false (V.length+j) (by omega)]
    simp only [Nat.add_sub_cancel_left,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj,Option.getD_some]

theorem original_fields (q b : ℕ) (V W U X : List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    CountedLateRepairKeyRun.V q X (V++W++U)=V ∧
    CountedLateRepairKeyRun.W q b X (V++W++U)=W ∧
    CountedLateRepairKeyRun.U q b X (V++W++U)=U := by
  refine ⟨?_,?_,?_⟩
  · simpa only [CountedLateRepairKeyRun.V,hV,List.append_assoc] using low_field V (W++U)
  · simpa only [CountedLateRepairKeyRun.W,hV,hW] using middle_field V W U
  · simpa only [CountedLateRepairKeyRun.U,List.length_append,hV,hW,hU] using high_field (V++W) U

theorem local_bound (q b : ℕ) (hq : 1≤q) (V W U X : List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    Counter.value (V++W++U)<lateMi q b X := by
  rw [lateMi_eq q b X hq]
  simpa only [List.length_append,hV,hW,hU] using Counter.value_lt (V++W++U)

theorem flag_rank (q b : ℕ) (hb : 1≤b) (hbq : b+3≤q) (V W U X : List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    (CountedLateRepairGuard.flag q b V W X || CountedLateRepairGuard.flag q b V U X)=
      rankFlag (lateRankEquiv q b X) (lateBadSet q b X) (Counter.value (V++W++U)) := by
  have h := CountedLateRepairKeyValue.flag_rank q b hb hbq X (V++W++U) _
    (local_bound q b (by omega) V W U X hV hW hU) rfl
  obtain ⟨hv,hw,hu⟩ := original_fields q b V W U X hV hW hU
  rw [hv,hw,hu] at h
  exact h

theorem destination_bits (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (V W U X : List Bool)
    (hV : V.length=X.length*q) (hW : W.length=X.length*b) (hU : U.length=X.length*b) :
    CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U X) X ++
      (CountedLateRepairInverse.temp q b hb hbq V W U X ++ CountedLateRepairInverse.restored b hb U X)=
      rankKey (lateRankEquiv q b X) (lateSperm q b X) (lateTperm q b X)
        (X.length*q+X.length*b+X.length*b) (Counter.value (V++W++U)) := by
  have h := CountedLateRepairKeyValue.bits_rank q b hb hbq X (V++W++U) _
    (local_bound q b (by omega) V W U X hV hW hU) rfl
  obtain ⟨hv,hw,hu⟩ := original_fields q b V W U X hV hW hU
  rw [hv,hw,hu] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairLateFieldsValue
