import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.BinaryDescriptorFrames

/-! Restore a saved ancestor frame over the child's still-present headers.
The child's descriptors are physically erased and rewound before any frame is
popped; the final bank contains the saved words and the exact older stack. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorFrameRestore
open BinaryDescriptorFrames
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

abbrev slots {stack : Fin t} (ops : List (Slot stack)) : List (Fin t) := ops.map Subtype.val

theorem slots_nodup {stack : Fin t} (ops : List (Slot stack)) (hu : ops.Nodup) : (slots ops).Nodup :=
  hu.map Subtype.val_injective

private theorem saved_setTape (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (i : Fin t) (hi : i ≠ stack) (f : ℤ → Fin (a+4)) (p : ℤ) :
    saved stack ops xs (setTape v i f p) = setTape (saved stack ops xs v) i f p := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih =>
    have hw : write stack op xs (setTape v i f p) = setTape (write stack op xs v) i f p := by
      apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : j = i <;> by_cases hs : j = stack <;>
        simp_all [write,setTape]
    simp only [saved,hw,ih]

/-- This is an equality of exact tape banks used to compose the two real
machines; it supplies no machine transition and no free clearing operation. -/
theorem cleared_saved (stack : Fin t) (ops : List (Slot stack)) (xs : Fin t → List Bool)
    (v : Tapes t a) (fields : List (Fin t)) (hfields : ∀ i ∈ fields, i ≠ stack) :
    BinaryDescriptorCleanupList.cleared fields (saved stack ops xs v) =
      saved stack ops xs (BinaryDescriptorCleanupList.cleared fields v) := by
  induction fields generalizing v with
  | nil => rfl
  | cons i fields ih =>
    rw [BinaryDescriptorCleanupList.cleared,← saved_setTape stack ops xs v i (hfields i List.mem_cons_self)]
    exact ih _ (fun j hj => hfields j (List.mem_cons_of_mem _ hj))

theorem restored_cleared {stack : Fin t} (ops : List (Slot stack)) (hu : ops.Nodup)
    (xs : Fin t → List Bool) (v : Tapes t a) :
    restored ops xs (BinaryDescriptorCleanupList.cleared (slots ops) v) = restored ops xs v := by
  have he (i : Fin t) :
      (restored ops xs (BinaryDescriptorCleanupList.cleared (slots ops) v)).head i = (restored ops xs v).head i ∧
      (restored ops xs (BinaryDescriptorCleanupList.cleared (slots ops) v)).tape i = (restored ops xs v).tape i := by
    by_cases hi : i ∈ slots ops
    · obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
      have h1 := restored_field ops hu xs (BinaryDescriptorCleanupList.cleared (slots ops) v) op hop
      have h2 := restored_field ops hu xs v op hop
      exact ⟨h1.1.trans h2.1.symm,h1.2.trans h2.2.symm⟩
    · have hn : ∀ op ∈ ops, i ≠ op.val := by
        intro op hop he
        exact hi (List.mem_map.mpr ⟨op,hop,he.symm⟩)
      have h1 := restored_frame ops xs (BinaryDescriptorCleanupList.cleared (slots ops) v) i hn
      have h2 := restored_frame ops xs v i hn
      have hc := BinaryDescriptorCleanupList.cleared_frame (slots ops) v i hi
      exact ⟨h1.1.trans (hc.1.trans h2.1.symm),h1.2.trans (hc.2.trans h2.2.symm)⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

noncomputable def program (stack : Fin t) (ops : List (Slot stack)) :
    Program t (BinaryDescriptorCleanupList.states (slots ops)+popStates ops) a :=
  seq (BinaryDescriptorCleanupList.program (Nat.zero_lt_of_lt stack.isLt) (slots ops)) (popProgram stack ops)

/-- Child headers are nonblank in the precondition. Their physical reset is
charged before restoring the saved ancestor fields into those same slots. -/
theorem restore_hoare (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup)
    (older child : Fin t → List Bool) (v : Tapes t a)
    (hchild : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (child i))
    (hfree : Free stack ops older v) :
    HoareTime (program stack ops) (fun w => w = saved stack ops older v)
      (fun w => w = restored ops older v)
      (BinaryDescriptorCleanupList.cost (slots ops) child+1+cost ops older) := by
  have hnot : stack ∉ slots ops := by
    intro h
    obtain ⟨i,_,he⟩ := List.mem_map.mp h
    exact i.property he
  have hs := BinaryDescriptorCleanupList.cleanup_hoare (Nat.zero_lt_of_lt stack.isLt) (slots ops)
    (slots_nodup ops hu) child (saved stack ops older v) (by
      intro i hi
      obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
      have hh := saved_frame stack ops older v op.val op.property
      have hc := hchild op hop
      exact ⟨hh.1.trans hc.1,hh.2.trans hc.2⟩)
  rw [cleared_saved stack ops older v (slots ops) (by
    intro i hi
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hi
    exact op.property)] at hs
  have hstack := BinaryDescriptorCleanupList.cleared_frame (slots ops) v stack hnot
  have hp := BinaryDescriptorFrames.pop_hoare stack ops hu older (BinaryDescriptorCleanupList.cleared (slots ops) v)
    (by
      intro i hi
      exact BinaryDescriptorCleanupList.cleared_slot (slots ops) (slots_nodup ops hu) v i.val (List.mem_map.mpr ⟨i,hi,rfl⟩))
    (by
      unfold Free at *
      simpa only [hstack.1,hstack.2] using hfree)
  rw [restored_cleared ops hu older v] at hp
  exact hs.seq hp

end IntegerMultBounds.Machine.BinaryDescriptorFrameRestore
