import IntegerMultBounds.Machine.PrefixWidthCopies

/-! Run prefix width replication using a descriptor already resident in an
arbitrary preserved bank; no additional source tape is allocated. -/
namespace IntegerMultBounds.Machine.PrefixWidthCopiesAt
open PrefixCounterInit (tapeCount)
noncomputable section
variable {t q : ℕ}

def slots (src : Fin t) (c : ℕ) : Fin (1+tapeCount c) → Fin (t+tapeCount c) :=
  Fin.addCases (fun _ => Fin.castAdd (tapeCount c) src) (Fin.natAdd t)

theorem slots_injective (src : Fin t) (c : ℕ) : Function.Injective (slots src c) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => congr 1; exact Subsingleton.elim _ _
    | right j =>
      have hv := congrArg Fin.val h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hs := src.isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      simp only [slots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hs := src.isLt
      omega
    | right j =>
      apply congrArg (Fin.natAdd 1)
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [slots] using hv

def placement (src : Fin t) (c : ℕ) : Fin ((1+tapeCount c)+(t-1)) ≃ Fin (t+tapeCount c) :=
  InjectivePlacement.placement (slots src c) (slots_injective src c) (by have h := src.isLt; omega)

@[simp] theorem placement_active (src : Fin t) (c : ℕ) (i : Fin (1+tapeCount c)) :
    placement src c (Fin.castAdd (t-1) i) = slots src c i :=
  InjectivePlacement.active_slot _ _ _ _

def program (q : ℕ) (src : Fin t) (c : ℕ) :
    Program (t+tapeCount c) (BinaryDescriptorCopies.states c) q :=
  Placement.placed (PrefixWidthCopies.program q c) (placement src c)

theorem active_input (src : Fin t) (c : ℕ) (dim : Tapes t q) (xs : List Bool)
    (hh : dim.head src = 1) (ht : dim.tape src = RadixZeroFill.encodedBinary xs) :
    Placement.active (placement src c) (dim.append (PrefixWidthCopies.blankBank q (tapeCount c))) =
      PrefixWidthCopies.input q c xs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [slots,Tapes.append,BinaryDescriptorCopies.single,hh,ht,
      PrefixWidthCopies.blankBank]

theorem active_output (src : Fin t) (c : ℕ) (dim : Tapes t q) (xs : List Bool)
    (hh : dim.head src = 1) (ht : dim.tape src = RadixZeroFill.encodedBinary xs) :
    Placement.active (placement src c) (dim.append (PrefixCounterInit.input c (fun _ => xs))) =
      PrefixWidthCopies.output q c xs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [slots,Tapes.append,BinaryDescriptorCopies.single,hh,ht]

private theorem extra_before (src : Fin t) (c : ℕ) (i : Fin (t-1)) :
    (placement src c (Fin.natAdd (1+tapeCount c) i)).val < t := by
  by_contra h
  have hle : t ≤ (placement src c (Fin.natAdd (1+tapeCount c) i)).val := Nat.le_of_not_gt h
  let j : Fin (tapeCount c) := ⟨(placement src c (Fin.natAdd (1+tapeCount c) i)).val-t,
    by have hb := (placement src c (Fin.natAdd (1+tapeCount c) i)).isLt; omega⟩
  have he : placement src c (Fin.natAdd (1+tapeCount c) i) = slots src c (Fin.natAdd 1 j) := by
    apply Fin.ext
    simp only [slots,Fin.addCases_right,Fin.val_natAdd,j]
    omega
  have hv := congrArg Fin.val ((placement src c).injective (he.trans (placement_active src c _).symm))
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

theorem extra_unchanged (src : Fin t) (c : ℕ) (dim : Tapes t q)
    (v w : Tapes (tapeCount c) q) :
    Placement.extra (placement src c) (dim.append v) =
      Placement.extra (placement src c) (dim.append w) := by
  have he (i : Fin (t-1)) : placement src c (Fin.natAdd (1+tapeCount c) i) =
      Fin.castAdd (tapeCount c) ⟨_,extra_before src c i⟩ := Fin.ext rfl
  apply congrArg₂ Tapes.mk <;> funext i <;>
    rw [he i] <;>
    simp only [Tapes.append,Fin.addCases_left]

theorem copies_hoare (src : Fin t) (c : ℕ) (dim : Tapes t q) (xs : List Bool)
    (hh : dim.head src = 1) (ht : dim.tape src = RadixZeroFill.encodedBinary xs) :
    HoareTime (program q src c)
      (fun v => v = dim.append (PrefixWidthCopies.blankBank q (tapeCount c)))
      (fun v => v = dim.append (PrefixCounterInit.input c (fun _ => xs)))
      (c*(2*xs.length+6)) := by
  have h := Placement.hoare_at (PrefixWidthCopies.copies_hoare q c xs) (placement src c)
    (dim.append (PrefixWidthCopies.blankBank q (tapeCount c))) (active_input src c dim xs hh ht)
  apply h.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_unchanged src c dim _ (PrefixCounterInit.input c (fun _ => xs)),
    ← active_output src c dim xs hh ht]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.PrefixWidthCopiesAt
