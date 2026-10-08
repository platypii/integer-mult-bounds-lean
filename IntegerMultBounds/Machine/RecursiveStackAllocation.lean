import IntegerMultBounds.Machine.RecursiveChildCallSetup
import IntegerMultBounds.Machine.RoleArrayCall

/-! Recursive stack allocation from blank suffixes. Each physical push moves
its head past its writes, leaving a blank suffix for every subsequent nested
frame. These invariants discharge finite free-interval premises without a
runtime allocation oracle or a bound on recursion depth. -/
namespace IntegerMultBounds.Machine.RecursiveStackAllocation
open SharedPlacementAlphabet (setTape)
variable {t a k : ℕ}

/-- The stack head points at its first free cell. Older cells are unrestricted. -/
def Available (slot : Fin t) (v : Tapes t a) : Prop :=
  ∀ z, v.head slot ≤ z → v.tape slot z = blank

theorem blank_available (slot : Fin t) (v : Tapes t a)
    (h : v.tape slot = fun _ => blank) : Available slot v := by
  intro z _
  rw [h]

theorem available_frame (slot : Fin t) (v w : Tapes t a)
    (hh : w.head slot = v.head slot) (ht : w.tape slot = v.tape slot)
    (hv : Available slot v) : Available slot w := by
  simpa only [Available,hh,ht] using hv

theorem descriptor_free (stack : Fin t) (ops : List (BinaryDescriptorFrames.Slot stack))
    (xs : Fin t → List Bool) (v : Tapes t a) (hv : Available stack v) :
    BinaryDescriptorFrames.Free stack ops xs v := fun z hz _ => hv z hz

theorem descriptor_saved (stack : Fin t) (ops : List (BinaryDescriptorFrames.Slot stack))
    (xs : Fin t → List Bool) (v : Tapes t a) (hv : Available stack v) :
    Available stack (BinaryDescriptorFrames.saved stack ops xs v) := by
  intro z hz
  rw [BinaryDescriptorFrames.saved_head] at hz
  rw [BinaryDescriptorFrames.saved_outside stack ops xs v z (Or.inr hz)]
  exact hv z (le_trans (le_add_of_nonneg_right (Int.natCast_nonneg _)) hz)

theorem payload_free (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (n : ℕ) (v : Tapes t a) (hv : Available L.stack v) :
    RoleArrayFrames.Free L ops n v := fun z hz _ => hv z hz

theorem payload_saved (L : RoleArrayFrames.Layout t) (ops : List (RoleArrayFrames.Role L))
    (n : ℕ) (v : Tapes t a) (hv : Available L.stack v) :
    Available L.stack (RoleArrayFrames.saved L ops n v) := by
  intro z hz
  rw [RoleArrayFrames.saved_head] at hz
  rw [RoleArrayFrames.saved_outside L ops n v z (Or.inr hz)]
  exact hv z (le_trans (le_add_of_nonneg_right (Int.natCast_nonneg _)) hz)

theorem pc_free (slot : Fin t) (v : Tapes t a) (hv : Available slot v) :
    ∀ j < k, v.tape slot (v.head slot+j) = blank := by
  intro j _
  exact hv _ (by omega)

theorem pc_pushed (slot : Fin t) (code : FiniteReturnStack.Code k)
    (v : Tapes t a) (hv : Available slot v) :
    Available slot (FiniteReturnStackAt.pushed slot code v) := by
  intro z hz
  simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self] at hz ⊢
  rw [FiniteReturnStack.wordPart,dite_eq_right (by omega)]
  exact hv z (by omega)

/-- Parking and destructive movement leave the payload stack ready for the
next recursive call, irrespective of the depth or parked data. -/
theorem child_payload_available (L : RoleArrayFrames.Layout t)
    (ops : List (RoleArrayFrames.Role L)) (src dst : RoleArrayFrames.Role L)
    (n : ℕ) (v : Tapes t a) (hv : Available L.stack v) :
    Available L.stack (RoleArrayCall.entered L ops src dst n v) := by
  have h := payload_saved L ops n v hv
  simpa [Available,RoleArrayCall.entered,RoleArrayCall.slots,RoleArrayMove.moved,setTape,
    src.property.1.symm,dst.property.1.symm] using h

open RecursiveChildCallSetup in
/-- Actual header/PC saving preserves both free suffixes, so repeated child
preparation needs no externally supplied stack-capacity bound. -/
theorem saved_stacks_available (hs : Fin 6 → List Bool) (stackBank : Tapes 2 a)
    (code : FiniteReturnStack.Code k)
    (hd : Available 0 stackBank) (hp : Available 1 stackBank) :
    Available 0 (savedStacks hs stackBank code) ∧ Available 1 (savedStacks hs stackBank code) := by
  have hd0 : Available descriptorStack (bank hs stackBank) := hd
  have hp0 : Available pcStack (bank hs stackBank) := hp
  have hd1 := descriptor_saved descriptorStack fields (words hs) (bank hs stackBank) hd0
  have hp1 := available_frame pcStack (bank hs stackBank)
    (BinaryDescriptorFrames.saved descriptorStack fields (words hs) (bank hs stackBank))
    (BinaryDescriptorFrames.saved_frame descriptorStack fields (words hs) (bank hs stackBank)
      pcStack (by decide)).1
    (BinaryDescriptorFrames.saved_frame descriptorStack fields (words hs) (bank hs stackBank)
      pcStack (by decide)).2 hp0
  let v := BinaryDescriptorFrames.saved descriptorStack fields (words hs) (bank hs stackBank)
  have hframe := FiniteReturnStackAt.pushed_frame pcStack descriptorStack (by decide) code v
  have hd2 := available_frame descriptorStack v (FiniteReturnStackAt.pushed pcStack code v)
    hframe.1 hframe.2 hd1
  have hp2 := pc_pushed pcStack code v hp1
  unfold Available savedStacks
  dsimp only
  rw [show Fin.natAdd 38 (0 : Fin 2) = descriptorStack by rfl,
    show Fin.natAdd 38 (1 : Fin 2) = pcStack by rfl]
  exact ⟨hd2,hp2⟩

end IntegerMultBounds.Machine.RecursiveStackAllocation
