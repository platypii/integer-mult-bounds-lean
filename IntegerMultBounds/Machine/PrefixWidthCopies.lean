import IntegerMultBounds.Machine.BinaryDescriptorCopies
import IntegerMultBounds.Machine.PrefixCounterInit

/-! Replicate one width descriptor into the actual prefix-field initializer
bank. Every output field, clock, and final spare remains wholly blank. -/
namespace IntegerMultBounds.Machine.PrefixWidthCopies
open PrefixCounterInit (tapeCount)
noncomputable section
variable {q : ℕ}

def descriptorSlot : (c : ℕ) → Fin c → Fin (tapeCount c)
  | 0, i => Fin.elim0 i
  | c+1, i => Fin.cases (Fin.castAdd (tapeCount c) (2 : Fin 3))
      (fun j => Fin.natAdd 3 (descriptorSlot c j)) i

@[simp] theorem descriptorSlot_zero (c : ℕ) :
    descriptorSlot (c+1) 0 = Fin.castAdd (tapeCount c) (2 : Fin 3) := rfl
@[simp] theorem descriptorSlot_succ (c : ℕ) (i : Fin c) :
    descriptorSlot (c+1) i.succ = Fin.natAdd 3 (descriptorSlot c i) := rfl

theorem descriptorSlot_val (c : ℕ) (i : Fin c) : (descriptorSlot c i).val = 3*i.val+2 := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => simp only [descriptorSlot_succ,Fin.val_natAdd,ih,Fin.val_succ]; omega

theorem descriptorSlot_injective (c : ℕ) : Function.Injective (descriptorSlot c) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [descriptorSlot_val,descriptorSlot_val] at hv
  apply Fin.ext
  omega

theorem input_descriptor (c : ℕ) (bs : Fin c → List Bool) (i : Fin c) :
    (PrefixCounterInit.input (q := q) c bs).head (descriptorSlot c i) = 1 ∧
    (PrefixCounterInit.input (q := q) c bs).tape (descriptorSlot c i) = RadixZeroFill.encodedBinary (bs i) := by
  induction c with
  | zero => exact Fin.elim0 i
  | succ c ih =>
    induction i using Fin.cases with
    | zero => exact ⟨rfl,rfl⟩
    | succ i => simpa only [PrefixCounterInit.input,descriptorSlot_succ,Tapes.append,Fin.addCases_right] using ih (fun j => bs j.succ) i

theorem input_frame (c : ℕ) (bs : Fin c → List Bool) (i : Fin (tapeCount c))
    (hi : ∀ j, i ≠ descriptorSlot c j) :
    (PrefixCounterInit.input (q := q) c bs).head i = 0 ∧
    (PrefixCounterInit.input (q := q) c bs).tape i = fun _ => blank := by
  induction c with
  | zero => exact ⟨rfl,rfl⟩
  | succ c ih =>
    induction i using Fin.addCases with
    | left i =>
      have hn := hi 0
      fin_cases i
      · exact ⟨rfl,rfl⟩
      · exact ⟨rfl,rfl⟩
      · exact (hn rfl).elim
    | right i =>
      simp only [PrefixCounterInit.input,Tapes.append,Fin.addCases_right]
      apply ih (fun j => bs j.succ) i
      intro j hj
      exact hi j.succ (congrArg (Fin.natAdd 3) hj)

def blankBank (q t : ℕ) : Tapes t q := ⟨fun _ => 0,fun _ _ => blank⟩

def input (q c : ℕ) (xs : List Bool) : Tapes (1+tapeCount c) q :=
  (BinaryDescriptorCopies.single q xs).append (blankBank q (tapeCount c))
def output (q c : ℕ) (xs : List Bool) : Tapes (1+tapeCount c) q :=
  (BinaryDescriptorCopies.single q xs).append (PrefixCounterInit.input c (fun _ => xs))

def slots (c : ℕ) : Fin (c+1) → Fin (1+tapeCount c) :=
  Fin.cases (Fin.castAdd (tapeCount c) (0 : Fin 1)) (fun i => Fin.natAdd 1 (descriptorSlot c i))

theorem slots_injective (c : ℕ) : Function.Injective (slots c) := by
  intro i j h
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j => have hv := congrArg Fin.val h; simp [slots] at hv; omega
  | succ i =>
    induction j using Fin.cases with
    | zero => have hv := congrArg Fin.val h; simp [slots] at hv
    | succ j =>
      apply congrArg Fin.succ
      apply descriptorSlot_injective c
      exact Fin.ext (by have hv := congrArg Fin.val h; simpa [slots] using hv)

def placement (c : ℕ) : Fin ((c+1)+(2*c+1)) ≃ Fin (1+tapeCount c) :=
  InjectivePlacement.placement (slots c) (slots_injective c) (by rw [PrefixCounterInit.tapeCount_eq]; omega)

@[simp] theorem placement_active (c : ℕ) (i : Fin (c+1)) :
    placement c (Fin.castAdd (2*c+1) i) = slots c i :=
  InjectivePlacement.active_slot _ _ _ _

def program (q c : ℕ) : Program (1+tapeCount c) (BinaryDescriptorCopies.states c) q :=
  Placement.placed (BinaryDescriptorCopies.program q c) (placement c)

theorem active_input (q c : ℕ) (xs : List Bool) :
    Placement.active (placement c) (input q c xs) = BinaryDescriptorCopies.input q c xs := by
  rw [BinaryDescriptorCopies.input_layout]
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.cases <;>
    simp [slots,input,Tapes.append,BinaryDescriptorCopies.single,blankBank]

theorem active_output (q c : ℕ) (xs : List Bool) :
    Placement.active (placement c) (output q c xs) = BinaryDescriptorCopies.output q c xs := by
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.cases with
    | zero => simp [slots,output,Tapes.append,BinaryDescriptorCopies.single]
    | succ i =>
      simpa [Placement.active,slots,output,Tapes.append,BinaryDescriptorCopies.output] using
        (input_descriptor (q := q) c (fun _ => xs) i).1
  · funext i
    induction i using Fin.cases with
    | zero => simp [slots,output,Tapes.append,BinaryDescriptorCopies.single]
    | succ i =>
      simpa [Placement.active,slots,output,Tapes.append,BinaryDescriptorCopies.output] using
        (input_descriptor (q := q) c (fun _ => xs) i).2

private theorem extra_not_selected (c : ℕ) (i : Fin (2*c+1)) (j : Fin (c+1)) :
    placement c (Fin.natAdd (c+1) i) ≠ slots c j := by
  intro h
  have hh := (placement c).injective (h.trans (placement_active c j).symm)
  have hv := congrArg Fin.val hh
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

theorem extra_unchanged (q c : ℕ) (xs : List Bool) :
    Placement.extra (placement c) (input q c xs) = Placement.extra (placement c) (output q c xs) := by
  have hf (i : Fin (2*c+1)) :
      (input q c xs).head (placement c (Fin.natAdd (c+1) i)) =
        (output q c xs).head (placement c (Fin.natAdd (c+1) i)) ∧
      (input q c xs).tape (placement c (Fin.natAdd (c+1) i)) =
        (output q c xs).tape (placement c (Fin.natAdd (c+1) i)) := by
    generalize he : placement c (Fin.natAdd (c+1) i) = k
    induction k using Fin.addCases with
    | left k => fin_cases k; simp [input,output,Tapes.append]
    | right k =>
      have hh := input_frame (q := q) c (fun _ => xs) k (by
        intro j hj
        apply extra_not_selected c i j.succ
        rw [he,hj]
        rfl)
      simpa only [input,output,Tapes.append,Fin.addCases_right,blankBank] using And.intro hh.1.symm hh.2.symm
  apply congrArg₂ Tapes.mk
  · funext i; exact (hf i).1
  · funext i; exact (hf i).2

theorem copies_hoare (q c : ℕ) (xs : List Bool) :
    HoareTime (program q c) (fun v => v = input q c xs) (fun v => v = output q c xs)
      (c*(2*xs.length+6)) := by
  have hh := Placement.hoare_at (BinaryDescriptorCopies.copies_hoare q c xs) (placement c)
    (input q c xs) (active_input q c xs)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [Placement.replace,extra_unchanged,← active_output q c xs]
  exact Placement.view _ _

end
end IntegerMultBounds.Machine.PrefixWidthCopies
