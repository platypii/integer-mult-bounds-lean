import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatAlphabet
import IntegerMultBounds.Machine.PlacementBank

/-! Caller-owned source/destination and four original repetition descriptors
are shared directly. Exactly five private tapes are appended, initialized and
returned blank; the source table is physically erased and spectators survive. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPlaced
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryAddressOffsetRepeatData
variable {t a : ℕ}
noncomputable section

def roles : Fin 11 ≃ Fin (6+5) where
  toFun := ![0,1,6,7,2,8,3,9,4,10,5]
  invFun := ![0,1,4,6,8,10,2,3,5,7,9]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def embed (focus : Fin 6 → Fin t) : Fin (6+5) → Fin (t+5) :=
  Fin.addCases (fun i => Fin.castAdd 5 (focus i)) (Fin.natAdd t)

theorem embed_injective (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (embed focus) := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [embed,Fin.addCases_left] at he
      exact congrArg (Fin.castAdd 5) (hf (Fin.castAdd_injective _ _ he))
    | right j =>
      have hh := congrArg Fin.val he
      simp only [embed,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hh
      have hi := (focus i).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hh := congrArg Fin.val he
      simp only [embed,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hh
      have hj := (focus j).isLt
      omega
    | right j =>
      simp only [embed,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hh
      exact congrArg (Fin.natAdd 6) (Fin.ext (by omega))

def slot (focus : Fin 6 → Fin t) (i : Fin 11) := embed focus (roles i)
theorem slot_injective (focus : Fin 6 → Fin t) (hf : Function.Injective focus) : Function.Injective (slot focus) :=
  (embed_injective focus hf).comp roles.injective

theorem room (focus : Fin 6 → Fin t) (hf : Function.Injective focus) : 11+(t-6)=t+5 := by
  have hh := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at hh
  omega

def placement (focus : Fin 6 → Fin t) (hf : Function.Injective focus) : Fin (11+(t-6)) ≃ Fin (t+5) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf)

def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 5)
def tapes (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool) : Fin 6 → ℤ → Fin (a+4) :=
  ![source,dest,CountedLoopReuseAlphabet.binary (hs 0),CountedLoopReuseAlphabet.binary (hs 1),
    CountedLoopReuseAlphabet.binary (hs 2),CountedLoopReuseAlphabet.binary (hs 3)]
def heads : Fin 6 → ℤ := ![0,0,1,1,1,1]

theorem active_input (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (source dest : ℤ → Fin (a+4)) (hs : Fin 4 → List Bool)
    (ht : ∀ i, caller.tape (focus i)=tapes source dest hs i) (hh : ∀ i, caller.head (focus i)=heads i) :
    Placement.active (placement focus hf) (input caller)=BinaryAddressOffsetRepeatAlphabet.bank source dest hs := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,hh,heads,Fin.addCases]
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,ht,tapes,Fin.addCases]

def result (caller : Tapes t a) (focus : Fin 6 → Fin t) (ys : List Bool) :=
  setTape (setTape caller (focus 0) (fun _ => blank) 0) (focus 1) (word ys) 0

theorem replaced (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (xs ys : List Bool) (hs : Fin 4 → List Bool)
    (ht : ∀ i, caller.tape (focus i)=tapes (word xs) (fun _ => blank) hs i)
    (hh : ∀ i, caller.head (focus i)=heads i) :
    Placement.replace (placement focus hf) (input caller)
      (BinaryAddressOffsetRepeatAlphabet.bank (fun _ => blank) (word ys) hs)=input (result caller focus ys) := by
  have hslot0 : slot focus 0=Fin.castAdd 5 (focus 0) := by simp [slot,embed,roles,Fin.addCases]
  have hslot1 : slot focus 1=Fin.castAdd 5 (focus 1) := by simp [slot,embed,roles,Fin.addCases]
  apply Placement.Tapes.ext'
  · intro j
    by_cases hj : ∃ i, slot focus i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [show placement focus hf=InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf) from rfl,
        InjectivePlacement.replace_head_slot]
      fin_cases i <;> simp [input,result,setTape,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,
        hh,heads,Fin.addCases,hf.eq_iff,BinaryAddressOffsetRepeatAlphabet.bank]
    · have hn : ∀ i, slot focus i≠j := fun i he => hj ⟨i,he⟩
      have h0 : j≠Fin.castAdd 5 (focus 0) := by rw [←hslot0]; exact (hn 0).symm
      have h1 : j≠Fin.castAdd 5 (focus 1) := by rw [←hslot1]; exact (hn 1).symm
      rw [show placement focus hf=InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf) from rfl,
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hn]
      simp only [input,result]
      rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]
      simp [setTape,h0,h1]
  · intro j
    by_cases hj : ∃ i, slot focus i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [show placement focus hf=InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf) from rfl,
        InjectivePlacement.replace_tape_slot]
      fin_cases i <;> simp [input,result,setTape,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,
        ht,tapes,Fin.addCases,hf.eq_iff,BinaryAddressOffsetRepeatAlphabet.bank]
    · have hn : ∀ i, slot focus i≠j := fun i he => hj ⟨i,he⟩
      have h0 : j≠Fin.castAdd 5 (focus 0) := by rw [←hslot0]; exact (hn 0).symm
      have h1 : j≠Fin.castAdd 5 (focus 1) := by rw [←hslot1]; exact (hn 1).symm
      rw [show placement focus hf=InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf) from rfl,
        InjectivePlacement.replace_tape_other _ _ _ _ _ _ hn]
      simp only [input,result]
      rw [←SharedPlacementAlphabet.setTape_append_left,←SharedPlacementAlphabet.setTape_append_left]
      simp [setTape,h0,h1]

def program (a : ℕ) (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (BinaryAddressOffsetRepeatAlphabet.program a) (placement focus hf)

theorem runs (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (blocks : List (List Bool)) (W L K : ℕ) (hu : BlockRotationData.Uniform W blocks)
    (hs : Fin 4 → List Bool) (hw : Counter.value (hs 0)=W) (hl : Counter.value (hs 1)=L)
    (hn : Counter.value (hs 2)=blocks.length) (hk : Counter.value (hs 3)=K)
    (ht : ∀ i, caller.tape (focus i)=tapes (word blocks.flatten) (fun _ => blank) hs i)
    (hh : ∀ i, caller.head (focus i)=heads i) :
    HoareTime (program a focus hf) (fun z => z=input caller)
      (fun z => z=input (result caller focus (copies (expanded blocks L) K)))
      (BinaryAddressOffsetRepeat.cost W L blocks.length K hs) := by
  have hrun := BinaryAddressOffsetRepeatAlphabet.runs (a := a) blocks W L K hu hs hw hl hn hk
  have hp := Placement.hoare_at hrun (placement focus hf) (input caller)
    (active_input caller focus hf _ _ hs ht hh)
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact replaced caller focus hf blocks.flatten (copies (expanded blocks L) K) hs ht hh

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPlaced
