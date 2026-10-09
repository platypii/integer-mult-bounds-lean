import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructAlphabet
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatCoordinates

/-! Arbitrary caller placement of the complete repeated-offset constructor.
Seven shared tapes hold q/b/n/P/H/L and the blank destination. The 42 appended
private tapes are all restored blank; every caller spectator is preserved. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructPlaced
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryAddressOffsetRepeatData
variable {t a : ℕ}
noncomputable section

def roles : Fin 49 ≃ Fin (7+42) where
  toFun := fun i => ⟨if i.val<6 then i.val else if i.val=9 then 6 else if i.val<9 then i.val+1 else i.val, by split_ifs <;> omega⟩
  invFun := fun i => ⟨if i.val<6 then i.val else if i.val=6 then 9 else if i.val<10 then i.val-1 else i.val, by split_ifs <;> omega⟩
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def embed (focus : Fin 7 → Fin t) : Fin (7+42) → Fin (t+42) :=
  Fin.addCases (fun i => Fin.castAdd 42 (focus i)) (Fin.natAdd t)

theorem embed_injective (focus : Fin 7 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (embed focus) := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [embed,Fin.addCases_left] at he
      exact congrArg (Fin.castAdd 42) (hf (Fin.castAdd_injective _ _ he))
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
      exact congrArg (Fin.natAdd 7) (Fin.ext (by omega))

def slot (focus : Fin 7 → Fin t) (i : Fin 49) := embed focus (roles i)
theorem slot_injective (focus : Fin 7 → Fin t) (hf : Function.Injective focus) : Function.Injective (slot focus) :=
  (embed_injective focus hf).comp roles.injective

theorem room (focus : Fin 7 → Fin t) (hf : Function.Injective focus) : 49+(t-7)=t+42 := by
  have hh := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at hh
  omega

def placement (focus : Fin 7 → Fin t) (hf : Function.Injective focus) : Fin (49+(t-7)) ≃ Fin (t+42) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf)

def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 42)
def tapes (hs : Fin 6 → List Bool) : Fin 7 → ℤ → Fin (a+4) :=
  ![CountedLoopReuseAlphabet.binary (hs 0),CountedLoopReuseAlphabet.binary (hs 1),
    CountedLoopReuseAlphabet.binary (hs 2),CountedLoopReuseAlphabet.binary (hs 3),
    CountedLoopReuseAlphabet.binary (hs 4),CountedLoopReuseAlphabet.binary (hs 5),fun _ => blank]
def heads : Fin 7 → ℤ := ![1,1,1,1,1,1,0]

theorem active_input (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 6 → List Bool) (ht : ∀ i, caller.tape (focus i)=tapes hs i)
    (hh : ∀ i, caller.head (focus i)=heads i) :
    Placement.active (placement focus hf) (input caller)=BinaryAddressOffsetRepeatConstructAlphabet.bank hs (fun _ => blank) := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,hh,heads,Fin.addCases]
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,ht,tapes,Fin.addCases]

def result (caller : Tapes t a) (focus : Fin 7 → Fin t) (ys : List Bool) :=
  setTape caller (focus 6) (word ys) 0

def program (a : ℕ) (focus : Fin 7 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (BinaryAddressOffsetRepeatConstructAlphabet.program a) (placement focus hf)

theorem constructs (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hH : 0<H)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (focus i)=tapes hs i) (hh : ∀ i, caller.head (focus i)=heads i) :
    HoareTime (program a focus hf) (fun z => z=input caller)
      (fun z => z=input (result caller focus (destination q b n L ((P*H)*2^(n*b)) hb hbq)))
      (BinaryAddressOffsetRepeatConstruct.cost hs q b n P H L) := by
  have ha := active_input caller focus hf hs ht hh
  have hp := Placement.hoare_at
    (BinaryAddressOffsetRepeatConstructAlphabet.constructs hs q b n P H L hb hbq hH hvq hvb hvn hvP hvH hvL hc)
    (placement focus hf) (input caller) ha
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [BinaryAddressOffsetRepeatConstructAlphabet.output_eq,←ha,PlacedDescriptorConstruction.replace_setTape]
  have hslot : placement focus hf (Fin.castAdd (t-7) (9 : Fin 49))=Fin.castAdd 42 (focus 6) := by
    rw [placement,InjectivePlacement.active_slot]
    simp [slot,embed,roles,Fin.addCases]
  rw [hslot]
  exact SharedPlacementAlphabet.setTape_append_left caller (FixedHeaderBankCopy.empty 42) (focus 6) _ 0

theorem constructs_volume (caller : Tapes t a) (focus : Fin 7 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 6 → List Bool) (q b n P H L B : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hP : 0<P) (hH : 0<H) (hL : 0<L)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (focus i)=tapes hs i) (hh : ∀ i, caller.head (focus i)=heads i)
    (hB : BinaryAddressOffset.allowance q b n≤B) :
    HoareTime (program a focus hf) (fun z => z=input caller)
      (fun z => z=input (result caller focus (destination q b n L ((P*H)*2^(n*b)) hb hbq)))
      (BinaryAddressOffsetRepeatConstructBudget.constant*BinaryAddressOffsetRepeatConstructBudget.volume q b n P H L B) :=
  (constructs caller focus hf hs q b n P H L hb hbq hH hvq hvb hvn hvP hvH hvL hc ht hh).consequence
    (fun _ h => h) (fun _ h => h)
    (BinaryAddressOffsetRepeatConstructBudget.cost_volume hs q b n P H L B hP hH hL hvL (hc 5) hB)

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructPlaced
