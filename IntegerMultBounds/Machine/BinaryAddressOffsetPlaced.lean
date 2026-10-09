import IntegerMultBounds.Machine.BinaryAddressOffset
import IntegerMultBounds.Machine.PlacementBank

/-! Place the complete parity-address producer using only caller-owned q/b/n
and one blank destination. All 26 appended private tapes are returned blank. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetPlaced
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}
noncomputable section

def roles : Fin 30 ≃ Fin (4+26) where
  toFun := ![0,1,2,4,5,6,7,8,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
  invFun := ![0,1,2,8,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def embed (focus : Fin 4 → Fin t) : Fin (4+26) → Fin (t+26) :=
  Fin.addCases (fun i => Fin.castAdd 26 (focus i)) (Fin.natAdd t)

theorem embed_injective (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (embed focus) := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [embed,Fin.addCases_left] at he
      exact congrArg (Fin.castAdd 26) (hf (Fin.castAdd_injective _ _ he))
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
      exact congrArg (Fin.natAdd 4) (Fin.ext (by omega))

def slot (focus : Fin 4 → Fin t) (i : Fin 30) := embed focus (roles i)
theorem slot_injective (focus : Fin 4 → Fin t) (hf : Function.Injective focus) : Function.Injective (slot focus) :=
  (embed_injective focus hf).comp roles.injective

theorem room (focus : Fin 4 → Fin t) (hf : Function.Injective focus) : 30+(t-4)=t+26 := by
  have hh := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at hh
  omega

def placement (focus : Fin 4 → Fin t) (hf : Function.Injective focus) : Fin (30+(t-4)) ≃ Fin (t+26) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf)

def input (caller : Tapes t 0) := caller.append (FixedHeaderBankCopy.empty 26)
def tapes (hs : Fin 3 → List Bool) : Fin 4 → ℤ → Fin 4 :=
  ![BinaryAddressOffsetHeaders.binary (hs 0),BinaryAddressOffsetHeaders.binary (hs 1),
    BinaryAddressOffsetHeaders.binary (hs 2),fun _ => blank]
def heads : Fin 4 → ℤ := ![1,1,1,0]

theorem active_input (caller : Tapes t 0) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 3 → List Bool) (ht : ∀ i, caller.tape (focus i)=tapes hs i)
    (hh : ∀ i, caller.head (focus i)=heads i) :
    Placement.active (placement focus hf) (input caller)=BinaryAddressOffset.input hs := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,hh,heads,Fin.addCases,
      BinaryAddressOffsetHeaders.bank]
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,ht,tapes,Fin.addCases,
      BinaryAddressOffsetHeaders.bank]

def result (caller : Tapes t 0) (focus : Fin 4 → Fin t) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape caller (focus 3) (BinaryAddressOffsetGather.outputTape q b n hb hbq) 0

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed BinaryAddressOffset.program (placement focus hf)

theorem runs (caller : Tapes t 0) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (focus i)=tapes hs i) (hh : ∀ i, caller.head (focus i)=heads i) :
    HoareTime (program focus hf) (fun z => z=input caller)
      (fun z => z=input (result caller focus q b n hb hbq))
      (BinaryAddressOffset.constant*(2^(n*q)*BinaryAddressOffset.allowance q b n)) := by
  have ha := active_input caller focus hf hs ht hh
  have hp := Placement.hoare_at (BinaryAddressOffset.constructs hs q b n hb hbq hvq hvb hvn hc)
    (placement focus hf) (input caller) ha
  have he : BinaryAddressOffset.output hs q b n hb hbq=
      setTape (BinaryAddressOffset.input hs) (8 : Fin 30) (BinaryAddressOffsetGather.outputTape q b n hb hbq) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [he,←ha,PlacedDescriptorConstruction.replace_setTape]
  have hslot : placement focus hf (Fin.castAdd (t-4) (8 : Fin 30))=Fin.castAdd 26 (focus 3) := by
    rw [placement,InjectivePlacement.active_slot]
    simp [slot,embed,roles,Fin.addCases]
  rw [hslot]
  exact SharedPlacementAlphabet.setTape_append_left caller (FixedHeaderBankCopy.empty 26) (focus 3) _ 0

end
end IntegerMultBounds.Machine.BinaryAddressOffsetPlaced
