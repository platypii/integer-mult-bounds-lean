import IntegerMultBounds.Machine.BinaryCorrectionOffset
import IntegerMultBounds.Machine.PlacementBank
import IntegerMultBounds.Machine.PackedOffsetPayloadAlphabet

/-! Place the complete third-line correction producer using only caller-owned b/q/n, original controls
and one blank destination. All 26 appended private tapes are returned blank. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetPlaced
open SharedPlacementAlphabet (setTape)
variable {a t : ℕ}
open StreamedFiberTranslationAlphabet (encoding mapTape)
noncomputable section

def roles : Fin 31 ≃ Fin (5+26) where
  toFun := ![0,1,2,5,6,7,8,9,10,11,12,13,14,15,4,16,3,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![0,1,2,16,14,3,4,5,6,7,8,9,10,11,12,13,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def embed (focus : Fin 5 → Fin t) : Fin (5+26) → Fin (t+26) :=
  Fin.addCases (fun i => Fin.castAdd 26 (focus i)) (Fin.natAdd t)

theorem embed_injective (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :
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
      exact congrArg (Fin.natAdd 5) (Fin.ext (by omega))

def slot (focus : Fin 5 → Fin t) (i : Fin 31) := embed focus (roles i)
theorem slot_injective (focus : Fin 5 → Fin t) (hf : Function.Injective focus) : Function.Injective (slot focus) :=
  (embed_injective focus hf).comp roles.injective

theorem room (focus : Fin 5 → Fin t) (hf : Function.Injective focus) : 31+(t-5)=t+26 := by
  have hh := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at hh
  omega

def placement (focus : Fin 5 → Fin t) (hf : Function.Injective focus) : Fin (31+(t-5)) ≃ Fin (t+26) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (room focus hf)

def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 26)
def tapes (hs : Fin 3 → List Bool) (Z : List Bool) : Fin 5 → ℤ → Fin (a+4) :=
  ![mapTape (BinaryAddressOffsetHeaders.binary (hs 0)),mapTape (BinaryAddressOffsetHeaders.binary (hs 1)),
    mapTape (BinaryAddressOffsetHeaders.binary (hs 2)),mapTape (putWord (fun _ => blank) 0 (Z.map bitSymbol)),fun _ => blank]
def heads : Fin 5 → ℤ := ![1,1,1,0,0]

theorem active_input (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 3 → List Bool) (Z : List Bool) (ht : ∀ i, caller.tape (focus i)=tapes hs Z i)
    (hh : ∀ i, caller.head (focus i)=heads i) :
    Placement.active (placement focus hf) (input caller)=Alphabet.mapTapes (encoding (a := a)) (BinarySelectedOffset.input hs Z) := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,hh,heads,Fin.addCases,
      BinaryAddressOffsetHeaders.bank,BinarySelectedOffsetPrepare.input,BinarySelectedOffsetPrepare.controls,BinarySelectedOffset.input]
  · funext i; fin_cases i <;> simp [input,slot,embed,roles,Tapes.append,FixedHeaderBankCopy.empty,ht,tapes,Fin.addCases,
      BinaryAddressOffsetHeaders.bank,BinarySelectedOffsetPrepare.input,BinarySelectedOffsetPrepare.controls,BinarySelectedOffset.input,encoding] <;> rfl

theorem original_header (hs : Fin 3 → List Bool) (Z : List Bool) (i : Fin 3) :
    tapes (a := a) hs Z (Fin.castAdd 2 i)=RadixZeroFill.encodedBinary (hs i) := by
  fin_cases i <;> rfl

theorem output_word (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :
    mapTape (a := a) (BinaryCorrectionOffsetRow.word (BinaryCorrectionOffsetData.word q b n Z hb hbq))=
      putWord (fun _ => blank) 0 ((BinaryCorrectionOffsetData.word q b n Z hb hbq).map bitSymbol) :=
  PackedOffsetPayloadAlphabet.map_bits (fun _ => blank) 0 _

def result (caller : Tapes t a) (focus : Fin 5 → Fin t) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape caller (focus 4) (mapTape (BinaryCorrectionOffsetRow.word (BinaryCorrectionOffsetData.word q b n Z hb hbq))) 0

def program (focus : Fin 5 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (Alphabet.program (encoding (a := a)) BinaryCorrectionOffset.program) (placement focus hf)

theorem runs (caller : Tapes t a) (focus : Fin 5 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 3 → List Bool) (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (ht : ∀ i, caller.tape (focus i)=tapes hs Z i) (hh : ∀ i, caller.head (focus i)=heads i) :
    HoareTime (program focus hf) (fun z => z=input caller)
      (fun z => z=input (result caller focus q b n Z hb hbq))
      (BinaryCorrectionOffset.constant*(2^(n*b)*BinaryCorrectionOffset.allowance q b n)) := by
  have ha := active_input caller focus hf hs Z ht hh
  have hm := Alphabet.map_hoare (encoding (a := a))
    (BinaryCorrectionOffset.constructs hs q b n Z hb hbq hvq hvb hvn hc hZ)
  have hl : HoareTime (Alphabet.program (encoding (a := a)) BinaryCorrectionOffset.program)
      (fun z => z=Alphabet.mapTapes (encoding (a := a)) (BinarySelectedOffset.input hs Z))
      (fun z => z=Alphabet.mapTapes (encoding (a := a)) (BinaryCorrectionOffset.output hs Z q b n hb hbq))
      (BinaryCorrectionOffset.constant*(2^(n*b)*BinaryCorrectionOffset.allowance q b n)) := by
    refine hm.consequence ?_ ?_ le_rfl
    · rintro z rfl; exact ⟨_,rfl,rfl⟩
    · rintro z ⟨small,rfl,rfl⟩; rfl
  have hp := Placement.hoare_at hl
    (placement focus hf) (input caller) ha
  have he : Alphabet.mapTapes (encoding (a := a)) (BinaryCorrectionOffset.output hs Z q b n hb hbq)=
      setTape (Alphabet.mapTapes (encoding (a := a)) (BinarySelectedOffset.input hs Z)) (14 : Fin 31) (mapTape (BinaryCorrectionOffsetRow.word (BinaryCorrectionOffsetData.word q b n Z hb hbq))) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply hp.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [he,←ha,PlacedDescriptorConstruction.replace_setTape]
  have hslot : placement focus hf (Fin.castAdd (t-5) (14 : Fin 31))=Fin.castAdd 26 (focus 4) := by
    rw [placement,InjectivePlacement.active_slot]
    simp [slot,embed,roles,Fin.addCases]
  rw [hslot]
  exact SharedPlacementAlphabet.setTape_append_left caller (FixedHeaderBankCopy.empty 26) (focus 4) _ 0

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetPlaced
