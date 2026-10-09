import IntegerMultBounds.Machine.BinaryPackedOffsetOriginalPlaced
import IntegerMultBounds.Machine.BinarySelectedOffsetRepeatPlaced
import IntegerMultBounds.Machine.BinaryRepeatedOffsetAction
import IntegerMultBounds.Machine.WordBankCleanup

/-! Physical selected-offset production, packed-field action and offset erasure
on one caller bank. The four action shape headers and six original generator
headers and retained control word are literal retained inputs; no offset word or action oracle is supplied.
Upstream reservation geometry construction remains a separate stage. -/
namespace IntegerMultBounds.Machine.BinarySelectedOffsetLoad
noncomputable section
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationPlacement (NativeTapes)
open BinarySelectedOffsetRepeatPlaced (tapes heads)

 def gen : Fin 8 → Fin 13 := ![6,7,8,9,10,11,12,4]
 theorem gen_injective : Function.Injective gen := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [gen] at h
 def base : Fin 6 → Fin 13 := fun i => Fin.castAdd 7 i
 def action : Fin 6 → Fin (13+42) := fun i => Fin.castAdd 42 (base i)
 theorem base_injective : Function.Injective base := by intro i j h; exact Fin.castAdd_injective _ _ h
 theorem action_injective : Function.Injective action := by intro i j h; exact base_injective (Fin.castAdd_injective _ _ h)
 def packed (q b n P H L : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) :=
  BinarySelectedOffsetRepeatData.destination q b n L ((P*H)*2^(n*q)) Z hb hbq
 def offset (caller : Tapes 13 prime) (V : List Bool) :=
  setTape caller 4 (BinaryAddressOffsetRepeatAlphabet.word V) 0
 def input (caller : Tapes 13 prime) :=
  CleanSubbank.bank (s := NativeTapes) (BinarySelectedOffsetRepeatPlaced.input caller)
 def prepare := extend (BinarySelectedOffsetRepeatPlaced.program prime gen gen_injective) NativeTapes
 def act := BinaryPackedOffsetOriginalPlaced.program action action_injective
 def offsetSlot : Fin ((13+42)+NativeTapes) := Fin.castAdd NativeTapes (Fin.castAdd 42 (4 : Fin 13))
 def clean := WordBankCleanup.clearProgram offsetSlot (by decide) prime
 def program := seq (seq prepare act) clean
 def cost (hs : Fin 6 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool) (q b n P H L B : ℕ)
    (hb : 1≤b) (hbq : b+1≤q) :=
  BinarySelectedOffsetRepeatConstruct.cost hs q b n P H L +
  BinaryPackedOffsetOriginalRun.cost P (n*q) (H*2^(n*b)*L) B shape +
  (2*(packed q b n P H L Z hb hbq).length+3)+2

 theorem store_ready (caller : Tapes 13 prime) (V : List Bool) {P N G B : ℕ}
    (x : Fin (RadixRangePadding.volume P N G B) → Bool) :
    BinaryPackedOffsetOriginalPlaced.store
      (BinarySelectedOffsetRepeatPlaced.input (offset caller V)) action x =
    BinarySelectedOffsetRepeatPlaced.input
      (offset (BinaryPackedOffsetOriginalPlaced.store caller base x) V) := by
  change setTape ((offset caller V).append (FixedHeaderBankCopy.empty 42))
    (Fin.castAdd 42 (5 : Fin 13)) _ 0 = _
  rw [SharedPlacementAlphabet.setTape_append_left]
  unfold BinarySelectedOffsetRepeatPlaced.input
  apply congrArg (fun v : Tapes 13 prime => v.append (FixedHeaderBankCopy.empty 42))
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [offset,BinaryPackedOffsetOriginalPlaced.store,base,setTape]

 theorem erase_ready (caller : Tapes 13 prime) (V : List Bool) {P N G B : ℕ}
    (x : Fin (RadixRangePadding.volume P N G B) → Bool)
    (ht : caller.tape 4=fun _ => blank) (hh : caller.head 4=0) :
    WordBankCleanup.write
      (input (offset (BinaryPackedOffsetOriginalPlaced.store caller base x) V)) offsetSlot
      (fun _ => blank) = input (BinaryPackedOffsetOriginalPlaced.store caller base x) := by
  let c := BinaryPackedOffsetOriginalPlaced.store caller base x
  have he : input (offset c V) = setTape (input c) offsetSlot
      (BinaryAddressOffsetRepeatAlphabet.word V) 0 := by
    unfold input CleanSubbank.bank BinarySelectedOffsetRepeatPlaced.input offsetSlot offset
    rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  have ht0 : (input c).tape offsetSlot=fun _ => blank := by
    change c.tape 4=fun _ => blank
    simpa [c,BinaryPackedOffsetOriginalPlaced.store,base,setTape] using ht
  have hh0 : (input c).head offsetSlot=0 := by
    change c.head 4=0
    simpa [c,BinaryPackedOffsetOriginalPlaced.store,base,setTape] using hh
  change WordBankCleanup.write (input (offset c V)) offsetSlot (fun _ => blank)=input c
  rw [he]
  rw [←ht0,←hh0]
  simp [WordBankCleanup.write,setTape]

 theorem runs (caller : Tapes 13 prime) (hs : Fin 6 → List Bool) (Z : List Bool) (shape : Fin 4 → List Bool)
    (q b n P H L B : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hP : 0<P) (hH : 0<H) (hL : 0<L) (hB : 0<B)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n)
    (ht : ∀ i, caller.tape (gen i)=tapes hs Z i) (hh : ∀ i, caller.head (gen i)=heads i)
    (hshape : BinaryAdjacentWidthHeadersShared.Sources (SharedBank.payload caller base)
      BinaryPackedOffsetOriginalRun.headers shape)
    (hvshape : ∀ i, Counter.value (shape i)=BinaryRadixRangePrepare.values P (H*2^(n*b)*L) B (n*q) i)
    (hcshape : ∀ i, GrowingCounterData.Canonical (shape i))
    (x : Fin (RadixRangePadding.volume P (2^(n*q)) (H*2^(n*b)*L) B) → Bool) :
    HoareTime program
      (fun z => z=input (BinaryPackedOffsetOriginalPlaced.store caller base x))
      (fun z => z=input (BinaryPackedOffsetOriginalPlaced.store caller base
        (BinaryPackedOffsetData.result (packed q b n P H L Z hb hbq) P (n*q) (H*2^(n*b)*L) B x)))
      (cost hs Z shape q b n P H L B hb hbq) := by
  let V := packed q b n P H L Z hb hbq
  have hgenT : ∀ i, (BinaryPackedOffsetOriginalPlaced.store caller base x).tape (gen i)=tapes hs Z i := by
    intro i; have hi := ht i; fin_cases i <;> simpa [BinaryPackedOffsetOriginalPlaced.store,base,gen,setTape] using hi
  have hgenH : ∀ i, (BinaryPackedOffsetOriginalPlaced.store caller base x).head (gen i)=heads i := by
    intro i; have hi := hh i; fin_cases i <;> simpa [BinaryPackedOffsetOriginalPlaced.store,base,gen,setTape] using hi
  have h0 := hoare_extend_eq (BinarySelectedOffsetRepeatPlaced.constructs
    (BinaryPackedOffsetOriginalPlaced.store caller base x) gen gen_injective hs Z q b n P H L
    hb hbq hH hvq hvb hvn hvP hvH hvL hc hZ hgenT hgenH) (SharedBank.empty NativeTapes prime)
  have hsrc : BinaryAdjacentWidthHeadersShared.Sources
      (SharedBank.payload (BinarySelectedOffsetRepeatPlaced.input (offset caller V)) action)
      BinaryPackedOffsetOriginalRun.headers shape := by
    constructor
    · intro i; have hi := hshape.tape i; fin_cases i <;>
        simpa [SharedBank.payload,BinarySelectedOffsetRepeatPlaced.input,offset,action,
          base,BinaryPackedOffsetOriginalRun.headers,setTape,Tapes.append] using hi
    · intro i; have hi := hshape.head i; fin_cases i <;>
        simpa [SharedBank.payload,BinarySelectedOffsetRepeatPlaced.input,offset,action,
          base,BinaryPackedOffsetOriginalRun.headers,setTape,Tapes.append] using hi
  have h1 := BinaryPackedOffsetOriginalPlaced.runs
    (BinarySelectedOffsetRepeatPlaced.input (offset caller V)) action action_injective
    V P (n*q) (H*2^(n*b)*L) B
    (BinarySelectedOffsetRepeatCoordinates.word_length q b n P H L Z hb hbq) hP
    (by positivity) hB shape hvshape hcshape hsrc rfl rfl x
  rw [store_ready,store_ready] at h1
  have h2 := WordBankCleanup.clear_hoare
    (input (offset (BinaryPackedOffsetOriginalPlaced.store caller base
      (BinaryPackedOffsetData.result V P (n*q) (H*2^(n*b)*L) B x)) V))
    offsetSlot (by decide) (V.map bitSymbol)
    (by intro z hz; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hz; cases z <;> decide) rfl
  rw [erase_ready _ V _ (by simpa [gen,tapes] using ht 7) (by simpa [gen,heads] using hh 7)] at h2
  exact ((h0.seq h1).seq h2).consequence
    (fun _ h => h) (fun _ h => h) (by simp only [List.length_map]; unfold cost; dsimp only [V]; omega)

end
end IntegerMultBounds.Machine.BinarySelectedOffsetLoad
