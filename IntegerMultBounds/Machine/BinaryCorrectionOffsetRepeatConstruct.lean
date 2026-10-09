import IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatData
import IntegerMultBounds.Machine.BinaryCorrectionOffsetPlaced
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructBudget

/-! Complete correction-offset repetition from original b/q/n/P/H/L and the
original control word. The exchanged width/range metadata uses the existing
physical descriptor constructor; all private storage is erased on return. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatConstruct
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatHeaders
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryCorrectionOffsetRepeatData
noncomputable section

def controlBank (Z : List Bool) : Tapes 1 0 := ⟨fun _ => 0,fun _ => word Z⟩
def headerInput (hs : Fin 6 → List Bool) (Z : List Bool) :=
  (BinaryAddressOffsetRepeatHeaders.input hs).append (controlBank Z)
def headerOutput (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ) :=
  (BinaryAddressOffsetRepeatHeaders.output hs b q n P H).append (controlBank Z)

def baseFocus : Fin 5 → Fin 19 := ![0,1,2,18,7]
theorem base_injective : Function.Injective baseFocus := by decide
def repeatFocus : Fin 6 → Fin 45 := ![7,9,6,5,8,11]
theorem repeat_injective : Function.Injective repeatFocus := by decide

def originals (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 1,hs 2]
def descriptors (hs : Fin 6 → List Bool) (q b n P H : ℕ) : Fin 4 → List Bool :=
  ![widthBits q n,hs 5,rangeBits b n,repeatBits q n P H]

def input (hs : Fin 6 → List Bool) (Z : List Bool) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryCorrectionOffsetPlaced.input (headerInput hs Z))
def headerBank (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryCorrectionOffsetPlaced.input (headerOutput hs Z q b n P H))
def baseCaller (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryCorrectionOffsetPlaced.input (BinaryCorrectionOffsetPlaced.result
    (headerOutput hs Z q b n P H) baseFocus q b n Z hb hbq)
def baseBank (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (baseCaller hs Z q b n P H hb hbq)
def repeatedBank (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryAddressOffsetRepeatPlaced.result
    (baseCaller hs Z q b n P H hb hbq) repeatFocus (destination q b n L ((P*H)*2^(n*q)) Z hb hbq))

def cleanupSlots : List (Fin 50) := [6,8,11]
def cleanupBits (q b n P H : ℕ) : Fin 50 → List Bool :=
  fun i => if i=6 then widthBits q n else if i=8 then rangeBits b n else if i=11 then repeatBits q n P H else []
def output (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryDescriptorCleanupList.cleared cleanupSlots (repeatedBank hs Z q b n P H L hb hbq)

def headerProgram := extend (extend (extend BinaryAddressOffsetRepeatHeaders.program 1) 26) 5
def baseProgram := extend (BinaryCorrectionOffsetPlaced.program (a := 0) baseFocus base_injective) 5
def repeatProgram := BinaryAddressOffsetRepeatPlaced.program 0 repeatFocus repeat_injective
def cleanupProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<50) cleanupSlots
def program := seq (seq (seq headerProgram baseProgram) repeatProgram) cleanupProgram

theorem mapTape_zero (f : ℤ → Fin 4) : StreamedFiberTranslationAlphabet.mapTape (a := 0) f=f := by
  funext j
  change (StreamedFiberTranslationAlphabet.encoding (a := 0)).encode (f j)=f j
  generalize f j=x
  fin_cases x <;> rfl

theorem header_hoare (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ)
    (hb : 0<b) (hq : 0<q) (hH : 0<H)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b)
    (hvn : Counter.value (hs 2)=n) (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime headerProgram (fun z => z=input hs Z) (fun z => z=headerBank hs Z q b n P H)
      (BinaryAddressOffsetRepeatHeaders.cost b q n P H) := by
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (BinaryAddressOffsetRepeatHeaders.constructs hs b q n P H hq hb hH hvb hvq hvn hvP hvH hc)
    (controlBank Z)) (FixedHeaderBankCopy.empty 26)) (FixedHeaderBankCopy.empty 5)

theorem base_hoare (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime baseProgram (fun z => z=headerBank hs Z q b n P H) (fun z => z=baseBank hs Z q b n P H hb hbq)
      (BinaryCorrectionOffset.constant*(2^(n*b)*BinaryCorrectionOffset.allowance q b n)) := by
  have ht : ∀ i, (headerOutput hs Z q b n P H).tape (baseFocus i)=BinaryCorrectionOffsetPlaced.tapes (originals hs) Z i := by
    intro i
    fin_cases i <;> simp only [BinaryCorrectionOffsetPlaced.tapes,mapTape_zero] <;> rfl
  have h := BinaryCorrectionOffsetPlaced.runs (headerOutput hs Z q b n P H)
    baseFocus base_injective (originals hs) q b n Z hb hbq hvq hvb hvn
    (by intro i; fin_cases i <;> exact hc _) hZ ht (by intro i; fin_cases i <;> rfl)
  exact hoare_extend_eq h (FixedHeaderBankCopy.empty 5)

theorem repeat_hoare (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvL : Counter.value (hs 5)=L) (hZ : Z.length=n) :
    HoareTime repeatProgram (fun z => z=baseBank hs Z q b n P H hb hbq)
      (fun z => z=repeatedBank hs Z q b n P H L hb hbq)
      (BinaryAddressOffsetRepeat.cost (n*q) L (2^(n*b)) ((P*H)*2^(n*q)) (descriptors hs q b n P H)) := by
  have ht : ∀ i, (baseCaller hs Z q b n P H hb hbq).tape (repeatFocus i)=
      BinaryAddressOffsetRepeatPlaced.tapes (word (offsets q b n Z hb hbq).flatten) (fun _ => blank)
        (descriptors hs q b n P H) i := by
    intro i
    rw [offsets_flatten q b n Z hb hbq hZ]
    fin_cases i
    · exact mapTape_zero _
    all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  have hh : ∀ i, (baseCaller hs Z q b n P H hb hbq).head (repeatFocus i)=BinaryAddressOffsetRepeatPlaced.heads i := by
    intro i; fin_cases i <;> rfl
  have h := BinaryAddressOffsetRepeatPlaced.runs (baseCaller hs Z q b n P H hb hbq)
    repeatFocus repeat_injective (offsets q b n Z hb hbq) (n*q) L ((P*H)*2^(n*q))
    (offsets_uniform q b n Z hb hbq hZ) (descriptors hs q b n P H)
    (DimensionProductDescriptor.bits_value n q) hvL
    (by simpa [offsets,descriptors,rangeBits] using FixedBasePowerDescriptor.result_value 2 (n*b))
    (DimensionProductDescriptor.bits_value (P*H) (2^(n*q))) ht hh
  simpa only [repeatProgram,baseBank,repeatedBank,destination,offsets,List.length_map,List.length_range] using h

theorem cleanup_hoare (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    HoareTime cleanupProgram (fun z => z=repeatedBank hs Z q b n P H L hb hbq)
      (fun z => z=output hs Z q b n P H L hb hbq)
      (BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)) := by
  apply BinaryDescriptorCleanupList.cleanup_hoare (by decide) cleanupSlots (by decide)
  intro i hi
  simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl <;> constructor <;> first | rfl |
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

def cost (hs : Fin 6 → List Bool) (q b n P H L : ℕ) :=
  BinaryAddressOffsetRepeatHeaders.cost b q n P H+
  BinaryCorrectionOffset.constant*(2^(n*b)*BinaryCorrectionOffset.allowance q b n)+
  BinaryAddressOffsetRepeat.cost (n*q) L (2^(n*b)) ((P*H)*2^(n*q)) (descriptors hs q b n P H)+
  BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)+3

theorem constructs (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hH : 0<H)
    (hvq : Counter.value (hs 1)=q) (hvb : Counter.value (hs 0)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n P H L hb hbq)
      (cost hs q b n P H L) := by
  have h0 := (header_hoare hs Z q b n P H hb (by omega) hH hvq hvb hvn hvP hvH hc).seq
    (base_hoare hs Z q b n P H hb hbq hvq hvb hvn hc hZ)
  have h1 := h0.seq (repeat_hoare hs Z q b n P H L hb hbq hvL hZ)
  have h2 := h1.seq (cleanup_hoare hs Z q b n P H L hb hbq)
  exact h2.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem output_eq (hs : Fin 6 → List Bool) (Z : List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    output hs Z q b n P H L hb hbq=setTape (input hs Z) (9 : Fin 50)
      (word (destination q b n L ((P*H)*2^(n*q)) Z hb hbq)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetRepeatConstruct
