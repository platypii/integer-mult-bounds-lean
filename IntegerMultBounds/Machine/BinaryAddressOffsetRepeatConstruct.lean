import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatHeaders
import IntegerMultBounds.Machine.BinaryAddressOffsetPlaced
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatPlaced
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatValue

/-! The complete repeated parity-offset constructor starts with only the six
original dimension descriptors. All derived counts and the base address table
are constructed, copied, rewound, and erased by fixed-control programs. -/
namespace IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstruct
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatHeaders
open BinaryAddressOffsetRepeatData
noncomputable section

def baseFocus : Fin 4 → Fin 18 := ![0,1,2,7]
theorem base_injective : Function.Injective baseFocus := by decide

def repeatFocus : Fin 6 → Fin 44 := ![7,9,6,5,8,11]
theorem repeat_injective : Function.Injective repeatFocus := by decide

def originals (hs : Fin 6 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 1,hs 2]
def descriptors (hs : Fin 6 → List Bool) (q b n P H : ℕ) : Fin 4 → List Bool :=
  ![widthBits b n,hs 5,rangeBits q n,repeatBits b n P H]

def input (hs : Fin 6 → List Bool) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryAddressOffsetPlaced.input (BinaryAddressOffsetRepeatHeaders.input hs))
def headerBank (hs : Fin 6 → List Bool) (q b n P H : ℕ) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryAddressOffsetPlaced.input (BinaryAddressOffsetRepeatHeaders.output hs q b n P H))
def baseCaller (hs : Fin 6 → List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetPlaced.input (BinaryAddressOffsetPlaced.result
    (BinaryAddressOffsetRepeatHeaders.output hs q b n P H) baseFocus q b n hb hbq)
def baseBank (hs : Fin 6 → List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (baseCaller hs q b n P H hb hbq)
def repeatedBank (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryAddressOffsetRepeatPlaced.result
    (baseCaller hs q b n P H hb hbq) repeatFocus (destination q b n L ((P*H)*2^(n*b)) hb hbq))

def cleanupSlots : List (Fin 49) := [6,8,11]
def cleanupBits (q b n P H : ℕ) : Fin 49 → List Bool :=
  fun i => if i=6 then widthBits b n else if i=8 then rangeBits q n else if i=11 then repeatBits b n P H else []
def output (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryDescriptorCleanupList.cleared cleanupSlots (repeatedBank hs q b n P H L hb hbq)

def headerProgram := extend (extend BinaryAddressOffsetRepeatHeaders.program 26) 5
def baseProgram := extend (BinaryAddressOffsetPlaced.program baseFocus base_injective) 5
def repeatProgram := BinaryAddressOffsetRepeatPlaced.program 0 repeatFocus repeat_injective
def cleanupProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<49) cleanupSlots
def program := seq (seq (seq headerProgram baseProgram) repeatProgram) cleanupProgram

theorem header_hoare (hs : Fin 6 → List Bool) (q b n P H : ℕ)
    (hb : 0<b) (hq : 0<q) (hH : 0<H)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b)
    (hvn : Counter.value (hs 2)=n) (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime headerProgram (fun z => z=input hs) (fun z => z=headerBank hs q b n P H)
      (BinaryAddressOffsetRepeatHeaders.cost q b n P H) := by
  exact hoare_extend_eq (hoare_extend_eq
    (BinaryAddressOffsetRepeatHeaders.constructs hs q b n P H hb hq hH hvq hvb hvn hvP hvH hc)
    (FixedHeaderBankCopy.empty 26)) (FixedHeaderBankCopy.empty 5)

theorem base_hoare (hs : Fin 6 → List Bool) (q b n P H : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime baseProgram (fun z => z=headerBank hs q b n P H) (fun z => z=baseBank hs q b n P H hb hbq)
      (BinaryAddressOffset.constant*(2^(n*q)*BinaryAddressOffset.allowance q b n)) := by
  have h := BinaryAddressOffsetPlaced.runs (BinaryAddressOffsetRepeatHeaders.output hs q b n P H)
    baseFocus base_injective (originals hs) q b n hb hbq hvq hvb hvn
    (by intro i; fin_cases i <;> exact hc _)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  exact hoare_extend_eq h (FixedHeaderBankCopy.empty 5)

theorem repeat_hoare (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvL : Counter.value (hs 5)=L) :
    HoareTime repeatProgram (fun z => z=baseBank hs q b n P H hb hbq)
      (fun z => z=repeatedBank hs q b n P H L hb hbq)
      (BinaryAddressOffsetRepeat.cost (n*b) L (2^(n*q)) ((P*H)*2^(n*b)) (descriptors hs q b n P H)) := by
  have ht : ∀ i, (baseCaller hs q b n P H hb hbq).tape (repeatFocus i)=
      BinaryAddressOffsetRepeatPlaced.tapes
        (BinaryAddressOffsetRepeatAlphabet.word (offsets q b n hb hbq).flatten) (fun _ => blank)
        (descriptors hs q b n P H) i := by
    intro i
    rw [BinaryAddressOffsetRepeatValue.offsets_flatten]
    fin_cases i <;> first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  have hh : ∀ i, (baseCaller hs q b n P H hb hbq).head (repeatFocus i)=BinaryAddressOffsetRepeatPlaced.heads i := by
    intro i; fin_cases i <;> rfl
  have h := BinaryAddressOffsetRepeatPlaced.runs (baseCaller hs q b n P H hb hbq)
    repeatFocus repeat_injective (offsets q b n hb hbq) (n*b) L ((P*H)*2^(n*b))
    (BinaryAddressOffsetRepeatValue.offsets_uniform q b n hb hbq) (descriptors hs q b n P H)
    (DimensionProductDescriptor.bits_value n b) hvL
    (by simpa [offsets,descriptors,rangeBits] using FixedBasePowerDescriptor.result_value 2 (n*q))
    (DimensionProductDescriptor.bits_value (P*H) (2^(n*b))) ht hh
  simpa only [repeatProgram,baseBank,repeatedBank,destination,offsets,List.length_map,List.length_range] using h

theorem cleanup_hoare (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    HoareTime cleanupProgram (fun z => z=repeatedBank hs q b n P H L hb hbq)
      (fun z => z=output hs q b n P H L hb hbq)
      (BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)) := by
  apply BinaryDescriptorCleanupList.cleanup_hoare (by decide) cleanupSlots (by decide)
  intro i hi
  simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl <;> constructor <;> first | rfl |
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

def cost (hs : Fin 6 → List Bool) (q b n P H L : ℕ) :=
  BinaryAddressOffsetRepeatHeaders.cost q b n P H+
  BinaryAddressOffset.constant*(2^(n*q)*BinaryAddressOffset.allowance q b n)+
  BinaryAddressOffsetRepeat.cost (n*b) L (2^(n*q)) ((P*H)*2^(n*b)) (descriptors hs q b n P H)+
  BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n P H)+3

theorem constructs (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hH : 0<H)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvP : Counter.value (hs 3)=P) (hvH : Counter.value (hs 4)=H) (hvL : Counter.value (hs 5)=L)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun z => z=input hs) (fun z => z=output hs q b n P H L hb hbq)
      (cost hs q b n P H L) := by
  have h0 := (header_hoare hs q b n P H hb (by omega) hH hvq hvb hvn hvP hvH hc).seq
    (base_hoare hs q b n P H hb hbq hvq hvb hvn hc)
  have h1 := h0.seq (repeat_hoare hs q b n P H L hb hbq hvL)
  have h2 := h1.seq (cleanup_hoare hs q b n P H L hb hbq)
  exact h2.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- Six original headers survive; the destination is the actual repeated word;
every other tape is blank and every private head has returned to zero. -/
theorem output_eq (hs : Fin 6 → List Bool) (q b n P H L : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    output hs q b n P H L hb hbq=setTape (input hs) (9 : Fin 49)
      (BinaryAddressOffsetRepeatAlphabet.word (destination q b n L ((P*H)*2^(n*b)) hb hbq)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstruct
