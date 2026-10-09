import IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatData
import IntegerMultBounds.Machine.BinaryPackedEarlyPrefixHeaders
import IntegerMultBounds.Machine.BinaryParityXorOffsetPlaced
import IntegerMultBounds.Machine.BinaryAddressOffsetRepeatConstructBudget

/-! Physical negative parity-XOR source-prefix table. Each current-source row
is repeated L times, and the whole table K times; all private storage is erased. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyPrefixNegative
open SharedPlacementAlphabet (setTape)
open BinaryAddressOffsetRepeatHeaders
open BinaryAddressOffsetHeaders (countBits)
open BinaryAddressOffsetRepeatAlphabet (word)
open BinaryParityXorOffsetRepeatData
noncomputable section

def headerInput := BinaryPackedEarlyPrefixHeaders.input
def headerOutput := BinaryPackedEarlyPrefixHeaders.output

def baseFocus : Fin 5 → Fin 19 := ![0,1,2,18,7]
theorem base_injective : Function.Injective baseFocus := by decide
def repeatFocus : Fin 6 → Fin 45 := ![7,8,6,16,4,17]
theorem repeat_injective : Function.Injective repeatFocus := by decide

def originals (hs : Fin 5 → List Bool) : Fin 3 → List Bool := ![hs 0,hs 1,hs 2]
def descriptors (hs : Fin 5 → List Bool) (q b n : ℕ) : Fin 4 → List Bool :=
  ![widthBits b n,hs 3,rangeBits q n,hs 4]

def input (hs : Fin 5 → List Bool) (Z : List Bool) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryParityXorOffsetPlaced.input (headerInput hs Z))
def headerBank (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryParityXorOffsetPlaced.input (headerOutput hs Z q b n))
def baseCaller (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryParityXorOffsetPlaced.input (BinaryParityXorOffsetPlaced.result
    (headerOutput hs Z q b n) baseFocus q b n Z hb hbq)
def baseBank (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (baseCaller hs Z q b n hb hbq)
def repeatedBank (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryAddressOffsetRepeatPlaced.input (BinaryAddressOffsetRepeatPlaced.result
    (baseCaller hs Z q b n hb hbq) repeatFocus (destination q b n L K Z hb hbq))

def cleanupSlots : List (Fin 50) := [3,4,5,6]
def cleanupBits (q b n : ℕ) : Fin 50 → List Bool :=
  fun i => if i=3 then widthBits q n else if i=4 then rangeBits q n else if i=5 then countBits q n else if i=6 then widthBits b n else []

def output (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryDescriptorCleanupList.cleared cleanupSlots (repeatedBank hs Z q b n L K hb hbq)

def headerProgram := extend (extend BinaryPackedEarlyPrefixHeaders.program 26) 5
def baseProgram := extend (BinaryParityXorOffsetPlaced.program (a := 0) baseFocus base_injective) 5
def repeatProgram := BinaryAddressOffsetRepeatPlaced.program 0 repeatFocus repeat_injective
def cleanupProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<50) cleanupSlots
def program := seq (seq (seq headerProgram baseProgram) repeatProgram) cleanupProgram

theorem mapTape_zero (f : ℤ → Fin 4) : StreamedFiberTranslationAlphabet.mapTape (a := 0) f=f := by
  funext j
  change (StreamedFiberTranslationAlphabet.encoding (a := 0)).encode (f j)=f j
  generalize f j=x
  fin_cases x <;> rfl

theorem header_hoare (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ)
    (hb : 0<b) (hq : 0<q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b)
    (hvn : Counter.value (hs 2)=n) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime headerProgram (fun z => z=input hs Z) (fun z => z=headerBank hs Z q b n)
      (BinaryPackedEarlyPrefixHeaders.cost q b n) := by
  exact hoare_extend_eq (hoare_extend_eq
    (BinaryPackedEarlyPrefixHeaders.constructs hs Z q b n hq hb hvq hvb hvn hc)
    (FixedHeaderBankCopy.empty 26)) (FixedHeaderBankCopy.empty 5)

theorem base_hoare (hs : Fin 5 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime baseProgram (fun z => z=headerBank hs Z q b n) (fun z => z=baseBank hs Z q b n hb hbq)
      (BinaryParityXorOffset.constant*(2^(n*q)*BinaryParityXorOffset.allowance q b n)) := by
  have ht : ∀ i, (headerOutput hs Z q b n).tape (baseFocus i)=BinaryParityXorOffsetPlaced.tapes (originals hs) Z i := by
    intro i
    fin_cases i <;> simp only [BinaryParityXorOffsetPlaced.tapes,mapTape_zero] <;> rfl
  have h := BinaryParityXorOffsetPlaced.runs (headerOutput hs Z q b n)
    baseFocus base_injective (originals hs) q b n Z hb hbq hvq hvb hvn
    (by intro i; fin_cases i <;> exact hc _) hZ ht (by intro i; fin_cases i <;> rfl)
  exact hoare_extend_eq h (FixedHeaderBankCopy.empty 5)

theorem repeat_hoare (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K) :
    HoareTime repeatProgram (fun z => z=baseBank hs Z q b n hb hbq)
      (fun z => z=repeatedBank hs Z q b n L K hb hbq)
      (BinaryAddressOffsetRepeat.cost (n*b) L (2^(n*q)) K (descriptors hs q b n)) := by
  have ht : ∀ i, (baseCaller hs Z q b n hb hbq).tape (repeatFocus i)=
      BinaryAddressOffsetRepeatPlaced.tapes (word (offsets q b n Z hb hbq).flatten) (fun _ => blank)
        (descriptors hs q b n) i := by
    intro i
    rw [offsets_flatten q b n Z hb hbq]
    fin_cases i
    · exact mapTape_zero _
    all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _
  have hh : ∀ i, (baseCaller hs Z q b n hb hbq).head (repeatFocus i)=BinaryAddressOffsetRepeatPlaced.heads i := by
    intro i; fin_cases i <;> rfl
  have h := BinaryAddressOffsetRepeatPlaced.runs (baseCaller hs Z q b n hb hbq)
    repeatFocus repeat_injective (offsets q b n Z hb hbq) (n*b) L K
    (offsets_uniform q b n Z hb hbq) (descriptors hs q b n)
    (DimensionProductDescriptor.bits_value n b) hvL
    (by simpa [offsets,BinaryParityXorOffsetData.rows,descriptors,rangeBits] using FixedBasePowerDescriptor.result_value 2 (n*q))
    hvK ht hh
  simpa only [repeatProgram,baseBank,repeatedBank,destination,offsets,BinaryParityXorOffsetData.rows,List.length_map,List.length_range] using h

theorem cleanup_hoare (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    HoareTime cleanupProgram (fun z => z=repeatedBank hs Z q b n L K hb hbq)
      (fun z => z=output hs Z q b n L K hb hbq)
      (BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n)) := by
  apply BinaryDescriptorCleanupList.cleanup_hoare (by decide) cleanupSlots (by decide)
  intro i hi
  simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> first | rfl |
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

def cost (hs : Fin 5 → List Bool) (q b n L K : ℕ) :=
  BinaryPackedEarlyPrefixHeaders.cost q b n+
  BinaryParityXorOffset.constant*(2^(n*q)*BinaryParityXorOffset.allowance q b n)+
  BinaryAddressOffsetRepeat.cost (n*b) L (2^(n*q)) K (descriptors hs q b n)+
  BinaryDescriptorCleanupList.cost cleanupSlots (cleanupBits q b n)+3

theorem constructs (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 0)=q) (hvb : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (hvL : Counter.value (hs 3)=L) (hvK : Counter.value (hs 4)=K)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=input hs Z) (fun z => z=output hs Z q b n L K hb hbq)
      (cost hs q b n L K) := by
  have h0 := (header_hoare hs Z q b n hb (by omega) hvq hvb hvn hc).seq
    (base_hoare hs Z q b n hb hbq hvq hvb hvn hc hZ)
  have h1 := h0.seq (repeat_hoare hs Z q b n L K hb hbq hvL hvK)
  have h2 := h1.seq (cleanup_hoare hs Z q b n L K hb hbq)
  exact h2.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem output_eq (hs : Fin 5 → List Bool) (Z : List Bool) (q b n L K : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    output hs Z q b n L K hb hbq=setTape (input hs Z) (8 : Fin 50)
      (word (destination q b n L K Z hb hbq)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.BinaryPackedEarlyPrefixNegative
