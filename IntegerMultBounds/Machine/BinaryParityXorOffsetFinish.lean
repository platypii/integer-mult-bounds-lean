import IntegerMultBounds.Machine.BinaryParityXorOffsetPrepare
import IntegerMultBounds.Machine.BinaryParityXorOffsetValue

/-! Physically construct the row width, negate each independently reset
row, then erase the full address table, repeated controls and every generated
descriptor. Only original q/b/n, original controls, and negative parity-XOR output remain. -/
namespace IntegerMultBounds.Machine.BinaryParityXorOffsetFinish
open SharedPlacementAlphabet (setTape)
open BinaryParityXorOffsetData
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits binary)
noncomputable section

def widthWord (b n : ℕ) := DimensionProductDescriptor.bits n b

def widthPlace : Fin (6+25) ≃ Fin 31 where
  toFun := ![11,10,12,1,13,2,0,3,4,5,6,7,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![6,3,5,7,8,9,10,11,12,13,1,0,2,4,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def negatePlace : Fin (7+24) ≃ Fin 31 where
  toFun := ![8,14,11,12,10,13,4,0,1,2,3,5,6,7,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![7,8,9,10,6,11,12,13,0,14,4,2,3,5,1,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def widthBank (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape (BinaryParityXorOffsetPrepare.output hs Z q b n hb hbq) 10 (binary (widthWord b n)) 1
def negated (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape (setTape (widthBank hs Z q b n hb hbq) 8 (fun _ => blank) 0)
    14 (BinaryParityXorOffsetRow.word (word q b n Z hb hbq)) 0

def cleanSource (v : Tapes 31 0) := setTape v 6 (fun _ => blank) 0
def cleanControls (v : Tapes 31 0) := setTape v 7 (fun _ => blank) 0
def headerSlots : List (Fin 31) := [3,4,5,10]
def headerWords (q b n : ℕ) : Fin 31 → List Bool := fun i =>
  if i=3 then widthBits q n else if i=4 then rangeBits q n else if i=5 then countBits q n else if i=10 then widthWord b n else []
def output (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryDescriptorCleanupList.cleared headerSlots (cleanControls (cleanSource (negated hs Z q b n hb hbq)))

def widthProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) widthPlace
def negateProgram := Placement.placed BinaryParityXorOffsetNegate.program negatePlace
def sourceProgram := WordBankCleanup.clearProgram (6 : Fin 31) (by decide) 0
def controlsProgram := WordBankCleanup.clearProgram (7 : Fin 31) (by decide) 0
def headersProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<31) headerSlots
def cleanup := seq (seq sourceProgram controlsProgram) headersProgram
def program := seq (seq widthProgram negateProgram) cleanup

theorem width_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (cq : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime widthProgram (fun z => z=BinaryParityXorOffsetPrepare.output hs Z q b n hb hbq)
      (fun z => z=widthBank hs Z q b n hb hbq) (53*(n*b)+28) := by
  have ha : Placement.active widthPlace (BinaryParityXorOffsetPrepare.output hs Z q b n hb hbq)=
      DimensionProductDescriptor.input (hs 1) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at (DimensionProductDescriptor.construct_hoare (hs 1) (hs 2) n b (by omega)
    hvq hvn cq cn) widthPlace _ ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem negate_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) :
    HoareTime negateProgram (fun z => z=widthBank hs Z q b n hb hbq)
      (fun z => z=negated hs Z q b n hb hbq)
      (BinaryParityXorOffsetNegate.cost (n*b) (2^(n*q)) (widthWord b n) (rangeBits q n)) := by
  have h := BinaryParityXorOffsetNegate.runs (rows q b n Z hb hbq) (n*b) (rows_uniform q b n Z hb hbq)
    (widthWord b n) (rangeBits q n) (DimensionProductDescriptor.bits_value n b)
    (by simpa [rows,rangeBits] using FixedBasePowerDescriptor.result_value 2 (n*q))
  rw [BinaryParityXorOffsetValue.rows_flatten q b n Z hb hbq hZ] at h
  simp only [rows,List.length_map,List.length_range] at h
  have ha : Placement.active negatePlace (widthBank hs Z q b n hb hbq)=
      BinaryParityXorOffsetNegate.raw (BinaryParityXorOffsetRow.word (positiveWord q b n Z hb hbq))
        (fun _ => blank) 0 0 (widthWord b n) (rangeBits q n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h negatePlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleanup_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    HoareTime cleanup (fun z => z=negated hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq)
      (2*((n*2^(n*q))*q)+2*(n*2^(n*q))+BinaryDescriptorCleanupList.cost headerSlots (headerWords q b n)+8) := by
  let v := negated hs Z q b n hb hbq
  have h0 := WordBankCleanup.clear_hoare v (6 : Fin 31) (by decide)
    ((BinarySelectedOffsetData.source q n).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  have he0 : WordBankCleanup.write v 6 (fun _ => blank)=cleanSource v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he0] at h0
  have h1 := WordBankCleanup.clear_hoare (cleanSource v) (7 : Fin 31) (by decide)
    ((BinarySelectedOffsetData.controls q n Z).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  have he1 : WordBankCleanup.write (cleanSource v) 7 (fun _ => blank)=cleanControls (cleanSource v) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he1] at h1
  have h2 := BinaryDescriptorCleanupList.cleanup_hoare (by decide : 0<31) headerSlots (by decide)
    (headerWords q b n) (cleanControls (cleanSource v)) (by
      intro i hi
      simp only [headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> first | rfl |
        exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h)
    (by simp only [List.length_map,BinarySelectedOffsetData.source_length,BinarySelectedOffsetData.controls_length q n Z hZ]; omega)

def cost (q b n : ℕ) := 53*(n*b)+28+
  BinaryParityXorOffsetNegate.cost (n*b) (2^(n*q)) (widthWord b n) (rangeBits q n)+
  2*((n*2^(n*q))*q)+2*(n*2^(n*q))+BinaryDescriptorCleanupList.cost headerSlots (headerWords q b n)+10

theorem finishes (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=b) (hvn : Counter.value (hs 2)=n)
    (cq : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=BinaryParityXorOffsetPrepare.output hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq) (cost q b n) := by
  have h0 := (width_hoare hs Z q b n hb hbq hvq hvn cq cn).seq (negate_hoare hs Z q b n hb hbq hZ)
  exact (h0.seq (cleanup_hoare hs Z q b n hb hbq hZ)).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem output_eq (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    output hs Z q b n hb hbq=setTape (BinaryParityXorOffsetPrepare.input hs Z) (14 : Fin 31)
      (BinaryParityXorOffsetRow.word (word q b n Z hb hbq)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.BinaryParityXorOffsetFinish
