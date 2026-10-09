import IntegerMultBounds.Machine.BinaryCorrectionOffsetPrepare
import IntegerMultBounds.Machine.BinaryCorrectionOffsetValue

/-! Physically construct the row width, subtract each independently reset
row, then erase the full address table, repeated controls and every generated
descriptor. Only original b/q/n, original controls, and correction output remain. -/
namespace IntegerMultBounds.Machine.BinaryCorrectionOffsetFinish
open SharedPlacementAlphabet (setTape)
open BinaryCorrectionOffsetData
open BinaryAddressOffsetHeaders (widthBits rangeBits countBits binary)
noncomputable section

def widthWord (q n : ℕ) := DimensionProductDescriptor.bits n q

def widthPlace : Fin (6+25) ≃ Fin 31 where
  toFun := ![11,10,12,1,13,2,0,3,4,5,6,7,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![6,3,5,7,8,9,10,11,12,13,1,0,2,4,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def subtractPlace : Fin (9+22) ≃ Fin 31 where
  toFun := ![9,8,14,11,12,13,10,15,4,0,1,2,3,5,6,7,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  invFun := ![9,10,11,12,8,13,14,15,1,0,6,3,4,5,2,7,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def widthBank (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape (BinaryCorrectionOffsetPrepare.output hs Z q b n hb hbq) 10 (binary (widthWord q n)) 1
def subtracted (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  setTape (setTape (setTape (widthBank hs Z q b n hb hbq) 9 (fun _ => blank) 0) 8 (fun _ => blank) 0)
    14 (BinaryCorrectionOffsetRow.word (word q b n Z hb hbq)) 0

def cleanSource (v : Tapes 31 0) := setTape v 6 (fun _ => blank) 0
def cleanControls (v : Tapes 31 0) := setTape v 7 (fun _ => blank) 0
def headerSlots : List (Fin 31) := [3,4,5,10]
def headerWords (q b n : ℕ) : Fin 31 → List Bool := fun i =>
  if i=3 then widthBits b n else if i=4 then rangeBits b n else if i=5 then countBits b n else if i=10 then widthWord q n else []
def output (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :=
  BinaryDescriptorCleanupList.cleared headerSlots (cleanControls (cleanSource (subtracted hs Z q b n hb hbq)))

def widthProgram := Placement.placed (DimensionProductDescriptor.program (q := 0)) widthPlace
def subtractProgram := Placement.placed BinaryCorrectionOffsetSubtract.program subtractPlace
def sourceProgram := WordBankCleanup.clearProgram (6 : Fin 31) (by decide) 0
def controlsProgram := WordBankCleanup.clearProgram (7 : Fin 31) (by decide) 0
def headersProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0<31) headerSlots
def cleanup := seq (seq sourceProgram controlsProgram) headersProgram
def program : Program 31 157 0 := seq (seq widthProgram subtractProgram) cleanup

theorem width_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvn : Counter.value (hs 2)=n)
    (cq : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) :
    HoareTime widthProgram (fun z => z=BinaryCorrectionOffsetPrepare.output hs Z q b n hb hbq)
      (fun z => z=widthBank hs Z q b n hb hbq) (53*(n*q)+28) := by
  have ha : Placement.active widthPlace (BinaryCorrectionOffsetPrepare.output hs Z q b n hb hbq)=
      DimensionProductDescriptor.input (hs 1) (hs 2) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := Placement.hoare_at (DimensionProductDescriptor.construct_hoare (hs 1) (hs 2) n q (by omega)
    hvq hvn cq cn) widthPlace _ ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem subtract_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hZ : Z.length=n) :
    HoareTime subtractProgram (fun z => z=widthBank hs Z q b n hb hbq)
      (fun z => z=subtracted hs Z q b n hb hbq)
      (BinaryCorrectionOffsetSubtract.cost (n*q) (2^(n*b)) (widthWord q n) (rangeBits b n)) := by
  have h := BinaryCorrectionOffsetSubtract.runs (rows q b n Z hb hbq) (n*q) (rows_uniform q b n Z hb hbq hZ)
    (widthWord q n) (rangeBits b n) (DimensionProductDescriptor.bits_value n q)
    (by simpa [rows,rangeBits] using FixedBasePowerDescriptor.result_value 2 (n*b))
  rw [left_rows q b n Z hb hbq hZ,right_rows q b n Z hb hbq hZ] at h
  simp only [rows,List.length_map,List.length_range] at h
  have ha : Placement.active subtractPlace (widthBank hs Z q b n hb hbq)=
      BinaryCorrectionOffsetSubtract.raw (BinaryCorrectionOffsetRow.word (controlWord q b n Z hb hbq))
        (BinaryCorrectionOffsetRow.word (BinarySelectedOffsetData.word q b n hb hbq Z)) (fun _ => blank)
        0 0 0 (widthWord q n) (rangeBits b n) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply (Placement.hoare_at h subtractPlace _ ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem cleanup_hoare (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) :
    HoareTime cleanup (fun z => z=subtracted hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq)
      (2*((n*2^(n*b))*b)+2*(n*2^(n*b))+BinaryDescriptorCleanupList.cost headerSlots (headerWords q b n)+8) := by
  let v := subtracted hs Z q b n hb hbq
  have h0 := WordBankCleanup.clear_hoare v (6 : Fin 31) (by decide)
    ((BinarySelectedOffsetData.source b n).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
  have he0 : WordBankCleanup.write v 6 (fun _ => blank)=cleanSource v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he0] at h0
  have h1 := WordBankCleanup.clear_hoare (cleanSource v) (7 : Fin 31) (by decide)
    ((BinarySelectedOffsetData.controls b n Z).map bitSymbol) (ReturnOrigin.bits_nonblank _) rfl
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
    (by simp only [List.length_map,BinarySelectedOffsetData.source_length,BinarySelectedOffsetData.controls_length b n Z hZ]; omega)

def cost (q b n : ℕ) := 53*(n*q)+28+
  BinaryCorrectionOffsetSubtract.cost (n*q) (2^(n*b)) (widthWord q n) (rangeBits b n)+
  2*((n*2^(n*b))*b)+2*(n*2^(n*b))+BinaryDescriptorCleanupList.cost headerSlots (headerWords q b n)+10

theorem finishes (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (hvq : Counter.value (hs 1)=q) (hvn : Counter.value (hs 2)=n)
    (cq : GrowingCounterData.Canonical (hs 1)) (cn : GrowingCounterData.Canonical (hs 2)) (hZ : Z.length=n) :
    HoareTime program (fun z => z=BinaryCorrectionOffsetPrepare.output hs Z q b n hb hbq)
      (fun z => z=output hs Z q b n hb hbq) (cost q b n) := by
  have h0 := (width_hoare hs Z q b n hb hbq hvq hvn cq cn).seq (subtract_hoare hs Z q b n hb hbq hZ)
  exact (h0.seq (cleanup_hoare hs Z q b n hb hbq hZ)).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem output_eq (hs : Fin 3 → List Bool) (Z : List Bool) (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) :
    output hs Z q b n hb hbq=setTape (BinaryCorrectionOffsetPrepare.input hs Z) (14 : Fin 31)
      (BinaryCorrectionOffsetRow.word (word q b n Z hb hbq)) 0 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.BinaryCorrectionOffsetFinish
