import IntegerMultBounds.Machine.BinaryLengthInit
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
import IntegerMultBounds.Machine.DescriptorStackControl
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore

/-! An actual fixed length scanner reads an original canonical row-count word,
constructs its binary word-length descriptor on a blank tape and restores both
heads. No supplied logarithm or row-bit-width descriptor is used. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersLength
noncomputable section
open BinaryDescriptorCopy (source)
open MarkedWordCleanup (marked empty)
open DescriptorStackControl (seek positioned once after)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)

private theorem source_marker (xs : List Bool) : source xs 0=separator := by
  rw [BinaryDescriptorCopy.source,marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl
private theorem source_no_marker (xs : List Bool) (z : ℤ) (hz : 0<z) : source xs z≠separator := by
  by_cases hi : z<1+xs.length
  · have hm := ReturnOrigin.putWord_mem (a := 0) empty 1 (xs.map bitSymbol) z ⟨by omega,by simpa using hi⟩
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    change putWord empty 1 (xs.map bitSymbol) z≠separator
    rw [←hy]
    cases y <;> decide
  · rw [BinaryDescriptorCopy.source,marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [empty,show z≠0 by omega,blank,separator,Fin.ext_iff]
private theorem source_nonblank (xs : List Bool) (j : ℕ) (hj : j<xs.length) : source xs (1+j)≠blank := by
  have hm := ReturnOrigin.putWord_mem (a := 0) empty 1 (xs.map bitSymbol) (1+j) ⟨by omega,by simp; omega⟩
  obtain ⟨b,_,hb⟩ := List.mem_map.mp hm
  change putWord empty 1 (xs.map bitSymbol) (1+j)≠blank
  rw [←hb]
  cases b <;> decide
private theorem source_end (xs : List Bool) : source xs (1+xs.length)=blank := by
  rw [BinaryDescriptorCopy.source,marked,putWord_outside _ _ _ _ (Or.inr (by simp))]
  simp [empty,show (1+(xs.length:ℤ))≠0 by omega]

def rawInput (xs : List Bool) := BinaryLengthInit.blankBank (source xs) 1
def rawScanned (xs : List Bool) := BinaryLength.bank (source xs) (1+xs.length) (bits xs.length)
def rawOutput (xs : List Bool) := Copy.tapes (source xs) (source (bits xs.length)) 1 1

def right := once (t := 2) (a := 0) (by decide) (fun sy i => (sy i,if i=0 then Move.right else Move.stay))
def reset := seq (seek (t := 2) (a := 0) 0 separator Move.left) right
def rawProgram := seq BinaryLengthInit.program reset

theorem scans (xs : List Bool) :
    HoareTime BinaryLengthInit.program (fun v => v=rawInput xs) (fun v => v=rawScanned xs) (8*xs.length+2) := by
  have hh := BinaryLengthInit.length_hoare xs.length (source xs) 1 (source_nonblank xs) (source_end xs)
  apply hh.consequence (fun _ hv => hv) _ le_rfl
  rintro v ⟨bs,hv,hc,_,rfl⟩
  rw [CompactGadgetReservationHeadersCore.canonical_bits bs xs.length hc hv]
  rfl

theorem resets (xs : List Bool) :
    HoareTime reset (fun v => v=rawScanned xs) (fun v => v=rawOutput xs) (xs.length+3) := by
  have hs := DescriptorStackControl.seek_hoare (rawScanned xs) 0 separator Move.left (xs.length+1)
    (by intro j hj; exact source_no_marker xs _ (by change 0<1+(xs.length:ℤ)+(j:ℤ)*(-1); omega))
    (by change source xs (1+(xs.length:ℤ)+(xs.length+1:ℕ)*(-1))=separator
        have he : (1+(xs.length:ℤ)+(xs.length+1:ℕ)*(-1))=0 := by push_cast; ring
        rw [he,source_marker])
  let mid := positioned (rawScanned xs) 0 0
  have he : positioned (rawScanned xs) 0 ((rawScanned xs).head 0+(xs.length+1:ℕ)*Move.left.offset)=mid := by
    congr 1
    change 1+(xs.length:ℤ)+(xs.length+1:ℕ)*(-1)=0
    push_cast
    ring
  rw [he] at hs
  have hr := DescriptorStackControl.once_hoare (t := 2) (a := 0) (by decide)
    (fun sy i => (sy i,if i=0 then Move.right else Move.stay)) mid
  have hret : (after mid (fun sy i => (sy i,if i=0 then Move.right else Move.stay))).tape=mid.tape := by
    funext i z
    by_cases hz : z=mid.head i <;> simp [after,hz]
  have hout : after mid (fun sy i => (sy i,if i=0 then Move.right else Move.stay))=rawOutput xs := by
    apply congrArg₂ Tapes.mk
    · funext i
      fin_cases i <;> simp [mid,positioned,rawScanned,BinaryLength.bank,Copy.cfg,Move.offset]
    · change (after mid (fun sy i => (sy i,if i=0 then Move.right else Move.stay))).tape=(rawOutput xs).tape
      rw [hret]
      funext i
      fin_cases i
      · rfl
      · exact (BinaryDescriptorCopy.source_binary _).symm
  rw [hout] at hr
  exact (hs.seq hr).consequence (fun _ hv => hv) (fun _ hv => hv) (by omega)

def program (a : ℕ) := Alphabet.program (RadixToBinary.binaryEncoding (q := a)) rawProgram
def input (a : ℕ) (xs : List Bool) := BinaryDescriptorCopy.encodedInput a xs
def output (a : ℕ) (xs : List Bool) :=
  Copy.tapes (RadixZeroFill.encodedBinary (q := a) xs) (RadixZeroFill.encodedBinary (bits xs.length)) 1 1

theorem runs (a : ℕ) (xs : List Bool) :
    HoareTime (program a) (fun v => v=input a xs) (fun v => v=output a xs) (9*xs.length+6) := by
  have hh := (scans xs).seq (resets xs)
  have hi : Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := a)) (rawInput xs)=input a xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (source xs z))=RadixZeroFill.encodedBinary xs
      rw [BinaryDescriptorCopy.source_binary]
      rfl
    · rfl
  have ho : Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := a)) (rawOutput xs)=output a xs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (source xs z))=RadixZeroFill.encodedBinary xs
      rw [BinaryDescriptorCopy.source_binary]
      rfl
    · change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (source (bits xs.length) z))=RadixZeroFill.encodedBinary (bits xs.length)
      rw [BinaryDescriptorCopy.source_binary]
      rfl
  apply (Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := a)) hh).consequence _ _ (by omega)
  · intro v hv; exact ⟨_,rfl,hv.trans hi.symm⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv.trans ho

variable {t a : ℕ}
def placed (focus : Fin 2 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (program a) (BinaryDescriptorCopyPlaced.placement focus hf)

theorem output_set (xs : List Bool) : output a xs=
    setTape (input a xs) 1 (RadixZeroFill.encodedBinary (bits xs.length)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem placed_runs (caller : Tapes t a) (focus : Fin 2 → Fin t) (hf : Function.Injective focus)
    (xs : List Bool) (hi : SharedBank.payload caller focus=input a xs) :
    HoareTime (placed focus hf) (fun v => v=caller)
      (fun v => v=setTape caller (focus 1) (RadixZeroFill.encodedBinary (bits xs.length)) 1)
      (9*xs.length+6) := by
  have ha := (BinaryDescriptorCopyPlaced.active caller focus hf).trans hi
  have hr := Placement.hoare_at (runs a xs) (BinaryDescriptorCopyPlaced.placement focus hf) caller ha
  apply hr.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [output_set,←ha,PlacedDescriptorConstruction.replace_setTape]
  simp only [BinaryDescriptorCopyPlaced.placement,InjectivePlacement.active_slot]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersLength
