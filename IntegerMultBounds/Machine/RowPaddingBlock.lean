import IntegerMultBounds.Machine.CountedRawMove
import IntegerMultBounds.Machine.ExactFrame

/-! One actual per-prefix row-padding block: move the valid span, write a
zero-bit span, and preserve the two supplied immutable count descriptors.
The reusable inner clock is cleaned to its sentinel. Whole-stream framing,
clock initialization and head reset belong to the outer padding procedure. -/
namespace IntegerMultBounds.Machine.RowPaddingBlock
open CountedRawFill (filled)

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) : Tapes 5 0 :=
  (CountedRawMove.bank source dest p q valid).append (CountedRawFill.one (CountedCopyReuse.binary padding) 1)

def fillPlacement : Fin (3+2) ≃ Fin 5 where
  toFun := ![1,2,4,0,3]
  invFun := ![3,0,1,4,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def spectators (source : ℤ → Fin 4) (p : ℤ) (valid : List Bool) : Tapes 2 0 :=
  ⟨![p,1],![source,CountedCopyReuse.binary valid]⟩

theorem fill_endpoint (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    ((CountedRawFill.bank dest q padding).append (spectators source p valid)).reindex fillPlacement =
      bank source dest p q valid padding := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Fixed finite program; both span counts are data on tapes, never parameters
of its finite control. The inserted zero is the actual binary zero symbol. -/
def program : Program 5 (18+18) 0 :=
  seq (extend CountedRawMove.program 1)
    (Placement.placed (CountedRawFill.program (bitSymbol false)) fillPlacement)

def erasePlacement : Fin (3+2) ≃ Fin 5 where
  toFun := ![0,2,4,1,3]
  invFun := ![0,3,1,4,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem erase_endpoint (source dest : ℤ → Fin 4) (p q : ℤ) (valid padding : List Bool) :
    ((CountedRawFill.bank source p padding).append (spectators dest q valid)).reindex erasePlacement =
      bank source dest p q valid padding := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Cropping physically moves the valid cells and erases every padded cell. -/
def cropProgram : Program 5 (18+18) 0 :=
  seq (extend CountedRawMove.program 1)
    (Placement.placed (CountedRawFill.program blank) erasePlacement)

/-- Every valid symbol is physically moved and erased at the source. Every
padding symbol is explicitly written. Payload and descriptor heads are exact. -/
theorem pad_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs : List (Fin 4))
    (valid padding : List Bool) (hv : Counter.value valid = xs.length) :
    HoareTime program (fun v => v = bank (putWord source p xs) dest p q valid padding)
      (fun v => v = bank (filled (putWord source p xs) p xs.length blank)
        (putWord dest q (xs++List.replicate (Counter.value padding) (bitSymbol false)))
        (p+xs.length) (q+xs.length+Counter.value padding) valid padding)
      (7*xs.length+7*valid.length+16+1+7*Counter.value padding+7*padding.length+16) := by
  let moved := filled (putWord source p xs) p xs.length blank
  have hm := hoare_extend_eq (CountedRawMove.move_hoare source dest p q xs valid hv)
    (CountedRawFill.one (CountedCopyReuse.binary padding) 1)
  have hf := hoare_place (CountedRawFill.fill_hoare (bitSymbol false) (putWord dest q xs) (q+xs.length) padding)
    fillPlacement (spectators moved (p+xs.length) valid)
  rw [fill_endpoint,fill_endpoint] at hf
  have he : filled (putWord dest q xs) (q+xs.length) (Counter.value padding) (bitSymbol false) =
      putWord dest q (xs++List.replicate (Counter.value padding) (bitSymbol false)) := by
    rw [CountedRawFill.filled_word]
    exact putWord_append_forward dest q xs _
  rw [he] at hf
  simpa only [program,Placement.placed,bank,moved,Nat.add_assoc] using hm.seq hf

theorem crop_hoare (source dest : ℤ → Fin 4) (p q : ℤ) (xs : List (Fin 4))
    (valid padding : List Bool) (hv : Counter.value valid = xs.length) :
    HoareTime cropProgram (fun v => v = bank (putWord source p xs) dest p q valid padding)
      (fun v => v = bank (filled (putWord source p xs) p (xs.length+Counter.value padding) blank)
        (putWord dest q xs) (p+xs.length+Counter.value padding) (q+xs.length) valid padding)
      (7*xs.length+7*valid.length+16+1+7*Counter.value padding+7*padding.length+16) := by
  let moved := filled (putWord source p xs) p xs.length blank
  have hm := hoare_extend_eq (CountedRawMove.move_hoare source dest p q xs valid hv)
    (CountedRawFill.one (CountedCopyReuse.binary padding) 1)
  have hf := hoare_place (CountedRawFill.fill_hoare blank moved (p+xs.length) padding)
    erasePlacement (spectators (putWord dest q xs) (q+xs.length) valid)
  rw [erase_endpoint,erase_endpoint] at hf
  simp only [moved,CountedRawFill.filled_adjacent] at hf
  simpa only [cropProgram,Placement.placed,bank,moved,Nat.add_assoc] using hm.seq hf

end IntegerMultBounds.Machine.RowPaddingBlock
