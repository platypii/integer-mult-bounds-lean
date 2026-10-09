import IntegerMultBounds.Machine.SymbolTripleArray
import IntegerMultBounds.Machine.SelectedSourceBitsRewind
import IntegerMultBounds.Machine.WordBankCleanup

/-! Paid converter lifecycle on two physical tapes: encode or decode, rewind
both heads, and erase the obsolete source. Both endpoints have head zero and
the source tape wholly blank. Native coefficient words have nonblank interiors;
arbitrary spectator transport is handled by the literal array layer. -/
namespace IntegerMultBounds.Machine.SymbolTripleClean
noncomputable section
open SharedPlacementAlphabet (setTape)
variable {B : ℕ}

def word (xs : List (Fin 6)) := putWord (fun _ => blank) 0 xs

def rewind (i : Fin 2) := Placement.placed (ReturnOrigin.program (a:=2)) (FiniteReturnStackAt.placement i)
def rewindBoth := seq (rewind 0) (rewind 1)
def clear := WordBankCleanup.clearProgram (0 : Fin 2) (by decide) 2
def encodeProgram := seq (seq SymbolTripleStream.program rewindBoth) clear
def decodeProgram := seq (seq SymbolTripleDecodeStream.program rewindBoth) clear

private theorem rewind_runs (v : Tapes 2 2) (i : Fin 2) (xs : List (Fin 6))
    (hn : ∀ s∈xs,s≠blank) (ht : v.tape i=word xs) (hh : v.head i=xs.length) :
    HoareTime (rewind i) (fun w => w=v) (fun w => w=setTape v i (word xs) 0) (xs.length+2) := by
  have h := Placement.hoare_at (ReturnOrigin.return_hoare xs hn)
    (FiniteReturnStackAt.placement i) v (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

private theorem both_runs (xs ys : List (Fin 6))
    (hx : ∀ s∈xs,s≠blank) (hy : ∀ s∈ys,s≠blank) :
    HoareTime rewindBoth
      (fun v => v=Copy.tapes (word xs) (word ys) xs.length ys.length)
      (fun v => v=Copy.tapes (word xs) (word ys) 0 0) (xs.length+ys.length+5) := by
  have h0 := rewind_runs (Copy.tapes (word xs) (word ys) xs.length ys.length) 0 xs hx rfl rfl
  have he0 : setTape (Copy.tapes (word xs) (word ys) xs.length ys.length) 0 (word xs) 0=
      Copy.tapes (word xs) (word ys) 0 ys.length := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he0] at h0
  have h1 := rewind_runs (Copy.tapes (word xs) (word ys) 0 ys.length) 1 ys hy rfl rfl
  have he1 : setTape (Copy.tapes (word xs) (word ys) 0 ys.length) 1 (word ys) 0=
      Copy.tapes (word xs) (word ys) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he1] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

private theorem clear_runs (xs ys : List (Fin 6)) (hx : ∀ s∈xs,s≠blank) :
    HoareTime clear (fun v => v=Copy.tapes (word xs) (word ys) 0 0)
      (fun v => v=Copy.tapes (fun _ => blank) (word ys) 0 0) (2*xs.length+3) := by
  have h := WordBankCleanup.clear_hoare (Copy.tapes (word xs) (word ys) 0 0)
    (0 : Fin 2) (by decide) xs hx rfl
  have he : WordBankCleanup.write (Copy.tapes (word xs) (word ys) 0 0) 0 (fun _ => blank)=
      Copy.tapes (fun _ => blank) (word ys) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem encoded_nonblank (xs : Fin B → Fin 6) :
    ∀ s∈SymbolTripleStream.word (List.ofFn xs),s≠blank := by
  rw [←SymbolTripleArray.triple_word]
  intro s hs
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hs
  cases b <;> simp [bitSymbol,blank]

/-- Actual destructive encoding with no retained native source, encoded heads
normalized and every join/rewind/source erasure included in the linear bound. -/
theorem encode_runs (xs : Fin B → Fin 6) (hn : ∀ j,xs j≠blank) :
    HoareTime encodeProgram
      (fun v => v=Copy.tapes (word (List.ofFn xs)) (fun _ => blank) 0 0)
      (fun v => v=Copy.tapes (fun _ => blank) (word (SymbolTripleStream.word (List.ofFn xs))) 0 0)
      (13*B+10) := by
  have hx : ∀ s∈List.ofFn xs,s≠blank := by
    intro s hs; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs; exact hn j
  have hy := encoded_nonblank xs
  have h0 := SymbolTripleStream.runs (fun _ => blank) (fun _ => blank) 0 0 (List.ofFn xs) rfl hx
  simp only [List.length_ofFn,zero_add] at h0
  have h1 := both_runs (List.ofFn xs) (SymbolTripleStream.word (List.ofFn xs)) hx hy
  have h2 := clear_runs (List.ofFn xs) (SymbolTripleStream.word (List.ofFn xs)) hx
  simp only [SymbolTripleStream.word_length,List.length_ofFn] at h1 h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Actual destructive decoding of coefficient symbols, including all scratch
cleanup. The nonblank native condition pays sentinel-based output rewind. -/
theorem decode_runs (xs : Fin B → Fin 6) (hn : ∀ j,xs j≠blank) :
    HoareTime decodeProgram
      (fun v => v=Copy.tapes (word (SymbolTripleStream.word (List.ofFn xs))) (fun _ => blank) 0 0)
      (fun v => v=Copy.tapes (fun _ => blank) (word (List.ofFn xs)) 0 0)
      (19*B+10) := by
  have hx : ∀ s∈List.ofFn xs,s≠blank := by
    intro s hs; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs; exact hn j
  have hy := encoded_nonblank xs
  have h0 := SymbolTripleDecodeStream.runs (fun _ => blank) (fun _ => blank) 0 0 xs rfl
  simp only [zero_add] at h0
  have h1 := both_runs (SymbolTripleStream.word (List.ofFn xs)) (List.ofFn xs) hy hx
  have h2 := clear_runs (SymbolTripleStream.word (List.ofFn xs)) (List.ofFn xs) hy
  simp only [SymbolTripleStream.word_length,List.length_ofFn] at h1 h2
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.SymbolTripleClean
