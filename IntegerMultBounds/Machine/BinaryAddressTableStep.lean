import IntegerMultBounds.Machine.BinaryAddressTableData
import IntegerMultBounds.Machine.MarkedControlStreamReset
import IntegerMultBounds.Machine.CountedLoopReuse

/-! Copy one actual fixed-width address to the packed output, physically rewind
its source, and increment it. The counter width is absent from finite control. -/
namespace IntegerMultBounds.Machine.BinaryAddressTableStep
open BinaryAddressTableData
open CountedCopyReuse (empty binary)

theorem bits_word (f : ℤ → Fin 4) (p : ℤ) (xs : List Bool) :
    putBits f p xs = putWord f p (xs.map bitSymbol) := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih => simp only [putBits,putWord,List.map_cons,ih]

theorem binary_word (xs : List Bool) : binary xs = MarkedWordCleanup.marked (xs.map bitSymbol) :=
  bits_word _ _ _

theorem pair_append (f g : ℤ → Fin 4) (p q : ℤ) :
    (⟨fun _ => p,fun _ => f⟩ : Tapes 1 0).append (⟨fun _ => q,fun _ => g⟩ : Tapes 1 0) = Copy.tapes f g p q := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program : Program 2 ((1+3)+3) 0 :=
  seq (seq (Copy.program blank false) (extend MarkedControlStreamReset.rewind 1))
    (extend CounterTape.program 1)

def bank (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) : Tapes 2 0 := Copy.tapes (binary xs) g 1 p

theorem runs (xs : List Bool) (g : ℤ → Fin 4) (p : ℤ) :
    HoareTime program (fun z => z=bank xs g p)
      (fun z => z=bank (Counter.increment xs) (putWord g p (xs.map bitSymbol)) (p+xs.length))
      (4*xs.length+7) := by
  have hc := Copy.copy_hoare blank false empty g 1 p (xs.map bitSymbol)
    (ReturnOrigin.bits_nonblank xs) (by simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega])
  have hi : (Copy.retained false : Fin 4 → Fin 4) = id := rfl
  simp only [hi,List.map_id,List.length_map] at hc
  rw [←bits_word empty 1 xs] at hc
  have hr := hoare_extend_eq (MarkedControlStreamReset.rewinds (xs.map (bitSymbol (a := 0)))
    (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; cases b <;> decide))
    (⟨fun _ => p+xs.length,fun _ => putWord g p (xs.map bitSymbol)⟩ : Tapes 1 0)
  have hr' : HoareTime (extend MarkedControlStreamReset.rewind 1)
      (fun z => z=Copy.tapes (binary xs) (putWord g p (xs.map bitSymbol)) (1+xs.length) (p+xs.length))
      (fun z => z=bank xs (putWord g p (xs.map bitSymbol)) (p+xs.length)) (xs.length+3) := by
    simpa only [List.length_map,←binary_word,MarkedWordCleanup.one,pair_append,bank] using hr
  have ha := hoare_extend_eq (CounterTape.increment_hoare empty xs rfl (by simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega]))
    (⟨fun _ => p+xs.length,fun _ => putWord g p (xs.map bitSymbol)⟩ : Tapes 1 0)
  have ha' : HoareTime (extend CounterTape.program 1)
      (fun z => z=bank xs (putWord g p (xs.map bitSymbol)) (p+xs.length))
      (fun z => z=bank (Counter.increment xs) (putWord g p (xs.map bitSymbol)) (p+xs.length))
      (2*CounterTape.carrySteps xs) := by
    simpa only [CounterTape.tapes,pair_append,bank,binary] using ha
  have hbound := (CounterTape.carrySteps_bounds xs).2.1
  exact ((hc.seq hr').seq ha').consequence (fun _ h => h) (fun _ h => h) (by omega)

def state (w i : ℕ) (g : ℤ → Fin 4) (p : ℤ) :=
  bank (row w i) (putWord g p ((table w i).map bitSymbol)) (p+(i*w : ℕ))

theorem step (w i : ℕ) (g : ℤ → Fin 4) (p : ℤ) :
    HoareTime program (fun z => z=state w i g p) (fun z => z=state w (i+1) g p) (4*w+7) := by
  have hh := runs (row w i) (putWord g p ((table w i).map bitSymbol)) (p+(i*w : ℕ))
  rw [←row_succ,row_length] at hh
  have hp : p+(i*w : ℕ)+w=p+((i+1)*w : ℕ) := by push_cast; ring
  have ht : putWord (putWord g p ((table w i).map bitSymbol)) (p+(i*w : ℕ)) ((row w i).map bitSymbol) =
      putWord g p ((table w (i+1)).map bitSymbol) := by
    rw [table_succ,List.map_append]
    simpa only [List.length_map,table_length] using
      putWord_append_forward g p ((table w i).map bitSymbol) ((row w i).map bitSymbol)
  simpa only [ht,hp,state] using hh

end IntegerMultBounds.Machine.BinaryAddressTableStep
