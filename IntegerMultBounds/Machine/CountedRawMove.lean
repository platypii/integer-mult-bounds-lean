import IntegerMultBounds.Machine.CountedRawFill
import IntegerMultBounds.Machine.WordSegments

/-! Exact raw destructive transfer with a reusable actual binary countdown.
Arbitrary symbols are moved; source cells are physically erased, surrounding
cells and the immutable span descriptor are retained. -/
namespace IntegerMultBounds.Machine.CountedRawMove
open CountedRawFill (filled)

def payload (source dest : ℤ → Fin 4) (p q : ℤ) : Tapes 2 0 := ⟨![p,q],![source,dest]⟩

def cell : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => (if i=0 then blank else symbols 0,Move.right)) else none

theorem cell_hoare (source dest : ℤ → Fin 4) (p q : ℤ) :
    HoareTime cell (fun v => v = payload source dest p q)
      (fun v => v = payload (Function.update source p blank) (Function.update dest q (source p))
        (p+1) (q+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(payload (Function.update source p blank) (Function.update dest q (source p))
    (p+1) (q+1)).head,(payload (Function.update source p blank) (Function.update dest q (source p))
    (p+1) (q+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,cell,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [payload,Move.offset]
    · funext i z; fin_cases i <;> simp [payload,Function.update_apply]
  · simp [step,cell]

def program : Program 4 18 0 := CountedLoopReuse.program cell

def bank (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) : Tapes 4 0 :=
  CountedLoopReuse.bank (payload source dest p q) CountedCopyReuse.empty (CountedCopyReuse.binary bs) 1 1

private theorem write_take (g : ℤ → Fin 4) (p : ℤ)
    (xs : List (Fin 4)) (i : ℕ) (hi : i < xs.length) :
    Function.update (putWord g p (xs.take i)) (p+i) xs[i] = putWord g p (xs.take (i+1)) := by
  have hl : (xs.take i).length=i := List.length_take_of_le (by omega)
  have hh := putWord_append_forward g p (xs.take i) [xs[i]]
  simpa only [putWord,hl,List.take_succ_eq_append_getElem hi] using hh

/-- Actual count preparation, transfer, source erasure and clock cleanup. No
sentinel of the payload is inspected, and both data heads advance by the span. -/
theorem move_hoare (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hc : Counter.value bs = xs.length) :
    HoareTime program (fun v => v = bank (putWord source p xs) dest p q bs)
      (fun v => v = bank (filled (putWord source p xs) p xs.length blank) (putWord dest q xs)
        (p+xs.length) (q+xs.length) bs)
      (7*xs.length+7*bs.length+16) := by
  let initial := putWord source p xs
  let v := fun i : ℕ => payload (filled initial p i blank) (putWord dest q (xs.take i)) (p+i) (q+i)
  have hh := CountedLoopReuse.loop_hoare cell bs xs.length v (fun _ => 1) hc (by
    intro i hi
    have h := cell_hoare (filled initial p i blank) (putWord dest q (xs.take i)) (p+i) (q+i)
    have hread : initial (p+i) = xs[i] := WordSegments.get source p xs i hi
    rw [CountedRawFill.filled_outside initial p i blank (p+i) (Or.inr le_rfl),
      hread,CountedRawFill.filled_succ,write_take dest q xs i hi] at h
    simpa only [v,initial,Nat.cast_add,Nat.cast_one,add_assoc] using h)
  simpa only [program,bank,v,List.take_zero,putWord,CountedRawFill.filled_zero,
    Nat.cast_zero,add_zero,List.take_length,Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one,
    show xs.length+6*xs.length=7*xs.length by omega] using hh

theorem move_linear (source dest : ℤ → Fin 4) (p q : ℤ)
    (xs : List (Fin 4)) (bs : List Bool) (hc : Counter.value bs = xs.length)
    (hcanon : GrowingCounterData.Canonical bs) :
    HoareTime program (fun v => v = bank (putWord source p xs) dest p q bs)
      (fun v => v = bank (filled (putWord source p xs) p xs.length blank) (putWord dest q xs)
        (p+xs.length) (q+xs.length) bs) (14*xs.length+23) := by
  have hw := GrowingCounterData.canonical_width bs hcanon
  have hl := Nat.log2_le_self (Counter.value bs)
  exact (move_hoare source dest p q xs bs hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.CountedRawMove
