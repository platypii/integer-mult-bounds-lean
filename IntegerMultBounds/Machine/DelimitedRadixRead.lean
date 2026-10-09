import IntegerMultBounds.Machine.RawLinearCombinationCleanup

/-! A delimiter-driven coefficient-field reader. The stream is retained, its
head advances over exactly one separator, and the extracted radix word is
returned at the marked-control head expected by the arithmetic compiler. -/
namespace IntegerMultBounds.Machine.DelimitedRadixRead
open MarkedWordCleanup (one empty marked word)
open RadixDigits
open RawLinearCombinationCleanup (prepend prepend_runs)
variable {q : ℕ}

def rightProgram : Program 2 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s symbols => if s=0 then some (1,fun i => (symbols i,Move.right)) else none

theorem right_runs (f g : ℤ → Fin (q+4)) (p r : ℤ) :
    HoareTime rightProgram (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f g (p+1) (r+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(Copy.tapes f g (p+1) (r+1)).head,(Copy.tapes f g (p+1) (r+1)).tape⟩,
    le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,rightProgram,Copy.tapes,Copy.cfg,Config.tapes,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z
      fin_cases i
      · by_cases hz : z=p <;> simp [hz]
      · by_cases hz : z=r <;> simp [hz]
  · simp [step,rightProgram]

theorem source_marker (xs : List (Fin q)) : marked (xs.map digitSymbol) 0=separator := by
  rw [marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

theorem source_no_marker (xs : List (Fin q)) (z : ℤ) (hz : 0<z) :
    marked (xs.map digitSymbol) z≠separator := by
  by_cases hi : z<1+xs.length
  · have hm := ReturnOrigin.putWord_mem empty 1 (xs.map digitSymbol) z ⟨by omega,by simpa using hi⟩
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hm
    change putWord empty 1 (xs.map digitSymbol) z≠separator
    rw [←hy]
    simp [digitSymbol,separator,Fin.ext_iff]
  · rw [marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [empty,show z≠0 by omega,blank,separator,Fin.ext_iff]

theorem rewind_runs (xs : List (Fin q)) :
    HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v=one (marked (xs.map digitSymbol)) (1+xs.length))
      (fun v => v=one (marked (xs.map digitSymbol)) 0) (xs.length+1) := by
  have h := Rewind.rewind_hoare (separator : Fin (q+4)) (marked (xs.map digitSymbol))
    (xs.length+1) (xs.length+1)
    (by intro j hj; apply source_no_marker; omega) (by simpa using source_marker xs)
  simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using h

def program : Program 2 6 q :=
  seq (seq (seq (prepend MarkedWordCleanup.markProgram 1) (Copy.program separator false))
    (prepend (Rewind.program separator) 1)) rightProgram

/-- Exterior stream cells are framed literally. The only source precondition is
its next delimiter; the serialized-record lemmas discharge it from the data. -/
theorem runs (f : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin q))
    (he : f (p+xs.length)=separator) :
    HoareTime program
      (fun v => v=Copy.tapes (putWord f p (xs.map digitSymbol)) (fun _ => blank) p 0)
      (fun v => v=Copy.tapes (putWord f p (xs.map digitSymbol)) (marked (xs.map digitSymbol))
        (p+xs.length+1) 1) (2*xs.length+6) := by
  have hm := prepend_runs MarkedWordCleanup.markProgram _ _
    (one (putWord f p (xs.map digitSymbol)) p) (MarkedWordCleanup.mark_hoare [])
  have hc := Copy.copy_hoare (separator : Fin (q+4)) false f empty p 1 (xs.map digitSymbol)
    (by intro z hz; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz; simp [digitSymbol,separator,Fin.ext_iff])
    (by simpa using he)
  have hid : (Copy.retained false : Fin (q+4) → Fin (q+4))=id := by funext x; rfl
  simp only [hid,List.map_id,List.length_map] at hc
  have hr := prepend_runs (Rewind.program (separator : Fin (q+4))) _ _
    (one (putWord f p (xs.map digitSymbol)) (p+xs.length)) (rewind_runs xs)
  have hf := right_runs (putWord f p (xs.map digitSymbol)) (marked (xs.map digitSymbol)) (p+xs.length) 0
  have ha : ∀ (u v : ℤ → Fin (q+4)) (j k : ℤ), (one u j).append (one v k)=Copy.tapes u v j k := by
    intro u v j k
    unfold one Tapes.append Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [ha,ha] at hm hr
  exact (((hm.seq hc).seq hr).seq hf).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.DelimitedRadixRead
