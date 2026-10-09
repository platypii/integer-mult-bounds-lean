import IntegerMultBounds.Machine.CountedRawMove

/-! Paid simultaneous movement of two payload heads by one immutable count. -/
namespace IntegerMultBounds.Machine.CountedPairPosition

def cell (m : Move) : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then some (1,fun i => (sy i,m)) else none

theorem cell_hoare (m : Move) (source dest : ℤ → Fin 4) (p q : ℤ) :
    HoareTime (cell m) (fun v => v = CountedRawMove.payload source dest p q)
      (fun v => v = CountedRawMove.payload source dest (p+m.offset) (q+m.offset)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,![p+m.offset,q+m.offset],![source,dest]⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,cell,Tapes.start,↓reduceIte,CountedRawMove.payload]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> split_ifs with hz <;> simp_all
  · simp [step,cell]

def program (m : Move) : Program 4 18 0 := CountedLoopReuse.program (cell m)

theorem position_hoare (m : Move) (source dest : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    HoareTime (program m) (fun v => v = CountedRawMove.bank source dest p q bs)
      (fun v => v = CountedRawMove.bank source dest
        (p+Counter.value bs*m.offset) (q+Counter.value bs*m.offset) bs)
      (7*Counter.value bs+7*bs.length+16) := by
  let v := fun i : ℕ => CountedRawMove.payload source dest (p+i*m.offset) (q+i*m.offset)
  have hb : ∀ i < Counter.value bs, HoareTime (cell m)
      (fun w => w = v i) (fun w => w = v (i+1)) 1 := by
    intro i _
    have h := cell_hoare m source dest (p+i*m.offset) (q+i*m.offset)
    have he : ∀ z : ℤ, z+(i : ℤ)*m.offset+m.offset = z+((i+1 : ℕ) : ℤ)*m.offset := by
      intro z; push_cast; ring
    simpa only [v,he] using h
  have h := CountedLoopReuse.loop_hoare (cell m) bs (Counter.value bs) v (fun _ => 1) rfl hb
  simpa [program,CountedRawMove.bank,v,show ∀ n : ℕ, n+6*n=7*n by omega] using h

end IntegerMultBounds.Machine.CountedPairPosition
