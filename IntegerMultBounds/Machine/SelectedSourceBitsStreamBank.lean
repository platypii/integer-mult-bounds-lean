import IntegerMultBounds.Machine.SelectedSourceBitsStreamCore
import IntegerMultBounds.Machine.CountedBankResetHeader

/-! Four independently counted scans share a literal two-tape source/output
payload. All four countdown clocks are physically initProgramd and erased. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamBank
open CountedLoopReuseAlphabet (bank empty binary)
variable {a : ℕ}

def marked (v : Tapes 2 a) (hs : Fin 4 → List Bool) : Tapes 10 a :=
  ⟨![v.head 0,v.head 1,1,1,1,1,1,1,1,1],
    ![v.tape 0,v.tape 1,empty,binary (hs 0),empty,binary (hs 1),empty,binary (hs 2),empty,binary (hs 3)]⟩

def raw (v : Tapes 2 a) (hs : Fin 4 → List Bool) : Tapes 10 a :=
  ⟨![v.head 0,v.head 1,0,1,0,1,0,1,0,1],
    ![v.tape 0,v.tape 1,fun _ => blank,binary (hs 0),fun _ => blank,binary (hs 1),
      fun _ => blank,binary (hs 2),fun _ => blank,binary (hs 3)]⟩

def clock (i : Fin 10) : Bool := i=2 || i=4 || i=6 || i=8

def initProgram : Program 10 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i =>
    (if clock i then separator else sy i,if clock i then .right else .stay)) else none

def cleanup : Program 10 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i =>
    (sy i,if clock i then .left else .stay))
    else if st=1 then some (2,fun i => (if clock i then blank else sy i,.stay)) else none

theorem initializes (v : Tapes 2 a) (hs : Fin 4 → List Bool) :
    HoareTime initProgram (fun z => z=raw v hs) (fun z => z=marked v hs) 1 := by
  rintro z rfl
  refine ⟨1,⟨1,(marked v hs).head,(marked v hs).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [raw,marked,clock,Move.offset]
    · funext i z; fin_cases i <;> simp [raw,marked,clock,empty]
      all_goals aesop
  · simp [step,initProgram]

theorem cleans (v : Tapes 2 a) (hs : Fin 4 → List Bool) :
    HoareTime cleanup (fun z => z=marked v hs) (fun z => z=raw v hs) 2 := by
  rintro z rfl
  let mid : Config 10 3 a := ⟨1,(raw v hs).head,(marked v hs).tape⟩
  let last : Config 10 3 a := ⟨2,(raw v hs).head,(raw v hs).tape⟩
  have h0 : step cleanup ((marked v hs).start cleanup) = some mid := by
    simp only [step,cleanup,Tapes.start,ite_true,mid]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [raw,marked,clock,Move.offset]
    · funext i z; fin_cases i <;> simp [marked]
      all_goals aesop
  have h1 : step cleanup mid = some last := by
    simp only [step,cleanup,mid,last,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    funext i z; fin_cases i <;> simp [raw,marked,clock,empty]
    all_goals aesop
  refine ⟨2,last,le_rfl,?_,?_,rfl⟩
  · change run cleanup (1+1) ((marked v hs).start cleanup) = some last
    rw [run_add,run_one,h0]
    simpa only [Option.bind_some,run_one] using h1
  · simp [step,cleanup,last]

end IntegerMultBounds.Machine.SelectedSourceBitsStreamBank
