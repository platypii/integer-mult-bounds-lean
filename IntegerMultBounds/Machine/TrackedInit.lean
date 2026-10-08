import IntegerMultBounds.Machine.TrackedExecution
import IntegerMultBounds.Machine.SharedBank

/-! Initialize synchronized visited tapes from wholly blank workspace for a
fixed zero/one head template. Original data tapes and heads are untouched. -/
namespace IntegerMultBounds.Machine.TrackedInit
variable {t a s : ℕ}

def position (right : Fin t → Bool) (i : Fin t) : ℤ := if right i then 1 else 0

def trackers (right : Fin t → Bool) : Tapes t a :=
  ⟨position right,fun i => TrackedCleanup.tracker 0 (position right i)⟩

def program (right : Fin t → Bool) (ht : 0 < t) : Program (t+t) 3 a where
  tapes_pos := by omega
  start := 0
  transition := fun s sy => if s = 0 then some (1,Fin.addCases
    (fun i => (sy (Fin.castAdd t i),Move.stay))
    (fun i => (separator,if right i then Move.right else Move.stay)))
    else if s = 1 then some (2,Fin.addCases
      (fun i => (sy (Fin.castAdd t i),Move.stay))
      (fun i => (TrackedExecution.mark (sy (Fin.natAdd t i)),Move.stay)))
    else none

theorem initialize_hoare (right : Fin t → Bool) (ht : 0 < t) (v : Tapes t a) :
    HoareTime (program right ht) (fun w => w = v.append (SharedBank.empty t a))
      (fun w => w = v.append (trackers right)) 2 := by
  let mid : Config (t+t) 3 a := ⟨1,Fin.addCases v.head (position right),
    Fin.addCases v.tape (fun _ => TrackedCleanup.origin)⟩
  let last : Config (t+t) 3 a := ⟨2,(v.append (trackers right)).head,(v.append (trackers right)).tape⟩
  have hfirst : step (program right ht) ((v.append (SharedBank.empty t a)).start (program right ht)) = some mid := by
    simp only [step,program,Tapes.start,ite_true,Tapes.append,SharedBank.empty]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.addCases_left,Move.offset,add_zero]
      | right i =>
        simp only [Fin.addCases_right,position]
        cases right i <;> rfl
    · funext i z
      induction i using Fin.addCases with
      | left i =>
        simp only [Fin.addCases_left]
        by_cases hz : z = v.head i <;> simp [hz]
      | right i => simp only [Fin.addCases_right,TrackedCleanup.origin]
  have hsecond : step (program right ht) mid = some last := by
    simp only [step,program,mid,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases <;>
        simp only [Fin.addCases_left,Fin.addCases_right,Move.offset,add_zero,Tapes.append,trackers]
    · funext i z
      induction i using Fin.addCases with
      | left i =>
        simp only [Fin.addCases_left,Tapes.append]
        by_cases hz : z = v.head i <;> simp [hz]
      | right i =>
        simp only [Fin.addCases_right,Tapes.append,trackers]
        cases hr : right i
        · by_cases hz : z = 0
          · subst z; simp [position,hr,TrackedCleanup.origin,TrackedCleanup.tracker,TrackedExecution.mark]
          · have hn : ¬ (0 ≤ z ∧ z ≤ 0) := by omega
            simp [position,hr,TrackedCleanup.origin,TrackedCleanup.tracker,hz,hn]
        · by_cases hz : z = 1
          · subst z
            simp [position,hr,TrackedCleanup.origin,TrackedCleanup.tracker,TrackedExecution.mark,
              show (blank : Fin (a+4)) ≠ separator by simp [blank,separator,Fin.ext_iff]]
          · have he : ¬ (0 ≤ z ∧ z ≤ 1) ∨ z = 0 := by omega
            rcases he with he | rfl
            · simp [position,hr,TrackedCleanup.origin,TrackedCleanup.tracker,hz,he]
            · simp [position,hr,TrackedCleanup.origin,TrackedCleanup.tracker,hz]
  intro w hw
  subst w
  refine ⟨2,last,le_rfl,?_,?_,rfl⟩
  · rw [run,hfirst]
    simpa only [Option.bind_some,run_one] using hsecond
  · simp [step,program,last]

/-- The initialized bank matches the exact simulation invariant whenever the
original machine has the fixed zero/one initial head pattern. -/
theorem start_lift (M : Program t s a) (right : Fin t → Bool) (v : Tapes t a)
    (hh : v.head = position right) :
    (v.append (trackers right)).start (TrackedExecution.program M) =
      TrackedExecution.lift (v.start M) (fun _ => 0) (position right) := by
  simp only [Tapes.start,Tapes.append,trackers,TrackedExecution.lift,TrackedExecution.program,hh]

end IntegerMultBounds.Machine.TrackedInit
