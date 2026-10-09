import IntegerMultBounds.Machine.ActiveRepairRecordFlattenEndpoint

/-! Physical left-marker installation for raw repaired record streams. -/
namespace IntegerMultBounds.Machine.ActiveRepairRecordFlattenPrepare
open CountedTapeRepairCleanupWord

def program : Program 1 3 1 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun _ => (sy 0,.left))
    else if s=1 then some (2,fun _ => (PartitionMarked.marker,.right)) else none

def cfg (f : ℤ → Fin 5) (p : ℤ) (s : Fin 3) : Config 1 3 1 :=
  ⟨s,fun _ => p,fun _ => f⟩

theorem first (f : ℤ → Fin 5) :
    step program (cfg f 0 0)=some (cfg f (-1) 1) := by
  simp only [step,program,cfg,↓reduceIte,Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (1 : Fin 3))
  · funext i; fin_cases i; rfl
  · funext i z; fin_cases i
    by_cases hz : z=0 <;> simp [hz]

theorem second (f : ℤ → Fin 5) :
    step program (cfg f (-1) 1)=
      some (cfg (Function.update f (-1) PartitionMarked.marker) 0 2) := by
  simp only [step,program,cfg,show (1 : Fin 3)≠0 by decide,↓reduceIte,Move.offset]
  congr 1
  apply congrArg₂ (Config.mk (2 : Fin 3))
  · funext i; fin_cases i; rfl
  · funext i z; fin_cases i; simp only [Function.update_apply]; rfl

theorem runs (f : ℤ → Fin 5) :
    HoareTime program (fun v => v=one f 0)
      (fun v => v=one (Function.update f (-1) PartitionMarked.marker) 0) 2 := by
  rintro v rfl
  refine ⟨2,cfg (Function.update f (-1) PartitionMarked.marker) 0 2,le_refl _,?_,?_,rfl⟩
  · change run program (1+1) (cfg f 0 0)=_
    rw [run_add,run_one,first,Option.bind_some,run_one,second]
  · simp [step,program,cfg]

theorem marked_word (xs : List (Fin 5)) :
    Function.update (putWord (fun _ => blank) 0 xs) (-1) PartitionMarked.marker=marked xs := by
  rw [←putWord_update_before (fun _ => blank) 0 (-1) PartitionMarked.marker xs (by omega)]
  have h : Function.update (fun _ : ℤ => (blank : Fin 5)) (-1) PartitionMarked.marker=
      PartitionMarked.markedTape 0 [] := by
    funext z
    simp [PartitionMarked.markedTape,putWord,PartitionMarked.encoding,Alphabet.widen,
      Function.update_apply]
    rfl
  rw [h]
  rfl

end IntegerMultBounds.Machine.ActiveRepairRecordFlattenPrepare
