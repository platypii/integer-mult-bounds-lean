import IntegerMultBounds.Machine.Copy
import IntegerMultBounds.Machine.Rewind

/-! Erase a finite nonblank word at cell one and restore an entirely blank tape.
A temporary marker is installed, scanned back to, and physically removed. -/

namespace IntegerMultBounds.Machine.MarkedWordCleanup

variable {a : ℕ}

def empty : ℤ → Fin (a+4) := fun z => if z = 0 then separator else blank

def word (xs : List (Fin (a+4))) := putWord (fun _ => blank) 1 xs

def marked (xs : List (Fin (a+4))) := putWord empty 1 xs

def one (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => f⟩

/-- One real marker write and head move. -/
def markProgram : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s = 0 then some (1,fun _ => (separator,Move.right)) else none

theorem mark_word (xs : List (Fin (a+4))) : Function.update (word xs) 0 separator = marked xs := by
  have he : Function.update (fun _ : ℤ => (blank : Fin (a+4))) 0 separator = empty := by
    funext z
    simp [empty,Function.update_apply]
  rw [word,marked,← he]
  exact (putWord_update_before (fun _ => blank) 1 0 separator xs (by omega)).symm

theorem mark_hoare (xs : List (Fin (a+4))) :
    HoareTime markProgram (fun v => v = one (word xs) 0) (fun v => v = one (marked xs) 1) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => 1,fun _ => marked xs⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,markProgram,one,Tapes.start,ite_true,Move.offset,zero_add]
    congr 1
    congr 1
    funext i z
    by_cases hz : z = 0 <;> simp [← mark_word,hz]
  · simp [step,markProgram]

def clearProgram : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ symbols => if symbols 0 = blank then none else some (0,fun _ => (blank,Move.right))

private def clearCfg (f : ℤ → Fin (a+4)) (p : ℤ) : Config 1 1 a := ⟨0,fun _ => p,fun _ => f⟩

private theorem clear_step (f : ℤ → Fin (a+4)) (p : ℤ) (h : f p ≠ blank) :
    step clearProgram (clearCfg f p) = some (clearCfg (Function.update f p blank) (p+1)) := by
  simp only [step,clearProgram,clearCfg,h,ite_false,Move.offset]
  congr 1
  congr 1
  funext i z
  simp [Function.update_apply,eq_comm]

private theorem clear_run (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (hxs : ∀ x ∈ xs, x ≠ blank) :
    run clearProgram xs.length (clearCfg (putWord f p xs) p) =
      some (clearCfg (putWord f p (xs.map (fun _ => blank))) (p+xs.length)) := by
  induction xs generalizing f p with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := clear_step (putWord f p (x::xs)) p
      (by rw [putWord_head]; exact hxs x (by simp))
    rw [putWord_replace_head] at hs
    simp only [List.length_cons,run,hs,Option.bind_some]
    have hr := ih (Function.update f p blank) (p+1) (fun y hy => hxs y (by simp [hy]))
    simpa only [List.map_cons,← putWord_cons,Nat.cast_add,Nat.cast_one,
      add_assoc,add_comm,add_left_comm] using hr

private theorem putWord_blank_eq (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List (Fin (a+4)))
    (hf : ∀ z : ℤ, p ≤ z → f z = blank) :
    putWord f p (xs.map (fun _ => blank)) = f := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,putWord,ih (p+1) (fun z hz => hf z (by omega))]
    exact Function.update_eq_self_iff.mpr (hf p le_rfl).symm

theorem clear_hoare (xs : List (Fin (a+4))) (hxs : ∀ x ∈ xs, x ≠ blank) :
    HoareTime clearProgram (fun v => v = one (marked xs) 1)
      (fun v => v = one empty (1+xs.length)) xs.length := by
  have hr := clear_run empty 1 xs hxs
  have he : putWord empty 1 (xs.map (fun _ => blank)) = empty :=
    putWord_blank_eq empty 1 _ (by intro z hz; simp [empty,show z ≠ 0 by omega])
  rw [he] at hr
  rintro v rfl
  refine ⟨xs.length,clearCfg empty (1+xs.length),le_rfl,hr,?_,rfl⟩
  simp [step,clearProgram,clearCfg,empty,show (1:ℤ)+xs.length ≠ 0 by omega]

/-- Erase the last temporary marker without moving the restored head. -/
def unmarkProgram : Program 1 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s = 0 then some (1,fun _ => (blank,Move.stay)) else none

theorem unmark_hoare (xs : List (Fin (a+4))) :
    HoareTime unmarkProgram (fun v => v = one (marked xs) 0) (fun v => v = one (word xs) 0) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,fun _ => 0,fun _ => word xs⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,unmarkProgram,one,Tapes.start,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    funext i
    funext z
    by_cases hz : z = 0
    · subst z
      simp only [ite_true]
      rw [word,putWord_outside _ _ _ _ (Or.inl (by omega))]
    · simp [← mark_word,hz]
  · simp [step,unmarkProgram]

/-- Six-state cleanup, with no count descriptor or fixed word-width parameter. -/
def program : Program 1 6 a := seq (seq (seq markProgram clearProgram) (Rewind.program separator)) unmarkProgram

theorem cleanup_hoare (xs : List (Fin (a+4))) (hxs : ∀ x ∈ xs, x ≠ blank) :
    HoareTime program (fun v => v = one (word xs) 0) (fun v => v = one (fun _ => blank) 0)
      (2*xs.length+6) := by
  have hr := Rewind.rewind_hoare (separator : Fin (a+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j ≠ 0 by omega,blank,separator])
    (by simp [empty])
  have hr' : HoareTime (Rewind.program (separator : Fin (a+4)))
      (fun v => v = one empty (1+xs.length)) (fun v => v = one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  have hh := (((mark_hoare xs).seq (clear_hoare xs hxs)).seq hr').seq (unmark_hoare [])
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.MarkedWordCleanup
