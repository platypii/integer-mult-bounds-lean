import IntegerMultBounds.Machine.MarkedWordCleanup
import IntegerMultBounds.Machine.ExactFrame

/-! Rewind and erase a marked control stream whose interior may contain blanks.
Only the separator terminates the backwards scan; every generated cell and the
marker are erased, while the cell beyond the stream is retained. -/
namespace IntegerMultBounds.Machine.MarkedControlStreamReset
open MarkedWordCleanup (marked empty one)
variable {a : ℕ}

def program : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun i => (sy i,Move.left))
    else if s=1 then if sy 0=separator then some (2,fun _ => (blank,Move.stay))
      else some (1,fun _ => (blank,Move.left)) else none

private def cfg (f : ℤ → Fin (a+4)) (p : ℤ) (s : Fin 3) : Config 1 3 a := ⟨s,fun _ => p,fun _ => f⟩

private theorem last_step (xs : List (Fin (a+4))) (x : Fin (a+4)) (hx : x ≠ separator) :
    step program (cfg (marked (xs++[x])) (xs.length+1) 1) = some (cfg (marked xs) xs.length 1) := by
  have hw : marked (xs++[x]) = Function.update (marked xs) (1+xs.length) x := by
    rw [marked,← putWord_append_forward]
    rfl
  have hr : marked xs (1+xs.length) = blank := by
    rw [marked,putWord_outside _ _ _ _ (Or.inr le_rfl)]
    simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega]
  have hs : marked (xs++[x]) (xs.length+1) = x := by
    rw [hw,show (xs.length : ℤ)+1=1+xs.length by omega,Function.update_self]
  dsimp only [step,program,cfg]
  simp only [show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,hs,hx,Move.offset]
  congr 1
  congr 1
  · funext i; omega
  · funext i z
    by_cases hz : z=(xs.length : ℤ)+1
    · subst z
      simp only [ite_true]
      simpa only [add_comm] using hr.symm
    · simp only [ite_eq_right hz]
      rw [hw,Function.update_of_ne (by omega)]

private theorem erase_run (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ separator) :
    run program xs.length (cfg (marked xs) xs.length 1) = some (cfg empty 0 1) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    have ht : ∀ y ∈ xs, y ≠ separator := fun y hy => hx y (by simp [hy])
    have hx' := hx x (by simp)
    simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    rw [run,last_step xs x hx',Option.bind_some]
    exact ih ht

theorem resets (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ separator) :
    HoareTime program (fun v => v = one (marked xs) (1+xs.length))
      (fun v => v = one (fun _ => blank) 0) (xs.length+2) := by
  have hfirst : step program (cfg (marked xs) (1+xs.length) 0) = some (cfg (marked xs) xs.length 1) := by
    simp only [step,program,cfg,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; omega
    · funext i z; by_cases hz : z=1+xs.length <;> simp [hz]
  have hlast : step program (cfg (a := a) empty 0 1) = some (cfg (fun _ => blank) 0 2) := by
    simp [step,program,cfg,empty,Move.offset]
    funext i z
    by_cases hz : z=0 <;> simp [hz]
  rintro v rfl
  refine ⟨xs.length+2,cfg (fun _ => blank) 0 2,le_rfl,?_,?_,rfl⟩
  · change run program (xs.length+2) (cfg (marked xs) (1+xs.length) 0) = _
    rw [show xs.length+2=1+xs.length+1 by omega,run_add,run_add,run_one,hfirst]
    simp only [Option.bind_some,erase_run xs hx,run_one,hlast]
  · simp [step,program,cfg]

/-- The same delimiter-bearing stream can be physically rewound without
erasing it, using its unique marker rather than the interior blank symbols. -/
def rewind : Program 1 3 a := seq (Rewind.program separator) StepRight.program

theorem rewinds (xs : List (Fin (a+4))) (hx : ∀ x ∈ xs, x ≠ separator) :
    HoareTime rewind (fun v => v = one (marked xs) (1+xs.length))
      (fun v => v = one (marked xs) 1) (xs.length+3) := by
  have hr := Rewind.rewind_hoare (separator : Fin (a+4)) (marked xs) (1+xs.length) (xs.length+1)
    (by
      intro j hj
      by_cases he : j=0
      · subst j
        rw [Nat.cast_zero,sub_zero,marked,putWord_outside _ _ _ _ (Or.inr le_rfl)]
        simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega,blank,separator]
      · have hz : 1 ≤ (1 : ℤ)+xs.length-j ∧ (1 : ℤ)+xs.length-j < 1+xs.length := by omega
        exact hx _ (ReturnOrigin.putWord_mem empty 1 xs _ hz))
    (by
      rw [show (1 : ℤ)+xs.length-(xs.length+1 : ℕ)=0 by omega,marked,
        putWord_outside _ _ _ _ (Or.inl (by omega))]
      rfl)
  have hr' : HoareTime (Rewind.program (separator : Fin (a+4)))
      (fun v => v = one (marked xs) (1+xs.length)) (fun v => v = one (marked xs) 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,show (1 : ℤ)+xs.length-(xs.length+1 : ℕ)=0 by omega] using hr
  exact (hr'.seq (StepRight.step_hoare (marked xs) 0)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.MarkedControlStreamReset
