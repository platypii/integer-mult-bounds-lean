import IntegerMultBounds.Machine.DelimitedReverseCopy
import IntegerMultBounds.Machine.ReturnOrigin

/-! Fixed local controls for descriptor stacks: one physical adjustment and a
real delimiter scan that preserves every complete tape. -/
namespace IntegerMultBounds.Machine.DescriptorStackControl
variable {t a : ℕ}

def once (ht : 0 < t) (action : (Fin t → Fin (a+4)) → Fin t → Fin (a+4) × Move) : Program t 2 a :=
  ⟨ht,0,fun s sy => if s = 0 then some (1,action sy) else none⟩

def after (v : Tapes t a) (action : (Fin t → Fin (a+4)) → Fin t → Fin (a+4) × Move) : Tapes t a :=
  ⟨fun i => v.head i+(action (fun j => v.tape j (v.head j)) i).2.offset,
    fun i z => if z = v.head i then (action (fun j => v.tape j (v.head j)) i).1 else v.tape i z⟩

theorem once_hoare (ht : 0 < t) (action : (Fin t → Fin (a+4)) → Fin t → Fin (a+4) × Move)
    (v : Tapes t a) : HoareTime (once ht action) (fun w => w = v) (fun w => w = after v action) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(after v action).head,(after v action).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp [run_one,step,once,Tapes.start,after]
  · simp [step,once]

def seek (focus : Fin t) (stop : Fin (a+4)) (move : Move) : Program t 1 a :=
  ⟨Nat.zero_lt_of_lt focus.isLt,0,fun _ sy => if sy focus = stop then none
    else some (0,fun i => (sy i,if i = focus then move else Move.stay))⟩

def positioned (v : Tapes t a) (focus : Fin t) (p : ℤ) : Tapes t a :=
  ⟨Function.update v.head focus p,v.tape⟩

private theorem seek_step (v : Tapes t a) (focus : Fin t) (stop : Fin (a+4)) (move : Move)
    (p : ℤ) (h : v.tape focus p ≠ stop) :
    step (seek focus stop move) ((positioned v focus p).start (seek focus stop move)) =
      some ((positioned v focus (p+move.offset)).start (seek focus stop move)) := by
  simp only [step,seek,Tapes.start,positioned,Function.update_self,h,ite_false]
  congr 1
  congr 1
  · funext i
    by_cases hi : i = focus <;> simp [hi,Move.offset]
  · funext i z
    by_cases hz : z = Function.update v.head focus p i <;> simp [hz]

private theorem seek_run (v : Tapes t a) (focus : Fin t) (stop : Fin (a+4)) (move : Move)
    (p : ℤ) (n : ℕ) (h : ∀ j < n, v.tape focus (p+j*move.offset) ≠ stop) :
    run (seek focus stop move) n ((positioned v focus p).start (seek focus stop move)) =
      some ((positioned v focus (p+n*move.offset)).start (seek focus stop move)) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [run_add,ih (fun j hj => h j (by omega))]
    simp only [Option.bind_some,run_one,seek_step v focus stop move _ (h n (by omega))]
    congr 3
    push_cast
    ring

theorem seek_hoare (v : Tapes t a) (focus : Fin t) (stop : Fin (a+4)) (move : Move) (n : ℕ)
    (h : ∀ j < n, v.tape focus (v.head focus+j*move.offset) ≠ stop)
    (he : v.tape focus (v.head focus+n*move.offset) = stop) :
    HoareTime (seek focus stop move) (fun w => w = v)
      (fun w => w = positioned v focus (v.head focus+n*move.offset)) n := by
  have hr := seek_run v focus stop move (v.head focus) n h
  have hv : positioned v focus (v.head focus) = v := by cases v; simp [positioned]
  rw [hv] at hr
  intro w hw
  subst w
  refine ⟨n,_,le_rfl,hr,?_,rfl⟩
  simp [step,seek,Tapes.start,positioned,he]

end IntegerMultBounds.Machine.DescriptorStackControl
