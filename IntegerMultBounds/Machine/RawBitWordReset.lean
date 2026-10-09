import IntegerMultBounds.Machine.SelectedSourceBitsScan

/-! A marker-free Boolean word is erased backwards from its actual endpoint.
The adjacent blank restores head zero, including for the empty word. -/
namespace IntegerMultBounds.Machine.RawBitWordReset
open SelectedSourceBitsScan (word)
open MarkedWordCleanup (one)
variable {a : ℕ}

def program : Program 1 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then some (1,fun i => (sy i,Move.left))
    else if st=1 then if sy 0=blank then some (2,fun _ => (blank,Move.right))
      else some (1,fun _ => (blank,Move.left)) else none
private def cfg (f : ℤ → Fin (a+4)) (p : ℤ) (st : Fin 3) : Config 1 3 a :=
  ⟨st,fun _ => p,fun _ => f⟩

private theorem last_step (xs : List Bool) (b : Bool) :
    step (program (a := a)) (cfg (word (xs++[b])) xs.length 1)=
      some (cfg (word xs) (xs.length-1) 1) := by
  have ht : word (a := a) (xs++[b])=Function.update (word xs) xs.length (bitSymbol b) := by
    have h := putWord_append_forward (fun _ => (blank : Fin (a+4))) 0 (xs.map bitSymbol) [bitSymbol b]
    simpa only [word,List.map_append,List.map_cons,List.map_nil,List.length_map,zero_add,putWord] using h.symm
  have he : word (a := a) xs xs.length=blank := by
    unfold word
    rw [putWord_outside _ _ _ _ (Or.inr (by simp))]
  have hb : (bitSymbol b : Fin (a+4)) ≠ blank := by cases b <;> simp [bitSymbol,blank]
  have hread : word (a := a) (xs++[b]) xs.length=bitSymbol b := by rw [ht,Function.update_self]
  simp only [step,program,cfg,show (1 : Fin 3) ≠ 0 by decide,ite_false,ite_true,
    hread,hb,Move.offset]
  apply congrArg₂ (fun head tape => some (⟨1,head,tape⟩ : Config 1 3 a))
  · funext i; omega
  · funext i z
    by_cases hz : z=(xs.length : ℤ)
    · subst z; simp only [ite_true,he]
    · simp only [ite_eq_right hz,ht,Function.update_of_ne hz]

private theorem erases (xs : List Bool) :
    run (program (a := a)) xs.length (cfg (word xs) (xs.length-1) 1)=
      some (cfg (fun _ => blank) (-1) 1) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs b ih =>
    simp only [List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    rw [show xs.length+1=1+xs.length by omega,run_add,run_one]
    have hp : (xs.length : ℤ)+1-1=xs.length := by omega
    rw [hp,last_step,Option.bind_some]
    exact ih

theorem runs (xs : List Bool) :
    HoareTime (program (a := a)) (fun v => v=one (word xs) xs.length)
      (fun v => v=one (fun _ => blank) 0) (xs.length+2) := by
  have h0 : step (program (a := a)) ((one (word xs) xs.length).start program)=
      some (cfg (word xs) (xs.length-1) 1) := by
    simp only [step,program,Tapes.start,one,cfg,ite_true,Move.offset]
    apply congrArg₂ (fun head tape => some (⟨1,head,tape⟩ : Config 1 3 a))
    · funext i; omega
    · funext i z
      by_cases hz : z=(xs.length : ℤ) <;> simp [hz]
  have h1 : step (program (a := a)) (cfg (fun _ => blank) (-1) 1)=
      some (cfg (fun _ => blank) 0 2) := by
    change some (⟨2,fun _ => 0,fun _ z => if z=(-1 : ℤ) then blank else blank⟩ : Config 1 3 a)=
      some (⟨2,fun _ => 0,fun _ _ => blank⟩ : Config 1 3 a)
    congr 1
    congr 1
    funext i z
    split_ifs <;> rfl
  rintro v rfl
  refine ⟨xs.length+2,cfg (fun _ => blank) 0 2,le_rfl,?_,?_,rfl⟩
  · rw [show xs.length+2=1+xs.length+1 by omega,run_add,run_add,run_one,h0,
      Option.bind_some,erases,Option.bind_some,run_one,h1]
  · simp [step,program,cfg]

end IntegerMultBounds.Machine.RawBitWordReset
