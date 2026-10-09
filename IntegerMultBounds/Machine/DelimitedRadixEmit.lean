import IntegerMultBounds.Machine.DelimitedRadixRead

/-! Emit an actual arithmetic result word as one delimited stream field.
The result tape is erased completely and its head restored for the next call. -/
namespace IntegerMultBounds.Machine.DelimitedRadixEmit
open MarkedWordCleanup (one empty marked word)
open RadixDigits
variable {q : ℕ}

def finishProgram : Program 2 2 q where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s=0 then some (1,fun i =>
    if i=0 then (blank,Move.stay) else (separator,Move.right)) else none

theorem finish_runs (g : ℤ → Fin (q+4)) (p : ℤ) :
    HoareTime finishProgram (fun v => v=Copy.tapes empty g 0 p)
      (fun v => v=Copy.tapes (fun _ => blank) (Function.update g p separator) 0 (p+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(Copy.tapes (fun _ => blank) (Function.update g p separator) 0 (p+1)).head,
    (Copy.tapes (fun _ => blank) (Function.update g p separator) 0 (p+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,finishProgram,Copy.tapes,Copy.cfg,Config.tapes,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> by_cases hz : z=0 <;> simp [empty,Function.update_apply,hz]
  · simp [step,finishProgram]

theorem cleared (xs : List (Fin q)) :
    putWord (empty : ℤ → Fin (q+4)) 1 ((xs.map digitSymbol).map (Copy.retained true))=empty := by
  have h (ys : List (Fin (q+4))) (p : ℤ) (hp : 0<p) :
      putWord (empty : ℤ → Fin (q+4)) p (ys.map (fun _ => blank))=empty := by
    induction ys generalizing p with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons,putWord]
      have he : Function.update (empty : ℤ → Fin (q+4)) p blank=empty := by
        apply Function.update_eq_self_iff.mpr
        simp [empty,show p≠0 by omega]
      rw [ih (p+1) (by omega),he]
  exact h _ 1 (by omega)

def program : Program 2 6 q :=
  seq (seq (seq (extend MarkedWordCleanup.markProgram 1) (Copy.program blank true))
    (extend (Rewind.program separator) 1)) finishProgram

/-- Every output digit, the delimiter, all seeks, and scratch erasure are paid. -/
theorem runs (g : ℤ → Fin (q+4)) (p : ℤ) (xs : List (Fin q)) :
    HoareTime program
      (fun v => v=Copy.tapes (word (xs.map digitSymbol)) g 0 p)
      (fun v => v=Copy.tapes (fun _ => blank)
        (putWord g p (xs.map digitSymbol++[separator])) 0 (p+xs.length+1)) (2*xs.length+6) := by
  have hm := FamilyPlacementAlphabet.extend_hoare (MarkedWordCleanup.mark_hoare (xs.map digitSymbol)) (one g p)
  have hc := Copy.copy_hoare (blank : Fin (q+4)) true empty g 1 p (xs.map digitSymbol)
    (by intro z hz; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz; simp [digitSymbol,blank,Fin.ext_iff])
    (by simp [empty,show (1:ℤ)+xs.length≠0 by omega])
  simp only [List.length_map,cleared] at hc
  have hr0 := Rewind.rewind_hoare (separator : Fin (q+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j≠0 by omega,blank,separator,Fin.ext_iff])
    (by simp [empty])
  have hr1 : HoareTime (Rewind.program (separator : Fin (q+4)))
      (fun v => v=one empty (1+xs.length)) (fun v => v=one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr0
  have hr := FamilyPlacementAlphabet.extend_hoare hr1 (one (putWord g p (xs.map digitSymbol)) (p+xs.length))
  have hf := finish_runs (putWord g p (xs.map digitSymbol)) (p+xs.length)
  have ha : ∀ (u v : ℤ → Fin (q+4)) (j k : ℤ), (one u j).append (one v k)=Copy.tapes u v j k := by
    intro u v j k
    unfold one Tapes.append Copy.tapes Copy.cfg Config.tapes
    congr 1 <;> funext i <;> fin_cases i <;> rfl
  rw [ha,ha] at hm hr
  have ho : Function.update (putWord g p (xs.map digitSymbol)) (p+xs.length) separator=
      putWord g p (xs.map digitSymbol++[separator]) := by
    rw [←putWord_append_forward]
    simp [putWord]
  rw [ho] at hf
  exact (((hm.seq hc).seq hr).seq hf).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.DelimitedRadixEmit
