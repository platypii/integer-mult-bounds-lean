import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.Rewind
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced

/-! Move a canonical marked binary word into a forward delimiter-separated
queue. The source bits and marker are physically erased, while the queue
cursor advances through the appended field and delimiter. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorQueueEmit
noncomputable section
variable {a : ℕ}
open BinaryDescriptorStack (descriptor empty)

def finishProgram : Program 2 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s _ => if s=0 then some (1,fun i =>
    if i=0 then (blank,Move.stay) else (separator,Move.right)) else none

private theorem finish (g : ℤ → Fin (a+4)) (p : ℤ) :
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

private theorem erased (xs : List Bool) :
    putWord (empty : ℤ → Fin (a+4)) 1 ((xs.map bitSymbol).map (Copy.retained true))=empty := by
  have h (ys : List (Fin (a+4))) (p : ℤ) (hp : 0 < p) :
      putWord (empty : ℤ → Fin (a+4)) p (ys.map (fun _ => blank))=empty := by
    induction ys generalizing p with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_cons,putWord]
      have he : Function.update (empty : ℤ → Fin (a+4)) p blank=empty := by
        apply Function.update_eq_self_iff.mpr
        simp [empty,show p≠0 by omega]
      rw [ih (p+1) (by omega),he]
  exact h _ 1 (by omega)

def program : Program 2 4 a :=
  seq (seq (Copy.program blank true) (extend (Rewind.program separator) 1)) finishProgram

theorem runs (g : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) :
    HoareTime program (fun v => v=Copy.tapes (descriptor xs) g 1 p)
      (fun v => v=Copy.tapes (fun _ => blank)
        (putWord g p (xs.map bitSymbol++[separator])) 0 (p+xs.length+1)) (2*xs.length+5) := by
  have hc := Copy.copy_hoare (blank : Fin (a+4)) true empty g 1 p (xs.map bitSymbol)
    (by intro z hz; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hz; cases y <;> simp [bitSymbol,blank,Fin.ext_iff])
    (by simp [empty,show (1:ℤ)+xs.length≠0 by omega])
  simp only [List.length_map,erased] at hc
  have hr0 := Rewind.rewind_hoare (separator : Fin (a+4)) empty (xs.length+1) (xs.length+1)
    (by intro j hj; simp [empty,show (xs.length:ℤ)+1-j≠0 by omega,blank,separator,Fin.ext_iff])
    (by simp [empty])
  have hr1 : HoareTime (Rewind.program (separator : Fin (a+4)))
      (fun v => v=FiniteReturnStack.bank empty (1+xs.length)) (fun v => v=FiniteReturnStack.bank empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,FiniteReturnStack.bank,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr0
  have hr := hoare_extend_eq hr1 (FiniteReturnStack.bank (putWord g p (xs.map bitSymbol)) (p+xs.length))
  have ha : ∀ (u v : ℤ → Fin (a+4)) (j k : ℤ),
      (FiniteReturnStack.bank u j).append (FiniteReturnStack.bank v k)=Copy.tapes u v j k := by
    intro u v j k
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simp only [ha] at hr
  have hf := finish (putWord g p (xs.map bitSymbol)) (p+xs.length)
  have he : Function.update (putWord g p (xs.map bitSymbol)) (p+xs.length) separator =
      putWord g p (xs.map bitSymbol++[separator]) := by
    rw [← putWord_append_forward]
    simp [putWord]
  rw [he] at hf
  exact ((hc.seq hr).seq hf).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryDescriptorQueueEmit
