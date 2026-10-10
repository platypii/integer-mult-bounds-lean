import IntegerMultBounds.Machine.RadixDigits
import IntegerMultBounds.Machine.Hoare

/-! One fixed native radix-two word machine copies the arithmetic right shift
with sign extension. Both words retain their length; source digits use the
same six-symbol alphabet as actual native Gaussian records. -/
namespace IntegerMultBounds.Machine.RadixSignedShiftRight
open RadixDigits

abbrev Word := List (Fin 2)
def shifted (xs : Word) := xs.tail++[xs.getLastD 0]
def track (last : Fin 2) : Fin 4 := ⟨last.val+1,by omega⟩
def program : Program 2 4 2 where
  tapes_pos := by decide
  start := 0
  transition := fun state sy =>
    if state=3 then none
    else if state=0 then
      match readDigit (sy 0) with
      | none => none
      | some digit => some (track digit,fun i => (sy i,if i=0 then .right else .stay))
    else match readDigit (sy 0) with
      | some digit => some (track digit,fun i => if i=0 then (sy i,.right) else (digitSymbol digit,.right))
      | none => some (3,fun i => if i=0 then (sy i,.stay) else
          (digitSymbol (if state=2 then 1 else 0),.right))

def cfg (f g : ℤ → Fin 6) (p q : ℤ) (state : Fin 4) : Config 2 4 2 :=
  ⟨state,fun i => if i=0 then p else q,fun i => if i=0 then f else g⟩
def tapes (f g : ℤ → Fin 6) (p q : ℤ) := (cfg f g p q 0).tapes

private theorem digit_step (x last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ)
    (hx : f p=digitSymbol x) :
    step program (cfg f g p q (track last)) =
      some (cfg f (Function.update g q (digitSymbol x)) (p+1) (q+1) (track x)) := by
  unfold step
  have ht : program.transition (track last) (fun i => (cfg f g p q (track last)).tape i ((cfg f g p q (track last)).head i))=
      some (track x,fun i => if i=0 then (f p,Move.right) else (digitSymbol x,Move.right)) := by
    fin_cases last <;> simp [program,track,cfg,hx,readDigit_symbol]
    all_goals funext i; fin_cases i <;> simp [hx]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk (track x) h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]; intro h; subst z; rfl

private theorem copy_run (xs : Word) (last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ) :
    run program xs.length (cfg (putWord f p (xs.map digitSymbol)) g p q (track last))=
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g q (xs.map digitSymbol))
        (p+xs.length) (q+xs.length) (track (xs.getLastD last))) := by
  induction xs generalizing last f g p q with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := digit_step x last (putWord f p ((x::xs).map digitSymbol)) g p q
      (by rw [List.map_cons,putWord_head])
    rw [List.length_cons,add_comm,run_add,run_one,hs]
    simp only [Option.bind_some,List.map_cons,putWord_cons,List.getLastD_cons]
    have hr := ih x (Function.update f p (digitSymbol x)) (Function.update g q (digitSymbol x)) (p+1) (q+1)
    rw [hr]
    congr 2 <;> push_cast <;> ring

private theorem exit_step (last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ) (hf : f p=blank) :
    step program (cfg f g p q (track last))=
      some (cfg f (Function.update g q (digitSymbol last)) p (q+1) 3) := by
  unfold step
  have ht : program.transition (track last) (fun i => (cfg f g p q (track last)).tape i ((cfg f g p q (track last)).head i))=
      some (3,fun i => if i=0 then (f p,Move.stay) else (digitSymbol last,Move.right)) := by
    fin_cases last <;> simp [program,track,cfg,hf,readDigit_blank]
    all_goals funext i; fin_cases i <;> simp [hf]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk 3 h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]; intro h; subst z; rfl

private theorem start_step (x : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ)
    (hx : f p=digitSymbol x) :
    step program (cfg f g p q 0)=some (cfg f g (p+1) q (track x)) := by
  unfold step
  have ht : program.transition 0 (fun i => (cfg f g p q 0).tape i ((cfg f g p q 0).head i))=
      some (track x,fun i => (if i=0 then f p else g q,if i=0 then Move.right else Move.stay)) := by
    simp [program,cfg,hx]
    funext i; fin_cases i <;> simp [hx]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk (track x) h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [eq_comm] <;>
      intro h <;> subst z <;> rfl

/-- Literal native execution, preserving the source and both field widths.
The source end must be blank; no condition is imposed on the output background. -/
theorem run_word (x : Fin 2) (xs : Word) (f g : ℤ → Fin 6) (p q : ℤ)
    (hf : f (p+(x::xs).length)=blank) :
    run program ((x::xs).length+1)
      (cfg (putWord f p ((x::xs).map digitSymbol)) g p q 0)=
    some (cfg (putWord f p ((x::xs).map digitSymbol))
      (putWord g q ((shifted (x::xs)).map digitSymbol))
      (p+(x::xs).length) (q+(x::xs).length) 3) := by
  have hs := start_step x (putWord f p ((x::xs).map digitSymbol)) g p q
    (by rw [List.map_cons,putWord_head])
  have hc := copy_run xs x (Function.update f p (digitSymbol x)) g (p+1) q
  rw [←putWord_cons,←List.map_cons] at hc
  have he : putWord f p ((x::xs).map digitSymbol) (p+(x::xs).length)=blank := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
  have hxlen : p+1+(xs.length:ℤ)=p+(x::xs).length := by simp; ring
  rw [hxlen] at hc
  have ht := exit_step (xs.getLastD x) (putWord f p ((x::xs).map digitSymbol))
    (putWord g q (xs.map digitSymbol)) (p+(x::xs).length) (q+xs.length) he
  rw [show (x::xs).length+1=1+(xs.length+1) by simp; omega,run_add,run_one,hs]
  simp only [Option.bind_some]
  rw [run_add,hc]
  simp only [Option.bind_some,run_one]
  rw [ht]
  have hg : Function.update (putWord g q (xs.map digitSymbol)) (q+xs.length)
      (digitSymbol (xs.getLastD x)) =
      putWord g q ((shifted (x::xs)).map digitSymbol) := by
    change putWord (putWord g q (xs.map digitSymbol)) (q+xs.length)
      [digitSymbol (xs.getLastD x)] = _
    rw [←List.length_map (f:=digitSymbol) (as:=xs),putWord_append_forward]
    simp only [shifted,List.tail_cons,List.map_append,List.map_singleton,List.getLastD_cons]
  rw [hg]
  congr 2; simp; ring

theorem halted (f g : ℤ → Fin 6) (p q : ℤ) : step program (cfg f g p q 3)=none := by
  simp [step,program,cfg]

/-- The word transducer's full exact tape contract, with affine runtime. -/
theorem hoare_word (x : Fin 2) (xs : Word) (f g : ℤ → Fin 6) (p q : ℤ)
    (hf : f (p+(x::xs).length)=blank) :
    HoareTime program
      (fun v => v=tapes (putWord f p ((x::xs).map digitSymbol)) g p q)
      (fun v => v=tapes (putWord f p ((x::xs).map digitSymbol))
        (putWord g q ((shifted (x::xs)).map digitSymbol))
        (p+(x::xs).length) (q+(x::xs).length)) ((x::xs).length+1) := by
  intro v hv
  subst v
  refine ⟨(x::xs).length+1,_,le_rfl,run_word x xs f g p q hf,halted _ _ _ _,rfl⟩

theorem shifted_length (xs : Word) (h : xs≠[]) : (shifted xs).length=xs.length := by
  cases xs with
  | nil => contradiction
  | cons x xs => simp [shifted]

end IntegerMultBounds.Machine.RadixSignedShiftRight
