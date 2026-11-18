module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Pass padded payloads through the accumulator and consume their two pivot schedules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.ShortConv
variable {T Q A d : ℕ} {P U : Type}

/-- The terminating zero belongs to the current pivot. -/
def skipPivot (src : Fin T) : Pr P T Q A U :=
  .seq (.act (nextPivotBit src)) (.loop (·.flag) (.act (nextPivotBit src)))

theorem skipPivot_exec (body : P → Pr P T Q A U) (src : Fin T) (v : HS T Q A U) (S : Stacks T A)
    (n : ℕ) (tail : List (Fin (A+4))) (code : S.R src = pivotCode n ++ tail) :
    Exec body (skipPivot src) (mk v S) (2*(n+1)) (mk {v with flag := false} {S with R := Function.update S.R src tail}) := by
  have loop (k : ℕ) (D : Stacks T A) (packed : D.R src = pivotCode k ++ tail) :
      Exec body (.loop (·.flag) (.act (nextPivotBit src))) (mk {v with flag := true} D) (2*(k+1)+1)
        (mk {v with flag := false} {D with R := Function.update D.R src tail}) := by
    induction k generalizing D with
    | zero =>
      have pop := Exec.act (body := body) (nextPivotBit src) (mk {v with flag := true} D)
      simp [nextPivotBit,Action.run,packed,pivotCode,update_rt] at pop
      exact Exec.loop_true (m := 1) (n := 1) rfl pop (.loop_false rfl)
    | succ k ih =>
      let rest := pivotCode (A := A) k ++ tail
      have head : D.R src = bitSymbol true :: rest := by simp [packed,rest,pivotCode,List.replicate_succ]
      have pop := Exec.act (body := body) (nextPivotBit src) (mk {v with flag := true} D)
      simp [nextPivotBit,Action.run,head,update_rt] at pop
      have more := ih {D with R := Function.update D.R src rest} (by simp [rest])
      exact (Exec.loop_true (by rfl) pop more).cast (by omega) (by simp [Function.update_idem])
  cases n with
  | zero =>
    have pop := Exec.act (body := body) (nextPivotBit src) (mk v S)
    simp [nextPivotBit,Action.run,code,pivotCode,update_rt] at pop
    exact Exec.seq (m := 1) (n := 1) pop (.loop_false rfl)
  | succ k =>
    let rest := pivotCode (A := A) k ++ tail
    have head : S.R src = bitSymbol true :: rest := by simp [code,rest,pivotCode,List.replicate_succ]
    have pop := Exec.act (body := body) (nextPivotBit src) (mk v S)
    simp [nextPivotBit,Action.run,head,update_rt] at pop
    have more := loop k {S with R := Function.update S.R src rest} (by simp [rest])
    exact (Exec.seq pop more).cast (by omega) (by simp [Function.update_idem])

def skipPivots (src : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => .seq (skipPivot src) (skipPivots src n)

theorem skipPivots_exec (body : P → Pr P T Q A U) (src : Fin T) (rows : Fin d → Fin d) (order : List (Fin d))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (code : S.R src = orderedScheduleCode order rows ++ tail) :
    ∃ z, z.user = v.user ∧ Exec body (skipPivots src order.length) (mk v S)
      (2*(orderedScheduleCode (A := A) order rows).length+1) (mk z {S with R := Function.update S.R src tail}) := by
  induction order generalizing v S with
  | nil =>
    have h : S.R src = tail := by simpa [orderedScheduleCode] using code
    exact ⟨v,rfl,by simpa [skipPivots,orderedScheduleCode,← h] using (Exec.act (body := body) .done (mk v S))⟩
  | cons i is ih =>
    let rest := orderedScheduleCode (A := A) is rows ++ tail
    have pop := skipPivot_exec body src v S (rows i).val rest (by simpa [rest,orderedScheduleCode,List.append_assoc] using code)
    obtain ⟨z,hz,more⟩ := ih {v with flag := false} {S with R := Function.update S.R src rest} (by simp [rest])
    refine ⟨z,hz,(Exec.seq pop more).cast ?_ (by simp [Function.update_idem])⟩
    simp [orderedScheduleCode,pivotCode]; omega

def paddingRecord (d : ℕ) (pivot count src acc tmp : Fin T) : Pr P T Q A U :=
  .seq (skipPivots pivot (d+d)) (transfer count src acc tmp)

theorem paddingRecord_exec (body : P → Pr P T Q A U) (pivot count src acc tmp : Fin T)
    (regs : [pivot,count,src,acc,tmp].Nodup) (rows : Fin d → Fin d)
    (v : HS T Q A U) (S : Stacks T A) (word rest schedule : List (Fin (A+4)))
    (pivots : S.R pivot = scheduleCode rows ++ orderedScheduleCode (List.finRange d).reverse rows ++ schedule)
    (queue : S.R src = word ++ rest) (width : (S.R count).length = word.length) (scratch : S.R tmp = []) :
    let D := {S with R := Function.update S.R pivot schedule}
    ∃ z n, z.user = v.user ∧ n ≤ 4*d*d+1+(4*word.length+4) ∧ Exec body (paddingRecord d pivot count src acc tmp)
      (mk v S) n (mk z {D with R := Function.update (Function.update D.R src rest) acc (word.reverse ++ S.R acc)}) := by
  intro D
  let order := List.finRange d ++ (List.finRange d).reverse
  obtain ⟨u,hu,skip⟩ := skipPivots_exec body pivot rows order v S schedule
    (by simpa [order,scheduleCode,orderedScheduleCode] using pivots)
  have len : order.length = d+d := by simp [order]
  rw [len] at skip
  have bound (is : List (Fin d)) : (orderedScheduleCode (A := A) is rows).length ≤ is.length*d := by
    induction is with
    | nil => simp [orderedScheduleCode]
    | cons i is ih =>
      have lt := (rows i).isLt
      simp only [orderedScheduleCode,List.flatMap_cons,List.length_append,pivotCode,List.length_replicate,
        List.length_cons,List.length_nil,Nat.succ_mul] at *
      omega
  have cap := bound order
  rw [len,Nat.add_mul] at cap
  have others := (List.nodup_cons.mp regs).2
  regs_ne regs
  have keep (j : Fin T) (hj : j ≠ pivot) : D.R j = S.R j := Function.update_of_ne hj _ _
  obtain ⟨z,hz,move⟩ := transfer_exec (body := body) others u D word rest ((keep src ‹pivot ≠ src›.symm).trans queue)
    (by rw [keep count ‹pivot ≠ count›.symm,width]) ((keep tmp ‹pivot ≠ tmp›.symm).trans scratch)
  rw [keep acc ‹pivot ≠ acc›.symm] at move
  exact ⟨z,_,hz.trans hu,by nlinarith,Exec.seq skip move⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
