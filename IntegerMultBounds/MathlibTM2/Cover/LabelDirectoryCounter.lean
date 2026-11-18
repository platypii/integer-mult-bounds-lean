module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectory
public import IntegerMultBounds.MathlibTM2.Host.Auto

/-! Emit a directory label while computing its successor in the same radix scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCounter
noncomputable section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open RadixDigits RadixCounterData Host Node
variable {q : ℕ} (hq : 2 ≤ q)

def digitStep (carry : Bool) (x : Fin q) : Bool × Fin q :=
  if carry then
    if h : x.val+1 < q then (false, ⟨x.val+1,h⟩) else (true,zeroDigit hq)
  else (false,x)

/-- Output zero copies the current label. Output one receives the next label. -/
def machine : Auto q 1 2 where
  init := bitSymbol true
  step := fun s col =>
    let x := (readDigit (col 0)).getD (zeroDigit hq)
    let y := digitStep hq (symBit s) x
    (bitSymbol y.1, ![col 0,digitSymbol y.2])

private def columns (xs : List (Fin q)) := xs.map fun x (_ : Fin 1) => digitSymbol x

private theorem scan (xs : List (Fin q)) (carry : Bool) (j : Fin 2) :
    (((machine hq).runWord (bitSymbol carry) (columns xs)).map (· j)) =
      (if j = 0 then xs else if carry then increment hq xs else xs).map digitSymbol := by
  induction xs generalizing carry j with
  | nil => cases carry <;> fin_cases j <;> rfl
  | cons x xs ih =>
    simp only [columns,List.map_cons,Auto.runWord,machine,symBit_bitSymbol,readDigit_symbol,
      Option.getD_some]
    change _ :: (((machine hq).runWord _ (columns xs)).map (· j)) = _
    rw [ih]
    cases carry <;> fin_cases j <;> by_cases hx : x.val+1 < q <;> simp [digitStep,increment,hx]

variable {T Q : ℕ} {P U : Type} {body : P → Pr P T Q q U}

/-- One host pass emits the current digits and the incremented digits on reverse accumulators. -/
theorem emit_exec {ins : Fin 1 → Fin T} {outs : Fin 2 → Fin T} {st width tmp : Fin T}
    (h : AutoLayout ins outs st width tmp) (xs : List (Fin q)) (hx : 0 < xs.length)
    (u : HS T Q q U) (S : Stacks T q) (hw : (S.R width).length = xs.length)
    (ht : S.R tmp = []) (hin : S.R (ins 0) = xs.map digitSymbol) :
    ∃ u' n, u'.user = u.user ∧ n ≤ 5*xs.length+8 ∧
      Exec body (autoWords ins outs st width tmp (machine hq)) (mk u S) n
        (mk u' {S with R := autoRegs S.R ins outs (fun j => (if j = 0 then xs else increment hq xs).map digitSymbol)}) := by
  obtain ⟨v,n,hu,hn,he⟩ := autoWords_exec_words body h (machine hq) hx hw [columns xs]
    (by simp [columns]) u S rfl ht (by intro i; fin_cases i; simpa [Auto.stream,columns,List.map_map,Function.comp_def] using hin)
  refine ⟨v,n,hu,by simpa [Nat.add_assoc] using hn,?_⟩
  have hout : (machine hq).outWords [columns xs] =
      fun j => (if j = 0 then xs else increment hq xs).map digitSymbol := by
    funext j
    simpa only [Auto.outWords,List.flatMap_singleton,ite_true,machine] using scan hq xs true j
  rwa [hout] at he

/-- Restore the incremented counter in reading order for the following record. -/
def tick (ins : Fin 1 → Fin T) (outs : Fin 2 → Fin T) (st width tmp : Fin T) : Pr P T Q q U :=
  .seq (autoWords ins outs st width tmp (machine hq)) (moveR (outs 1) (ins 0) id)

theorem tick_exec {ins : Fin 1 → Fin T} {outs : Fin 2 → Fin T} {st width tmp : Fin T}
    (h : AutoLayout ins outs st width tmp) (xs : List (Fin q)) (hx : 0 < xs.length)
    (u : HS T Q q U) (S : Stacks T q) (hw : (S.R width).length = xs.length)
    (ht : S.R tmp = []) (hs : S.R (outs 1) = []) (hin : S.R (ins 0) = xs.map digitSymbol) :
    ∃ u' n, u'.user = u.user ∧ n ≤ 7*xs.length+10 ∧
      Exec body (tick hq ins outs st width tmp) (mk u S) n
        (mk u' {S with R := Function.update (Function.update S.R (outs 0)
          ((xs.map digitSymbol).reverse ++ S.R (outs 0))) (ins 0) ((increment hq xs).map digitSymbol)}) := by
  let word (j : Fin 2) := (if j = 0 then xs else increment hq xs).map digitSymbol
  let M : Stacks T q := {S with R := autoRegs S.R ins outs word}
  obtain ⟨v,n,hu,hn,he⟩ := emit_exec (body := body) hq h xs hx u S hw ht hin
  obtain ⟨v',hu',he'⟩ := moveR_exec body (outs 1) (ins 0) (h.ins_outs 0 1).symm id v M
  have hc : M.R (ins 0) = [] := autoRegs_ins h.ins_inj 0
  have ho (j : Fin 2) : M.R (outs j) = (word j).reverse ++ S.R (outs j) :=
    autoRegs_outs h.outs_inj h.ins_outs j
  have hnxt : M.R (outs 1) = ((increment hq xs).map digitSymbol).reverse := by simp [ho,word,hs]
  refine ⟨v',_,hu'.trans hu,?_,(Exec.seq he he').cast rfl ?_⟩
  · simp only [hnxt,List.length_reverse,List.length_map,increment_length]; omega
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have h01 : outs 0 ≠ outs 1 := fun e => (by decide : (0 : Fin 2) ≠ 1) (h.outs_inj e)
    by_cases hi : k = ins 0
    · subst k; simp [movedR,hc,hnxt]
    by_cases ha : k = outs 0
    · subst k; simp [movedR,hi,h01,ho,word]
    by_cases hb : k = outs 1
    · subst k; simp [movedR,hi,ha,hs]
    simp only [movedR,Function.update_of_ne hi,Function.update_of_ne hb,Function.update_of_ne ha]
    apply autoRegs_of_notMem
    · rintro ⟨i,rfl⟩; fin_cases i; exact hi rfl
    · rintro ⟨j,rfl⟩; fin_cases j <;> contradiction

end
end IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCounter
