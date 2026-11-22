module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderTranspose

/-! Recover one active row from the ordinary compact layout in a sequential pass. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Mult.ShortConv

def splitActiveStep {P U : Type} {A Q : ℕ} : Pr P 8 Q A U :=
  (transfer 3 0 1 5).seq ((transfer 4 0 2 5).seq (.act (peekR 0)))

/-- Take the final field from every inherited block. Register 1 collects
the remaining prefixes and register 2 collects the extracted active row.
Both accumulate in reverse scan order. -/
theorem splitActiveRow_exec {P U : Type} {A Q : ℕ} (body : P → Pr P 8 Q A U)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (S : Stacks 8 A)
    (u : HS 8 Q A U) (old row : List (Fin (A+4))) (positive : 0 < (S.R 4).length)
    (width : ∀ r ∈ rows, r.1.length = (S.R 3).length ∧ r.2.length = (S.R 4).length)
    (free : S.R 5 = []) :
    let input := rows.flatMap (fun r => r.1++r.2)
    ∃ v, v.user = u.user ∧ Exec body (.seq (.act (peekR 0)) (.loop (·.flag) splitActiveStep))
      (mk u (mergeStacks S input old row)) (rows.length*(4*((S.R 3).length+(S.R 4).length)+10)+2)
      (mk v (mergeStacks S [] ((rows.flatMap Prod.fst).reverse++old) ((rows.flatMap Prod.snd).reverse++row))) := by
  intro input
  let fee := 4*((S.R 3).length+(S.R 4).length)+10
  let stream := fun (rs : List (List (Fin (A+4)) × List (Fin (A+4)))) => rs.flatMap (fun r => r.1++r.2)
  have loop (rs) (widths : ∀ r ∈ rs, r.1.length = (S.R 3).length ∧ r.2.length = (S.R 4).length)
      (v : HS 8 Q A U) (xs ys) (flag : v.flag = (stream rs).head?.isSome) :
      ∃ z, z.user = v.user ∧ Exec body (.loop (·.flag) splitActiveStep)
        (mk v (mergeStacks S (stream rs) xs ys)) (rs.length*fee+1)
        (mk z (mergeStacks S [] ((rs.flatMap Prod.fst).reverse++xs) ((rs.flatMap Prod.snd).reverse++ys))) := by
    induction rs generalizing v xs ys with
    | nil =>
      simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,List.flatMap_nil,List.reverse_nil,List.nil_append]
      exact ⟨v,rfl,Exec.loop_false flag⟩
    | cons r rs ih =>
      obtain ⟨hx,hy⟩ := widths r List.mem_cons_self
      have nonempty : stream (r::rs) ≠ [] := by
        intro h
        have len := congrArg List.length h
        simp only [stream,List.flatMap_cons,List.length_append,List.length_nil] at len
        omega
      have on : v.flag = true := by
        cases h : stream (r::rs) with
        | nil => contradiction
        | cons a as => simpa [h] using flag
      let C := mergeStacks S (stream (r::rs)) xs ys
      let D := mergeStacks S (r.2++stream rs) (r.1.reverse++xs) ys
      obtain ⟨v₁,h₁,read⟩ := transfer_exec (body := body) (count := 3) (src := 0) (dst := 1) (tmp := 5)
        (by decide) v C r.1 (r.2++stream rs) (by simp [C,mergeStacks,stream,List.append_assoc])
        (by simp [C,mergeStacks,hx]) (by simp [C,mergeStacks,free])
      have left : Exec body (transfer 3 0 1 5) (mk v C) (4*r.1.length+4) (mk v₁ D) := by
        apply read.cast rfl
        apply congrArg (mk v₁)
        refine Stacks.ext rfl rfl rfl ?_
        funext j
        fin_cases j <;> rfl
      let F := mergeStacks S (stream rs) (r.1.reverse++xs) (r.2.reverse++ys)
      obtain ⟨v₂,h₂,read₂⟩ := transfer_exec (body := body) (count := 4) (src := 0) (dst := 2) (tmp := 5)
        (by decide) v₁ D r.2 (stream rs) (by simp [D,mergeStacks])
        (by simp [D,mergeStacks,hy]) (by simp [D,mergeStacks,free])
      have right : Exec body (transfer 4 0 2 5) (mk v₁ D) (4*r.2.length+4) (mk v₂ F) := by
        apply read₂.cast rfl
        apply congrArg (mk v₂)
        refine Stacks.ext rfl rfl rfl ?_
        funext j
        fin_cases j <;> rfl
      let next := {v₂ with flag := (stream rs).head?.isSome}
      have peek : Exec body (.act (peekR 0)) (mk v₂ F) 1 (mk next F) := Exec.act _ _
      obtain ⟨z,user,rest⟩ := ih (fun r h => widths r (List.mem_cons_of_mem _ h)) next _ _ rfl
      refine ⟨z,user.trans (h₂.trans h₁),(Exec.loop_true on (Exec.seq left (Exec.seq right peek)) rest).cast ?_ ?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul,fee,hx,hy]; omega
      · simp [List.reverse_append,List.append_assoc]
  let next := {u with flag := input.head?.isSome}
  have peek : Exec body (.act (peekR 0)) (mk u (mergeStacks S input old row)) 1
      (mk next (mergeStacks S input old row)) := Exec.act _ _
  obtain ⟨v,user,run⟩ := loop rows width next old row rfl
  exact ⟨v,user,(Exec.seq peek run).cast (by dsimp only [fee]; omega) rfl⟩

/-- Undo one insertion: shorten the prefix counter by one field, split the
rectangle, restore the prefix order and prepend the extracted row to the return stream. -/
def extractActiveRow {P U : Type} {A Q : ℕ} : Pr P 8 Q A U :=
  (transfer 4 3 2 5).seq ((Node.uclear 2).seq
    ((Prog.seq (.act (peekR 0)) (.loop (·.flag) splitActiveStep)).seq ((moveR 1 0 id).seq (moveR 2 6 id))))

theorem extractActiveRow_exec {P U : Type} {A Q : ℕ} (body : P → Pr P 8 Q A U)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (S : Stacks 8 A) (u : HS 8 Q A U)
    (rest prefixWidth recordWidth rowWidth : List (Fin (A+4))) (positive : 0 < recordWidth.length)
    (width : ∀ r ∈ rows, r.1.length = prefixWidth.length ∧ r.2.length = recordWidth.length) :
    let old := rows.flatMap Prod.fst
    let incoming := rows.flatMap Prod.snd
    let combined := rows.flatMap (fun r => r.1++r.2)
    let start := transposeStacks S combined rest (recordWidth.reverse++prefixWidth) recordWidth rowWidth
    ∃ v steps, v.user = u.user ∧ Exec body extractActiveRow (mk u start) steps
      (mk v (transposeStacks S old (incoming++rest) prefixWidth recordWidth rowWidth)) ∧
      steps = 6*recordWidth.length + rows.length*(4*(prefixWidth.length+recordWidth.length)+10)+
        2*old.length+2*incoming.length+12 := by
  intro old incoming combined start
  let base := transposeStacks S combined rest prefixWidth recordWidth rowWidth
  obtain ⟨v₁,h₁,cut⟩ := transfer_exec (body := body) (count := 4) (src := 3) (dst := 2) (tmp := 5)
    (by decide) u start recordWidth.reverse prefixWidth rfl (by simp [start,transposeStacks]) rfl
  let C := mergeStacks base combined [] recordWidth
  have firstRun : Exec body (transfer 4 3 2 5) (mk u start) (4*recordWidth.length+4) (mk v₁ C) := by
    apply cut.cast (by simp)
    apply congrArg (mk v₁)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> first | rfl | (change recordWidth.reverse.reverse++[] = recordWidth; simp)
  obtain ⟨v₂,h₂,clear⟩ := Node.uclear_exec body 2 v₁ C
  have clearRun : Exec body (Node.uclear 2) (mk v₁ C) (2*recordWidth.length+2)
      (mk v₂ (mergeStacks base combined [] [])) := by
    apply clear.cast rfl
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> rfl
  obtain ⟨v₃,h₃,split⟩ := splitActiveRow_exec body rows base v₂ [] [] positive width rfl
  let D := mergeStacks base [] (old.reverse++[]) (incoming.reverse++[])
  let F := mergeStacks base old [] (incoming.reverse++[])
  obtain ⟨v₄,h₄,put⟩ := moveR_exec body 1 0 (by decide) id v₃ D
  have putRun : Exec body (moveR 1 0 id) (mk v₃ D) (2*old.length+2) (mk v₄ F) := by
    apply put.cast (by simp [D,mergeStacks])
    apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> first | rfl | (change ((old.reverse++[]).map id).reverse++[] = old; simp)
  obtain ⟨z,hz,write⟩ := moveR_exec body 2 6 (by decide) id v₄ F
  have writeRun : Exec body (moveR 2 6 id) (mk v₄ F) (2*incoming.length+2)
      (mk z (transposeStacks S old (incoming++rest) prefixWidth recordWidth rowWidth)) := by
    apply write.cast (by simp [F,mergeStacks])
    apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> first | rfl | (change ((incoming.reverse++[]).map id).reverse++rest = incoming++rest; simp)
  refine ⟨z,_,hz.trans (h₄.trans (h₃.trans (h₂.trans h₁))),
    Exec.seq firstRun (Exec.seq clearRun (Exec.seq split (Exec.seq putRun writeRun))),?_⟩
  change 4*recordWidth.length+4+(2*recordWidth.length+2+
    ((rows.length*(4*(prefixWidth.length+recordWidth.length)+10)+2)+(2*old.length+2+(2*incoming.length+2)))) = _
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
