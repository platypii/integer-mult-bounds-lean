module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactLayout

/-! Merge one active row into an already transposed rectangle from a compact input stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Mult.ShortConv

def mergeStep {P U : Type} {A Q : ℕ} : Pr P 8 Q A U :=
  (transfer 3 0 2 5).seq ((transfer 4 1 2 5).seq (.act (peekR 1)))

def mergeRow {P U : Type} {A Q : ℕ} : Pr P 8 Q A U :=
  .seq (.act (peekR 1)) (.loop (·.flag) mergeStep)

def mergeStacks {A : ℕ} (S : Stacks 8 A) (x y acc : List (Fin (A+4))) : Stacks 8 A :=
  { S with R := Function.update (Function.update (Function.update S.R 0 x) 1 y) 2 acc }

/-- Each pair contains the old active fields of one inherited block and the
new field. Both widths are read from reusable unary counters. -/
theorem mergeRow_exec {P U : Type} {A Q : ℕ} (body : P → Pr P 8 Q A U)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (S : Stacks 8 A)
    (u : HS 8 Q A U) (acc : List (Fin (A+4))) (positive : 0 < (S.R 4).length)
    (width : ∀ r ∈ rows, r.1.length = (S.R 3).length ∧ r.2.length = (S.R 4).length)
    (free : S.R 5 = []) :
    let start := mergeStacks S (rows.flatMap Prod.fst) (rows.flatMap Prod.snd) acc
    let output := rows.flatMap (fun r => r.1++r.2)
    ∃ v, v.user = u.user ∧ Exec body mergeRow (mk u start)
      (rows.length*(4*((S.R 3).length+(S.R 4).length)+10)+2)
      (mk v (mergeStacks S [] [] (output.reverse++acc))) := by
  intro start output
  let fee := 4*((S.R 3).length+(S.R 4).length)+10
  have loop (rs : List (List (Fin (A+4)) × List (Fin (A+4)))) (widths : ∀ r ∈ rs,
      r.1.length = (S.R 3).length ∧ r.2.length = (S.R 4).length) (v : HS 8 Q A U) (zs)
      (flag : v.flag = (rs.flatMap Prod.snd).head?.isSome) :
      ∃ z, z.user = v.user ∧ Exec body (.loop (·.flag) mergeStep)
        (mk v (mergeStacks S (rs.flatMap Prod.fst) (rs.flatMap Prod.snd) zs))
        (rs.length*fee+1) (mk z (mergeStacks S [] [] ((rs.flatMap (fun r => r.1++r.2)).reverse++zs))) := by
    induction rs generalizing v zs with
    | nil =>
      simp only [List.length_nil,Nat.zero_mul,Nat.zero_add,List.flatMap_nil,List.reverse_nil,List.nil_append]
      exact ⟨v,rfl,Exec.loop_false flag⟩
    | cons r rs ih =>
      obtain ⟨hx,hy⟩ := widths r List.mem_cons_self
      have nonempty : r.2 ≠ [] := by intro h; rw [h] at hy; simp at hy; omega
      have on : v.flag = true := by
        cases h : r.2 with
        | nil => contradiction
        | cons a as => simpa [List.flatMap_cons,h] using flag
      let xs := rs.flatMap Prod.fst
      let ys := rs.flatMap Prod.snd
      let C := mergeStacks S (r.1++xs) (r.2++ys) zs
      obtain ⟨v₁,user₁,run₁⟩ := transfer_exec (body := body) (count := 3) (src := 0) (dst := 2) (tmp := 5)
        (by decide) v C r.1 xs (by simp [C,mergeStacks]) (by simp [C,mergeStacks,hx]) (by simp [C,mergeStacks,free])
      let D := mergeStacks S xs (r.2++ys) (r.1.reverse++zs)
      have step₁ : Exec body (transfer 3 0 2 5) (mk v C) (4*r.1.length+4) (mk v₁ D) := by
        apply run₁.cast rfl
        apply congrArg (mk v₁)
        refine Stacks.ext rfl rfl rfl ?_
        funext j
        fin_cases j <;> simp [C,D,mergeStacks]
      obtain ⟨v₂,user₂,run₂⟩ := transfer_exec (body := body) (count := 4) (src := 1) (dst := 2) (tmp := 5)
        (by decide) v₁ D r.2 ys (by simp [D,mergeStacks]) (by simp [D,mergeStacks,hy]) (by simp [D,mergeStacks,free])
      let acc' := r.2.reverse++(r.1.reverse++zs)
      let F := mergeStacks S xs ys acc'
      have step₂ : Exec body (transfer 4 1 2 5) (mk v₁ D) (4*r.2.length+4) (mk v₂ F) := by
        apply run₂.cast rfl
        apply congrArg (mk v₂)
        refine Stacks.ext rfl rfl rfl ?_
        funext j
        fin_cases j <;> simp [D,F,acc',mergeStacks]
      let next := {v₂ with flag := ys.head?.isSome}
      have test : Exec body (.act (peekR 1)) (mk v₂ F) 1 (mk next F) := by
        simpa [peekR_run,next,F,mergeStacks] using Exec.act (body := body) (peekR 1) (mk v₂ F)
      obtain ⟨z,user,rest⟩ := ih (fun a h => widths a (List.mem_cons_of_mem _ h)) next acc' rfl
      refine ⟨z,user.trans (user₂.trans user₁), (Exec.loop_true on (Exec.seq step₁ (Exec.seq step₂ test)) rest).cast ?_ ?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul,fee,hx,hy]; omega
      · simp [acc',List.reverse_append,List.append_assoc]
  let next := {u with flag := (rows.flatMap Prod.snd).head?.isSome}
  have test : Exec body (.act (peekR 1)) (mk u start) 1 (mk next start) := by
    simpa [peekR_run,start,mergeStacks,next] using Exec.act (body := body) (peekR 1) (mk u start)
  obtain ⟨v,user,run⟩ := loop rows width next acc rfl
  exact ⟨v,user,(Exec.seq test run).cast (by dsimp only [fee]; omega) rfl⟩

/-- Return the merged rectangle in forward order on the original prefix
register, clearing the output accumulator for the next active row. -/
theorem mergeRowForward_exec {P U : Type} {A Q : ℕ} (body : P → Pr P 8 Q A U)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (S : Stacks 8 A)
    (u : HS 8 Q A U) (positive : 0 < (S.R 4).length)
    (width : ∀ r ∈ rows, r.1.length = (S.R 3).length ∧ r.2.length = (S.R 4).length)
    (free : S.R 5 = []) :
    let output := rows.flatMap (fun r => r.1++r.2)
    ∃ v, v.user = u.user ∧ Exec body (mergeRow.seq (moveR 2 0 id))
      (mk u (mergeStacks S (rows.flatMap Prod.fst) (rows.flatMap Prod.snd) []))
      (rows.length*(4*((S.R 3).length+(S.R 4).length)+10)+2 + (2*output.length+2))
      (mk v (mergeStacks S output [] [])) := by
  intro output
  obtain ⟨v,user,run⟩ := mergeRow_exec body rows S u [] positive width free
  let D := mergeStacks S [] [] (output.reverse++[])
  obtain ⟨z,same,restore⟩ := moveR_exec body 2 0 (by decide) id v D
  refine ⟨z,same.trans user,(Exec.seq run restore).cast ?_ ?_⟩
  · simp [D,mergeStacks]
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> simp [D,mergeStacks,movedR]

/-- Stream register 6 holds the unread rows. Register 7 counts one entire
active row. Registers 3 and 4 count the accumulated and incoming record widths. -/
def transposeStacks {A} (S : Stacks 8 A) (old unread prefixWidth recordWidth rowWidth : List (Fin (A+4))) :
    Stacks 8 A :=
  {S with R := fun j => match j.val with
    | 0 => old
    | 3 => prefixWidth
    | 4 => recordWidth
    | 6 => unread
    | 7 => rowWidth
    | _ => []}

def insertActiveRow {P U : Type} {A Q : ℕ} : Pr P 8 Q A U :=
  (transfer 7 6 2 5).seq ((moveR 2 1 id).seq
    ((mergeRow.seq (moveR 2 0 id)).seq (Fast.copyR 4 3 5 id)))

theorem insertActiveRow_exec {P U : Type} {A Q : ℕ} (body : P → Pr P 8 Q A U)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (S : Stacks 8 A) (u : HS 8 Q A U)
    (rest prefixWidth recordWidth rowWidth : List (Fin (A+4))) (positive : 0 < recordWidth.length)
    (width : ∀ r ∈ rows, r.1.length = prefixWidth.length ∧ r.2.length = recordWidth.length)
    (size : (rows.flatMap Prod.snd).length = rowWidth.length) :
    let old := rows.flatMap Prod.fst
    let incoming := rows.flatMap Prod.snd
    let output := rows.flatMap (fun r => r.1++r.2)
    let start := transposeStacks S old (incoming++rest) prefixWidth recordWidth rowWidth
    ∃ v steps, v.user = u.user ∧ Exec body insertActiveRow (mk u start) steps
      (mk v (transposeStacks S output rest (recordWidth.reverse++prefixWidth) recordWidth rowWidth)) ∧
      steps = 6*rowWidth.length+rows.length*(4*(prefixWidth.length+recordWidth.length)+10)+
        2*output.length+4*recordWidth.length+14 := by
  intro old incoming output start
  let base := transposeStacks S old rest prefixWidth recordWidth rowWidth
  obtain ⟨v₁,h₁,read⟩ := transfer_exec (body := body) (count := 7) (src := 6) (dst := 2) (tmp := 5)
    (by decide) u start incoming rest rfl size.symm rfl
  let C := mergeStacks base old [] incoming.reverse
  have load : Exec body (transfer 7 6 2 5) (mk u start) (4*incoming.length+4) (mk v₁ C) := by
    as_aux_lemma =>
      apply read.cast rfl
      apply congrArg (mk v₁)
      refine Stacks.ext rfl rfl rfl ?_
      funext j
      fin_cases j <;> first | rfl | exact List.append_nil _
  obtain ⟨v₂,h₂,move⟩ := moveR_exec body 2 1 (by decide) id v₁ C
  have restore : Exec body (moveR 2 1 id) (mk v₁ C) (2*incoming.length+2)
      (mk v₂ (mergeStacks base old incoming [])) := by
    as_aux_lemma =>
      apply move.cast (by simp [C,mergeStacks])
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext j
      fin_cases j <;> first | rfl | (change (incoming.reverse.map id).reverse ++ [] = incoming; simp)
  obtain ⟨v₃,h₃,merge⟩ := mergeRowForward_exec body rows base v₂ positive width rfl
  let F := mergeStacks base output [] []
  obtain ⟨z,hz,advance⟩ := Fast.copyR_exec body 4 3 5 (by decide) (by decide) (by decide) id v₃ F rfl
  refine ⟨z,_,hz.trans (h₃.trans (h₂.trans h₁)),(Exec.seq load (Exec.seq restore (Exec.seq merge advance))).cast rfl ?_,?_⟩
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    fin_cases j <;> first | rfl | (change (recordWidth.map id).reverse ++ prefixWidth = recordWidth.reverse ++ prefixWidth; simp)
  · change 4*incoming.length+4 + (2*incoming.length+2 + (_ + (4*recordWidth.length+4))) = _
    change incoming.length = rowWidth.length at size
    change 4*incoming.length+4 + (2*incoming.length+2 +
      ((rows.length*(4*(prefixWidth.length+recordWidth.length)+10)+2+(2*output.length+2))+
      (4*recordWidth.length+4))) = _
    omega

/-- Inserting the final active row extends every inherited block by its
corresponding record, in exactly compact-transpose order. -/
theorem mergeTransposedRows {α : Type} {B a : ℕ} (word : Fin (a+1) → Fin B → List α) :
    let rows := List.ofFn (fun b => ((List.ofFn fun j : Fin a => word j.castSucc b).flatten,
      word (Fin.last a) b))
    rows.flatMap (fun r => r.1++r.2) =
      (List.ofFn (fun b => (List.ofFn fun j => word j b).flatten)).flatten := by
  intro rows
  simp only [rows,List.flatMap_def,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext b
  rw [List.ofFn_succ' (f := fun j => word j b)]
  simp

end IntegerMultBounds.MathlibTM2.M6.BitNode
