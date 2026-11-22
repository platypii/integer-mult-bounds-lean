module

public import IntegerMultBounds.MathlibTM2.Host.GatherRecords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Stream record selectors from a single tape, preserving the source block. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node Mult.PhaseCellToeplitz

def sweepGatherRow {P U : Type} {Q A : ℕ} : Pr P 10 Q A U :=
  .seq (movePrefix 4 0 5 6 7) (.seq (gatherRecords 2 5 3 6 7 8 9 1 6
    (fun x => decide (x = bitSymbol true))) (uclear 5))

def sweepGatherStacks {A : ℕ} (S : Stacks 10 A) (stream out : List (Fin (A+4))) : Stacks 10 A :=
  {S with R := Function.update (Function.update S.R 0 stream) 1 out}

private theorem gatherRow_exec {P U : Type} {Q A W : ℕ} (body : P → Pr P 10 Q A U)
    (rows : List (List (Fin (A+4)))) (flags : List Bool) (hlen : flags.length = rows.length)
    (width : ∀ row ∈ rows, row.length = W) (rest out tail : List (Fin (A+4)))
    (v : HS 10 Q A U) (S : Stacks 10 A) (input : S.R 2 = rows.flatten ++ tail)
    (clock : (S.R 4).length = rows.length) (record : (S.R 3).length = W)
    (fresh : ∀ k : Fin 10, 5 ≤ k.val → S.R k = []) :
    ∃ z steps, z.user = v.user ∧ steps ≤ rows.length*(16*W+18)+24 ∧ Exec body sweepGatherRow
      (mk v (sweepGatherStacks S (flags.map bitSymbol ++ rest) out)) steps
      (mk z (sweepGatherStacks S rest ((gatherSymbols rows flags).flatten ++ out))) := by
  let mask := flags.map (bitSymbol (a := A))
  let start := sweepGatherStacks S (mask ++ rest) out
  let loaded : Stacks 10 A := {start with R := Function.update (Function.update start.R 0 rest) 5 mask}
  obtain ⟨u,hu,load⟩ := movePrefix_exec (body := body) (count := 4) (src := 0) (dst := 5)
    (saved := 6) (tmp := 7) (by decide) mask rest v start (by simp [start,sweepGatherStacks])
    (by simpa [start,sweepGatherStacks,mask,hlen] using clock)
    (by simpa [start,sweepGatherStacks] using fresh 6 (by decide))
    (by simpa [start,sweepGatherStacks] using fresh 7 (by decide))
  have enter : Exec body (movePrefix 4 0 5 6 7) (mk v start) (6*mask.length+6) (mk u loaded) := by
    simpa [loaded,start,sweepGatherStacks,fresh 5 (by decide)] using load
  obtain ⟨y,t,hy,paid,run⟩ := gatherRecords_exec (body := body) (src := 2) (mask := 5)
    (width := 3) (symbols := 6) (ts := 7) (tm := 8) (acc := 9) (out := 1) (cs := 6)
    (by decide) mask rows W (fun x => decide (x = bitSymbol true)) (by simp [mask,hlen])
    width tail u loaded (by simpa [loaded,start,sweepGatherStacks] using input) (by simp [loaded])
    (by simpa [loaded,start,sweepGatherStacks] using record) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl <;> simp [loaded,start,sweepGatherStacks,fresh])
  have decode (b : Bool) : decide (bitSymbol (a := A) b = bitSymbol true) = b := by cases b <;> rfl
  have decoded : mask.map (fun x => decide (x = bitSymbol true)) = flags := by
    simp [mask,List.map_map,Function.comp_def,decode]
  rw [decoded] at run
  let kept := (gatherSymbols rows flags).flatten ++ out
  let gathered : Stacks 10 A := {loaded with R := Function.update loaded.R 1 kept}
  have gather := run
  simp only [loaded,start,sweepGatherStacks,Function.update_of_ne (by decide : (1 : Fin 10) ≠ 5),Function.update_of_ne (by decide : (1 : Fin 10) ≠ 0),Function.update_self] at gather
  change Exec _ _ _ _ (mk y gathered) at gather
  obtain ⟨z,hz,clear⟩ := uclear_exec (body := body) 5 y gathered
  refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq enter (Exec.seq gather clear)).cast rfl ?_⟩
  · simp [gathered,loaded,mask,hlen] at paid ⊢
    ring_nf at paid ⊢
    omega
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    fin_cases k <;> simp [gathered,loaded,start,sweepGatherStacks,kept,fresh]

def sweepGatherLoop {P U : Type} {Q A : ℕ} : Pr P 10 Q A U :=
  .loop (·.flag) (sweepGatherRow.seq (.act (peekR 0)))

def sweepGatherProgram {P U : Type} {Q A : ℕ} : Pr P 10 Q A U :=
  .seq (.act (peekR 0)) sweepGatherLoop

private theorem gatherLoop_exec {P U : Type} {Q A W : ℕ} (body : P → Pr P 10 Q A U)
    (rows : List (List (Fin (A+4)))) (nonempty : 0 < rows.length)
    (width : ∀ row ∈ rows, row.length = W) (tail : List (Fin (A+4))) (S : Stacks 10 A)
    (input : S.R 2 = rows.flatten ++ tail) (clock : (S.R 4).length = rows.length)
    (record : (S.R 3).length = W) (fresh : ∀ k : Fin 10, 5 ≤ k.val → S.R k = [])
    (masks : List (List Bool)) (sizes : ∀ m ∈ masks, m.length = rows.length)
    (v : HS 10 Q A U) (out : List (Fin (A+4)))
    (flag : v.flag = (masks.flatten.map (bitSymbol (a := A))).head?.isSome) :
    ∃ z steps, z.user = v.user ∧ Exec body sweepGatherLoop
      (mk v (sweepGatherStacks S (masks.flatten.map bitSymbol) out)) steps
      (mk z (sweepGatherStacks S [] (masks.foldl (fun acc m => (gatherSymbols rows m).flatten ++ acc) out))) ∧
      steps ≤ masks.length*(rows.length*(16*W+18)+26)+1 := by
  induction masks generalizing v out with
  | nil => exact ⟨v,1,rfl,Exec.loop_false flag,by simp⟩
  | cons m ms ih =>
    have len := sizes m (by simp)
    have on : v.flag = true := by
      cases m with
      | nil => simp at len; omega
      | cons b m => simpa using flag
    let rest := ms.flatten.map (bitSymbol (a := A))
    let dst := (gatherSymbols rows m).flatten ++ out
    obtain ⟨u,t,user,paid,run⟩ := gatherRow_exec body rows m len width rest out tail v S input clock record fresh
    let z := {u with flag := ((sweepGatherStacks S rest dst).R 0).head?.isSome}
    have peek : Exec body (.act (peekR 0)) (mk u (sweepGatherStacks S rest dst)) 1
        (mk z (sweepGatherStacks S rest dst)) := Exec.act _ _
    obtain ⟨v',k,same,loop,bill⟩ := ih (fun x hx => sizes x (by simp [hx])) z dst (by simp [z,sweepGatherStacks,rest])
    refine ⟨v',t+1+k+1,same.trans user,?_,?_⟩
    · simpa only [sweepGatherLoop,List.flatten_cons,List.map_append,List.foldl_cons,rest,dst] using
        Exec.loop_true (f := fun x : HS 10 Q A U => x.flag) on (Exec.seq run peek) loop
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

/-- A fixed ten-register program consumes a stream of selector masks. The
last selected record appears first because each pass prepends its output. -/
theorem sweepGatherProgram_exec {P U : Type} {Q A W : ℕ} (body : P → Pr P 10 Q A U)
    (rows : List (List (Fin (A+4)))) (nonempty : 0 < rows.length)
    (width : ∀ row ∈ rows, row.length = W) (tail : List (Fin (A+4))) (S : Stacks 10 A)
    (input : S.R 2 = rows.flatten ++ tail) (clock : (S.R 4).length = rows.length)
    (record : (S.R 3).length = W) (fresh : ∀ k : Fin 10, 5 ≤ k.val → S.R k = [])
    (masks : List (List Bool)) (sizes : ∀ m ∈ masks, m.length = rows.length)
    (v : HS 10 Q A U) (out : List (Fin (A+4))) :
    ∃ z steps, z.user = v.user ∧ Exec body sweepGatherProgram
      (mk v (sweepGatherStacks S (masks.flatten.map bitSymbol) out)) steps
      (mk z (sweepGatherStacks S [] (masks.foldl (fun acc m => (gatherSymbols rows m).flatten ++ acc) out))) ∧
      steps ≤ masks.length*(rows.length*(16*W+18)+26)+2 := by
  let tape := masks.flatten.map (bitSymbol (a := A))
  let u := {v with flag := ((sweepGatherStacks S tape out).R 0).head?.isSome}
  have peek : Exec body (.act (peekR 0)) (mk v (sweepGatherStacks S tape out)) 1
      (mk u (sweepGatherStacks S tape out)) := Exec.act _ _
  obtain ⟨z,t,user,run,paid⟩ := gatherLoop_exec body rows nonempty width tail S input clock record fresh masks sizes u out (by simp [u,sweepGatherStacks,tape])
  exact ⟨z,1+t,user,Exec.seq peek run,by omega⟩

/-- One bit per source record in physical scan order. -/
def recordMask {n : ℕ} (i : Fin n) : List Bool :=
  List.replicate i.val false ++ true :: List.replicate (n-(i.val+1)) false

private theorem recordMask_length {n : ℕ} (i : Fin n) : (recordMask i).length = n := by
  simp [recordMask]
  omega

private theorem gather_recordMask {α : Type} (rows : List α) (i : Fin rows.length) :
    gatherSymbols rows (recordMask i) = [rows[i.val]] := by
  have split := List.take_append_drop i.val rows
  rw [List.drop_eq_getElem_cons i.isLt] at split
  conv_lhs => arg 1; rw [← split]
  unfold recordMask
  rw [gatherSymbols_append _ _ _ _ (by simp)]
  have pre := gatherSymbols_replicate (rows.take i.val) false
  have post := gatherSymbols_replicate (rows.drop (i.val+1)) false
  simp only [List.length_take,Nat.min_eq_left i.isLt.le,List.length_drop] at pre post
  simp [pre,post,gatherSymbols]

/-- The stream enumerates destinations backwards because the machine prepends
each copied record. The permutation maps source indices to destinations. -/
def permutationMasks {n : ℕ} (p : Equiv.Perm (Fin n)) : List (List Bool) :=
  (List.ofFn fun j => recordMask (p.symm j)).reverse

theorem sweepGatherPermutation_exec {P U : Type} {Q A W n : ℕ} (body : P → Pr P 10 Q A U)
    (p : Equiv.Perm (Fin n)) (rows : Fin n → List (Fin (A+4))) (nonempty : 0 < n)
    (width : ∀ i, (rows i).length = W) (tail : List (Fin (A+4))) (S : Stacks 10 A)
    (input : S.R 2 = (List.ofFn rows).flatten ++ tail) (clock : (S.R 4).length = n)
    (record : (S.R 3).length = W) (fresh : ∀ k : Fin 10, 5 ≤ k.val → S.R k = [])
    (v : HS 10 Q A U) (out : List (Fin (A+4))) :
    ∃ z steps, z.user = v.user ∧ Exec body sweepGatherProgram
      (mk v (sweepGatherStacks S ((permutationMasks p).flatten.map bitSymbol) out)) steps
      (mk z (sweepGatherStacks S [] ((List.ofFn (fun j => rows (p.symm j))).flatten ++ out))) ∧
      steps ≤ n*(n*(16*W+18)+26)+2 := by
  have select (i : Fin n) : gatherSymbols (List.ofFn rows) (recordMask i) = [rows i] := by
    simpa [recordMask] using gather_recordMask (List.ofFn rows) (i.cast (List.length_ofFn.symm))
  have masks : ∀ m ∈ permutationMasks p, m.length = (List.ofFn rows).length := by
    intro m hm
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hm)
    simp [recordMask_length]
  obtain ⟨z,t,user,run,bill⟩ := sweepGatherProgram_exec body (List.ofFn rows) (by simpa using nonempty)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact width i) tail S input (by simpa using clock)
    record fresh (permutationMasks p) masks v out
  refine ⟨z,t,user,?_,by simpa [permutationMasks] using bill⟩
  have output (js : List (Fin n)) (dst : List (Fin (A+4))) :
      (js.map (fun j => recordMask (p.symm j))).reverse.foldl
        (fun acc m => (gatherSymbols (List.ofFn rows) m).flatten ++ acc) dst =
      (js.map (fun j => rows (p.symm j))).flatten ++ dst := by
    induction js with
    | nil => rfl
    | cons j js ih => simp [List.foldl_append,ih,select,List.append_assoc]
  have ordered := output (List.finRange n) out
  rw [← List.ofFn_eq_map,← List.ofFn_eq_map] at ordered
  simpa only [permutationMasks,ordered] using run

end IntegerMultBounds.MathlibTM2.M6.BitNode
