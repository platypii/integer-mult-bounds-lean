module

public import IntegerMultBounds.MathlibTM2.M6.BitParkedLeaf
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChart

/-! Prepare the ordinary directory descriptor and run its interleaved stopped MOVE. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

private def outerSlots (K : ℕ) := (List.finRange 3).map (fun j => stoppedChartHeader K 0 (j.castAdd 3))

private theorem restoreReplay {K Q : ℕ} {P U : Type} (body : P → Pr P (66+(K+3+0)) Q prime U)
    (lane : Descriptor) (S D : Stacks (66+(K+3+0)) prime) (v : HS (66+(K+3+0)) Q prime U)
    (initial : ∀ j : Fin 3, S.R (stoppedChartHeader K 0 (j.castAdd 3)) = [])
    (ready : StoppedChartReady K 0 lane D) (left : D.L = S.L)
    (stable : ∀ j, (∀ i : Fin 3, j ≠ stoppedChartHeader K 0 (i.castAdd 3)) → D.R j = S.R j) :
    ∃ u F, u.user = v.user ∧ Exec body (Prog.seqList ((outerSlots K).map WordCmd.dropR)) (mk v D)
      (((List.finRange 3).map fun j => 2*(Routines.hdr lane (j.castAdd 3)).length+2).sum+1)
      (mk u F) ∧ F.L = S.L ∧ F.R = S.R := by
  have address (j : Fin 3) : (stoppedChartHeader K 0 (j.castAdd 3)).val = 66+K+j.val := by
    simp [stoppedChartHeader,j.isLt]
  have inject : Function.Injective (fun j : Fin 3 => stoppedChartHeader K 0 (j.castAdd 3)) := by
    intro i j eq
    have h := congrArg Fin.val eq
    rw [address,address] at h
    exact Fin.ext (by omega)
  obtain ⟨u,F,user,run,l,r⟩ := retire_exec body (outerSlots K) ((List.nodup_finRange _).map inject) v D
  refine ⟨u,F,user,?_,l.trans left,?_⟩
  · simpa only [outerSlots,List.map_map,Function.comp_def,ready.1,List.length_map] using run
  · funext j
    rw [r]
    split_ifs with mem
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp mem
      exact (initial i).symm
    · exact stable j (fun i eq => mem (List.mem_map.mpr ⟨i,List.mem_finRange i,eq.symm⟩))

private theorem prepareReplay {K N Q : ℕ} {P U : Type} (body : P → Pr P N Q prime U)
    (view : Fin (66+(K+3+0)) ↪ Fin N) (parent : Descriptor) (lo hi w : ℕ)
    (positive : parent.Positive) (u : HS N Q prime U) (S : Stacks N prime) :
    let outer := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+0) by omega)
    let ports := directoryOuterHeaderBank K
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let lane := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
    (∀ j : Fin 3, (S.R (view (outer (ports (j.castAdd 9))))).length = values j) →
    (∀ j : Fin 12, 3 ≤ j.val → S.R (view (outer (ports j))) = []) →
    (∀ j : Fin 3, S.R (view (stoppedChartHeader K 0 (j.natAdd 3))) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
    ∃ y E a, y.user = u.user ∧ a ≤ 63*LabelMask.records parent+31 ∧
      Exec body (embProg view Empty.elim (embProg outer Empty.elim (IntervalDescriptor.directoryOuterHeaders ports)))
        (mk u S) a (mk y E) ∧ StoppedChartReady K 0 lane (embStk view E) ∧
      (∀ j, (∀ i, view i ≠ j) → E.L j = S.L j ∧ E.R j = S.R j) ∧
      ∀ (v : HS N Q prime U) (B : Stacks N prime),
        (∀ i, B.L (view i) = E.L (view i) ∧ B.R (view i) = E.R (view i)) →
        ∃ u G, u.user = v.user ∧ Exec body (embProg view Empty.elim (Prog.seqList ((outerSlots K).map WordCmd.dropR)))
          (mk v B) (((List.finRange 3).map fun j => 2*(Routines.hdr lane (j.castAdd 3)).length+2).sum+1)
          (mk u G) ∧ (∀ j, (∀ i, view i ≠ j) → G.L j = B.L j ∧ G.R j = B.R j) ∧ ∀ j, ((∀ i, view i ≠ j) → B.L j = S.L j ∧ B.R j = S.R j) →
          G.L j = S.L j ∧ G.R j = S.R j := by
  intro outer ports values row lane lengths clear inner
  obtain ⟨v,D,a,user,bill,exec,left,ready,stable⟩ := prepareStoppedChart_exec (K := K) (T := 0)
    (P := Empty) Empty.elim parent positive lo hi w (embDn view u) (embStk view S)
    lengths clear inner (fun j => Fin.elim0 j)
  obtain ⟨y,E,placed,_,same,viewEq,off⟩ := exec_emb (body' := body) (ι := Empty.elim)
    view.injective (fun e => nomatch e) exec u rfl S rfl
  refine ⟨y,E,a,same.trans user,bill,placed,viewEq ▸ ready,off,?_⟩
  intro z B keep
  have l : (embStk view B).L = D.L := by rw [← viewEq]; exact funext (fun i => (keep i).1)
  have r : (embStk view B).R = D.R := by rw [← viewEq]; exact funext (fun i => (keep i).2)
  have initial (j : Fin 3) : (embStk view S).R (stoppedChartHeader K 0 (j.castAdd 3)) = [] := by
    have eq : stoppedChartHeader K 0 (j.castAdd 3) = outer (ports ((j.natAdd 3).castAdd 6)) := by
      apply Fin.ext
      change (if j.val < 3 then 66+K+j.val else 33+j.val) =
        (if 3+j.val < 3 then 29+(3+j.val) else if 3+j.val < 6 then 66+K+(3+j.val-3) else 58+(3+j.val-6))
      split_ifs <;> omega
    rw [eq]
    exact clear _ (by change 3 ≤ 3+j.val; omega)
  have restored := restoreReplay (P := Empty) Empty.elim lane (embStk view S) (embStk view B)
    (embDn view z) initial ⟨fun i => (congrFun r _).trans (ready.1 i),fun j => Fin.elim0 j⟩
    (l.trans left) (fun j away => (congrFun r j).trans (stable j away).2)
  obtain ⟨q,G,user,erase,gl,gr⟩ := restored
  obtain ⟨last,F,done,_,final,back,unchanged⟩ := exec_emb (body' := body) (ι := Empty.elim)
    view.injective (fun e => nomatch e) erase z rfl B rfl
  refine ⟨last,F,final.trans user,done,unchanged,?_⟩
  intro j away
  by_cases inside : ∃ i, view i = j
  · obtain ⟨i,rfl⟩ := inside
    rw [← back] at gl gr
    exact ⟨congrFun gl i,congrFun gr i⟩
  · have h := fun i eq => inside ⟨i,eq⟩
    exact ⟨(unchanged j h).1.trans (away h).1,(unchanged j h).2.trans (away h).2⟩

theorem directoryStoppedMove [M8.Machine.Net] {K T Q : ℕ} {P U : Type}
    (saved : Fin 3 ↪ Fin T) (fan : Fin (142080+2) ↪ Fin T) (apart : ∀ i j, saved i ≠ fan j)
    (replay : Fin (66+(K+3+0)) ↪ Fin T)
    (hs : ∀ i j, saved i ≠ replay j) (hf : ∀ i j, fan i ≠ replay j)
    (capacity : columnCapacity ≤ Q)
    (splitCapacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let work := LeafCore.small
    let H := (T+work)+1
    let ext := (Fin.castAddEmb work : Fin T ↪ Fin (T+work))
    let bank := ownerSplitBank (saved.trans ext) (fan.trans ext) (fun i j => ext.injective.ne (apart i j))
    let place := parkedLeafPlace T work
    let view := (replay.trans ext).trans (Fin.succEmb _)
    let outer := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+0) by omega)
    let ports := directoryOuterHeaderBank K
    ∃ leaf : Pr P H Q prime U, ∀ (body : P → Pr P H Q prime U) (entry : P), body entry = leaf →
    ∃ code : Pr P H Q prime U, ∀ (parent : Descriptor) (lo hi w : ℕ), parent.Positive →
      let lane := ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w
      let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
      let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      ∀ (x : Fin (volume prime wide) → ZMod 2) (u : HS H Q prime U) (S : Stacks H prime), 0 < m →
      S.R (ext (saved 0)).succ = List.ofFn (fun i : Fin (m*142080) => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ j, S.L (bank j) = []) → (∀ j, j ≠ Fin.succ 0 → S.R (bank j) = []) →
      (∀ j : Fin 3, (S.R (view (outer (ports (j.castAdd 9))))).length = values j) →
      (∀ j : Fin 12, 3 ≤ j.val → S.R (view (outer (ports j))) = []) →
      (∀ j : Fin 3, S.R (view (stoppedChartHeader K 0 (j.natAdd 3))) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
      (∀ j : Fin work, let t := place (j.natAdd (T+1)); S.L t = [] ∧ S.R t = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ (63*LabelMask.records parent+31+19*m : ℕ)+parkedStoppedRate*((volume prime wide : ℝ)*((max 1 lane.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        z.user = u.user ∧ RecordPayload (ext (saved 0)).succ (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        ∀ j, (∀ k, bank k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro work H ext bank place view outer ports
  let fields := fun j => replay (stoppedChartHeader K 0 j)
  obtain ⟨leaf,install⟩ := parkedStoppedMove (P := P) (U := U) saved fan apart fields
    (fun i j => hs i _) (fun i j => hf i _) capacity splitCapacity
  refine ⟨leaf,?_⟩
  intro body entry installed
  obtain ⟨move,run⟩ := install body entry installed
  let prep : Pr Empty (66+(K+3+0)) Q prime U :=
    embProg outer Empty.elim (IntervalDescriptor.directoryOuterHeaders ports)
  refine ⟨((embProg view Empty.elim prep).seq move).seq (embProg view Empty.elim (Prog.seqList ((outerSlots K).map WordCmd.dropR))),?_⟩
  intro parent lo hi w positive lane row values m wide size x u S live source left empty lengths clear inner free
  obtain ⟨y,E,a,user,bill,placed,ready,off,retire⟩ := prepareReplay body view parent lo hi w positive u S lengths clear inner
  have disjoint (i j) : bank i ≠ view j :=
    splitAvoids (saved.trans ext) (fan.trans ext) (fun a b => ext.injective.ne (apart a b))
      (ext (replay j)) (fun a => ext.injective.ne (hs a j)) (fun a => ext.injective.ne (hf a j)) i
  obtain ⟨z,F,b,moveRun,cost,final,payload,frame⟩ := run lane x y E live
    (((off _ (fun j => (Fin.succ_injective _).ne (ext.injective.ne (hs 0 j).symm))).2).trans source)
    (fun i => ((off _ (fun j => (disjoint i j).symm)).1).trans (left i))
    (fun i ne => ((off _ (fun j => (disjoint i j).symm)).2).trans (empty i ne))
    ready.1 (by
      intro j
      have h := off (place (j.natAdd (T+1))) (fun i eq => by
        have val := congrArg Fin.val eq
        change (replay i).val+1 = T+1+j.val at val
        have := (replay i).isLt
        omega)
      exact ⟨h.1.trans (free j).1,h.2.trans (free j).2⟩)
  obtain ⟨last,G,same,erase,unchanged,restored⟩ := retire z F (fun i => frame _ (fun k => disjoint k i))
  have eraseBill := (directoryHeaderCosts parent (hi-lo) (64-(hi-lo)) w live).2
  refine ⟨last,G,_,(placed.seq moveRun).seq erase,?_,same.trans (final.trans user),?_,?_⟩
  · push_cast
    push_cast at cost
    have aBound := (Nat.cast_le (α := ℝ)).mpr bill
    have eBound := (Nat.cast_le (α := ℝ)).mpr eraseBill
    push_cast at aBound eBound
    linarith only [cost,aBound,eBound]
  · have outside : ∀ i, view i ≠ (ext (saved 0)).succ := fun i =>
      (Fin.succ_injective _).ne (ext.injective.ne (hs 0 i).symm)
    intro t
    change readAt blank (G.L _) (G.R _) _ = _
    rw [(unchanged _ outside).1,(unchanged _ outside).2]
    exact payload t
  · intro j away
    exact restored j (fun h => ⟨(frame j away).1.trans (off j h).1,(frame j away).2.trans (off j h).2⟩)

end IntegerMultBounds.MathlibTM2.M6.BitNode
