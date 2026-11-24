module

public import IntegerMultBounds.MathlibTM2.M6.BitLiveMoveArchive
public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhaseCall

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)

/-- Registers beyond the routing bank are available to the selected MOVE. -/
noncomputable def phaseMoveSuffix (T : ℕ) : List (Fin T) :=
  (List.finRange T).filter fun j => rowSwapBlock.tapes+35 ≤ j.val

private theorem suffixClean {T : ℕ} (fits : rowSwapBlock.tapes+35 ≤ T) (S : Stacks T prime) :
    let route := Fin.castLEEmb fits
    withBlankRegisters (phaseMoveSuffix T) S (∀ k, 35 ≤ k.val → S.L (route k) = [] ∧ S.R (route k) = []) ↔
      ∀ j, 35 ≤ j.val → S.L j = [] ∧ S.R j = [] := by
  intro route
  rw [withBlankRegisters_iff]
  constructor
  · rintro ⟨bank,extra⟩ j hj
    by_cases h : j.val < rowSwapBlock.tapes+35
    · exact bank ⟨j.val,h⟩ hj
    · exact extra j (by simp [phaseMoveSuffix,Nat.le_of_not_gt h])
  · intro free
    refine ⟨fun k hk => free _ hk,?_⟩
    intro j hj
    have h : rowSwapBlock.tapes+35 ≤ j.val := by simpa [phaseMoveSuffix] using hj
    exact free j (by omega)

/-- Install each selected MOVE as a callable procedure on the phase routing
bank. Its scratch suffix is blank at entry and is restored on return. -/
theorem selectedScheduledBandMoves {U : Type} (stage : Fin 9) (run : StageRun) (afterCopy : Bool) :
    let _ := BinaryRadixEqualShared.supplierNet
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ (T : ℕ) (fits : rowSwapBlock.tapes+35 ≤ T) (P : J → Type)
        (tables : ∀ j, Option (P j) → Pr (Option (P j)) T Q prime U) (rate : ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (j : J),
        let i := phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)
        let child := scheduledChild prime p.node i
        let V := (prime^(p.w+1))^16*p.stageWidth
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) → 49*(p.w+1) ≤ 64*p.cutoff →
        ∃ position : Fin (volume prime child) ≃ Fin V,
          (∀ h, (position h).val = (CopyChildLayout.packActive child h).val) ∧
          ScheduledChildExec p.node child p.w p.stageWidth (Fin.castLEEmb fits)
            (binSyms p.root.width.size p.cutoff) position (tables j) none
            (cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child+rate*p.cells)
            true (phaseMoveSuffix T) := by
  intro inst J
  classical
  obtain ⟨states,compile⟩ := selectedLiveBandMoves (U := U) stage run afterCopy
  refine ⟨states,?_⟩
  intro Q enough
  obtain ⟨minimum,leaf,build⟩ := compile enough
  refine ⟨minimum,leaf,?_⟩
  intro D large
  obtain ⟨N,place⟩ := build D large
  let T := max (rowSwapBlock.tapes+35) (N+35)+1
  have fits : rowSwapBlock.tapes+35 ≤ T := (le_max_left ..).trans (Nat.le_succ _)
  let ports := Fin.castLEEmb (show N+35 ≤ T from (le_max_right ..).trans (Nat.le_succ _))
  let tmp : Fin T := Fin.last _
  have apart (i : Fin (N+35)) : ports i ≠ tmp := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = max _ _ at h
    omega
  obtain ⟨P,body,code,rate,worker⟩ := place (fun _ => ports) tmp (fun _ => apart)
  let table (j : J) (f : Option (P j)) : Pr (Option (P j)) T Q prime U :=
    stateMapProg id id some (f.elim (code j) (body j))
  refine ⟨T,fits,P,table,rate,?_⟩
  intro p blocks j i child V root rows label band
  obtain ⟨position,packed,call⟩ := worker p blocks j root rows label band
  refine ⟨position,packed,?_⟩
  intro smaller u S word ready free
  have blanks := (suffixClean fits S).1 free
  have temp : 35 ≤ tmp.val := by change 35 ≤ max _ (N+35); omega
  obtain ⟨z,F,t,y,exec,paid,user,out,clear,frame,action⟩ :=
    call u S word ready (fun k hk => blanks (ports k) hk) (blanks tmp temp).2
  have final (k : Fin T) (hk : 35 ≤ k.val) : F.L k = [] ∧ F.R k = [] := by
    by_cases h : k.val < N+35
    · exact clear ⟨k.val,h⟩ hk
    · have off := frame k (fun l eq => by
        have same : l.val = k.val := congrArg Fin.val eq
        exact h (same ▸ l.isLt))
      simpa only [off.1,off.2] using blanks k hk
  have lifted := stateMap_exec id id (fun _ => rfl) some (body' := table j) (fun _ => rfl) exec
  refine ⟨z,F,t,y,lifted,paid,user,out,(suffixClean fits F).2 final,?_,action⟩
  intro k outside
  have h : rowSwapBlock.tapes+35 ≤ k.val := by
    by_contra! inside
    exact outside ⟨k.val,inside⟩ rfl
  have hk : 35 ≤ k.val := by omega
  exact ⟨(final k hk).1.trans (blanks k hk).1.symm,(final k hk).2.trans (blanks k hk).2.symm⟩


noncomputable def selectedMoveEdge (afterCopy : Bool) (j : Fin (selectedPhaseSchedule afterCopy).1.length) : ℕ × ℕ :=
  (Geometry.Moves.phaseEdges.filter positiveMove)[(selectedPhaseIndex afterCopy j).val]'(selectedPhaseIndex afterCopy j).isLt

def RoutedPhaseMove [M8.Machine.Net] {U P : Type} {T Q : ℕ}
    (stage : Fin 9) (run : StageRun) (afterCopy : Bool)
    (j : Fin (selectedPhaseSchedule afterCopy).1.length) (fits : rowSwapBlock.tapes+35 ≤ T)
    (body : P → Pr P T Q prime U) (entry : P) (D leafRate : ℝ) (rate base swaps : ℕ)
    (p : CutoffNodeInput) (blocks : ℕ) : Prop :=
  let i := phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)
  let child := scheduledChild prime p.node i
  let V := (prime^(p.w+1))^16*p.stageWidth
  let a := Geometry.Dimensions.value (selectedMoveEdge afterCopy j).1
  let b := Geometry.Dimensions.value (selectedMoveEdge afterCopy j).2
  let lane := phaseIntervalChild (min a b) (max a b) (p.w+1) p.stageWidth 8
  p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
  p.root.beforeH = blocks*prime^(64*p.root.width) → 49*(p.w+1) ≤ 64*p.cutoff →
  ∀ (position : Fin (volume prime child) ≃ Fin V) (size : volume prime lane = V),
    InheritedIntervalPositions child lane size position →
    ScheduledChildExec p.node child p.w p.stageWidth (Fin.castLEEmb fits)
      (binSyms p.root.width.size p.cutoff) position body entry
      (cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child+rate*p.cells+
        4+(base+swaps*swapVolumeRate p.w)*V) true (phaseMoveSuffix T)

/-- Each selected MOVE returns its transposition at the caller's inherited
addresses, with both field permutations included in its recursive bill. -/
theorem selectedRoutedBandMoves {U : Type} (stage : Fin 9) (run : StageRun) (afterCopy : Bool) :
    let _ := BinaryRadixEqualShared.supplierNet
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ (T : ℕ) (fits : rowSwapBlock.tapes+35 ≤ T) (P : J → Type)
        (tables : ∀ j, Option (P j) → Pr (Option (P j)) T Q prime U) (rate : ℕ) (base swaps : J → ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (j : J),
        RoutedPhaseMove stage run afterCopy j fits (tables j) none D leafRate rate (base j) (swaps j) p blocks := by
  intro inst J
  classical
  let edge := selectedMoveEdge afterCopy
  obtain ⟨states,compile⟩ := selectedScheduledBandMoves (U := U) stage run afterCopy
  refine ⟨max states rowSwapBlock.states,?_⟩
  intro Q enough
  have capacity := (le_max_right states rowSwapBlock.states).trans enough
  obtain ⟨minimum,leaf,build⟩ := compile ((le_max_left ..).trans enough)
  refine ⟨minimum,leaf,?_⟩
  intro D large
  obtain ⟨T,fits,P,body,rate,worker⟩ := build D large
  let ports := Fin.castLEEmb fits
  let order (j : J) := phasePackSchedule
    (min (Geometry.Dimensions.value (edge j).1) (Geometry.Dimensions.value (edge j).2))
    (max (Geometry.Dimensions.value (edge j).1) (Geometry.Dimensions.value (edge j).2))
  let pack (j : J) (js : List ℕ) : Pr (Option (Option (P j))) T Q prime U :=
    statePlacedNormalized ports capacity swapStates_pos Empty.elim (packSchedule 16 js)
  let table (j : J) : Option (Option (P j)) → Pr (Option (Option (P j))) T Q prime U
    | some f => stateMapProg id id some (body j f)
    | none => (pack j (order j)).seq ((Prog.call (some none)).seq (pack j (order j).reverse))
  have apart (k) (hk : k ∈ phaseMoveSuffix T) (i) : ports i ≠ k := by
    have h : rowSwapBlock.tapes+35 ≤ k.val := by simpa [phaseMoveSuffix] using hk
    intro eq
    exact (Nat.not_lt_of_ge h) (show k.val < _ from eq ▸ i.isLt)
  have member (j : J) := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) (selectedPhaseIndex afterCopy j).isLt)
  choose base swaps adapt using fun j : J => packedPhaseChild capacity ports (table j) none (some none)
    (edge j) (Geometry.Moves.phase_checked _ (member j).1) (Nat.pos_of_ne_zero (bne_iff_ne.mp (member j).2))
    (phaseMoveSuffix T) apart rfl
  refine ⟨T,fits,fun j => Option (P j),table,rate,base,swaps,?_⟩
  intro p blocks j
  unfold RoutedPhaseMove
  intro i child V a b lane root rows label band position size coords
  obtain ⟨packed,addr,call⟩ := worker p blocks j root rows label band
  obtain ⟨canonical,offset,route⟩ := adapt j p i (phaseChildPositions.choose_spec stage run (selectedPhaseIndex afterCopy j)).1
  have same : packed = canonical := Equiv.ext (fun k => Fin.ext ((addr k).trans (offset k).symm))
  subst canonical
  apply route position coords
  intro smaller u S x ready free
  obtain ⟨z,F,t,y,exec,paid,user,out,clean,frame,act⟩ := call smaller u S x ready free
  exact ⟨z,F,t,y,stateMap_exec id id (fun _ => rfl) some (body' := table j) (fun _ => rfl) exec,
    paid,user,out,clean,frame,act⟩


/-- A call from a scalar phase realizes the physical interval transposition
on its record. The schedule determines both the child and its address map. -/
theorem RoutedPhaseMove.call {U P : Type} {T Q : ℕ}
    {stage : Fin 9} {run : StageRun} {afterCopy : Bool}
    {j : Fin (selectedPhaseSchedule afterCopy).1.length} {fits : rowSwapBlock.tapes+35 ≤ T}
    {body : P → Pr P T Q prime U} {entry : P} {D leafRate : ℝ} {rate base swaps : ℕ}
    {p : CutoffNodeInput} {blocks : ℕ}
    (move : RoutedPhaseMove stage run afterCopy j fits body entry D leafRate rate base swaps p blocks)
    (root : p.root.Positive) (rows : 142080^(p.depth+1) ∣ p.root.rows)
    (label : p.root.beforeH = blocks*prime^(64*p.root.width)) (band : 49*(p.w+1) ≤ 64*p.cutoff) :
    let edge := selectedMoveEdge afterCopy j
    let a := Geometry.Dimensions.value edge.1
    let b := Geometry.Dimensions.value edge.2
    let lane := phaseIntervalChild (min a b) (max a b) (p.w+1) p.stageWidth
    let V := (prime^(p.w+1))^16*p.stageWidth
    let bank := scheduledRecordPorts (Fin.castLEEmb fits)
    let stored := RecordReady (b := prime) (w := p.w) (W := p.stageWidth) (d := 16) bank
      (prime^(p.w+1)).size p.stageWidth.size (binSyms p.root.width.size p.cutoff) SparseRoleCircuit.encode
      (fun _ => blank) (fun _ => blank) 0 0
    let child := scheduledChild prime p.node (phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j))
    let price := cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child
    ∃ size : volume prime lane = V, ∀ (word : Fin V → ZMod 2) u S, stored word S →
      (∀ k, 35 ≤ k.val → S.L k = [] ∧ S.R k = []) →
      let after := fun k : Fin V => Shared50RecursiveNodeRows.transpose (v := lane)
        (one_dvd _) (fun h => word (h.cast size)) (k.cast size.symm)
      ∃ z F t, Exec body ((Prog.call entry).seq (compactOwner (bank 24) (bank 0) (bank 1))) (mk u S) t (mk z F) ∧
        CleanupBound S F t (price+rate*p.cells+6+(base+swaps*swapVolumeRate p.w)*V+
          cleanupWeight (S.L (bank 24)) (S.R (bank 24))+14*V+19) ∧
        z.user = u.user ∧ stored after F ∧ F.L (bank 24) = [] ∧
        F.R (bank 24) = List.ofFn (fun i => SparseRoleCircuit.encode (after i)) ∧
        ∀ k, 35 ≤ k.val → F.L k = [] ∧ F.R k = [] := by
  intro edge a b lane V bank stored child price
  let i := phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)
  have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) (selectedPhaseIndex afterCopy j).isLt)
  have checked := Geometry.Moves.phase_checked edge mem.1
  have pos : 0 < Geometry.moveRank edge.1 edge.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  have rank := (phaseChildPositions.choose_spec stage run (selectedPhaseIndex afterCopy j)).1
  have smaller : child.width < p.node.width := by
    have h := Nat.mul_lt_mul_of_pos_right ((nodeChildren5_le i).trans_lt (by decide : 42 < 64)) (Nat.succ_pos p.w)
    simpa only [child,i,scheduledChild,rankDescriptor,p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)] using h
  have align : p.B*prime^(64*((p.w+1)*64))*((prime^(p.w+1))^112*
      (p.node.beforeRows*p.rowsPerStage*p.node.between*p.node.afterD)) = p.stageWidth := by
    unfold CutoffNodeInput.stageWidth CutoffNodeInput.stageFactor
    ring
  have coords := scheduledPhaseCoordinates p.node i edge checked (p.w+1) p.B p.rowsPerStage rank p.width p.rows p.label
  dsimp only at coords
  rw [align] at coords
  obtain ⟨e,address,_⟩ := coords
  have size : volume prime lane = V := phaseIntervalChild_volume (phaseInterval_bounds checked pos).1.le
    (phaseInterval_bounds checked pos).2 _ _
  let position := e.symm.trans (finCongr size)
  have inherited : InheritedIntervalPositions child lane size position := by
    intro k
    simpa [position] using address (e.symm k)
  have width : lane.width = child.width := by
    change lane.width = nodeChildren5[i.val]*(p.node.width/64)
    rw [rank,p.width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    exact phaseIntervalChild_width checked (p.w+1) p.stageWidth
  refine ⟨size,?_⟩
  intro word u S ready free after
  obtain ⟨z,F,t,y,exec,paid,user,out,fresh,_,action⟩ :=
    move root rows label band position size inherited smaller u S word ready ((suffixClean fits S).2 free)
  have eq : y = after := (inherited.transpose_iff width word y).1 action
  subst y
  have wordAt : WordAtZero after (F.L (bank 24)) (F.R (bank 24)) := by
    intro k
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using out.src k
  obtain ⟨v,same,finish⟩ := compactOwner_exec body (bank 24) (bank 0) (bank 1)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) after z F wordAt
    (out.scratch 0 (by decide)).1 (out.scratch 0 (by decide)).2 (out.scratch 1 (by decide)).2
  let xs := List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (after i)
  let G := {F with L := Function.update F.L (bank 24) [], R := Function.update F.R (bank 24) xs}
  have kept k (ne : k ≠ bank 24) : G.L k = F.L k ∧ G.R k = F.R k := by simp [G,ne]
  have zl : G.L (bank 24) = [] := by simp [G]
  have zr : G.R (bank 24) = xs := by simp [G]
  have bill : CleanupBound S F (t+2) (price+rate*p.cells+6+(base+swaps*swapVolumeRate p.w)*V) := by
    intro js nd
    have h := paid js nd
    change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
      (price+rate*p.cells+4+(base+swaps*swapVolumeRate p.w)*V) at h
    change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
    omega
  refine ⟨v,G,_,(Exec.call exec).seq finish,?_,same.trans user,?_,zl,zr,?_⟩
  · simpa only [xs,List.length_ofFn] using compactCharge (bank 24) S F xs bill
  · apply out.returnPayload (outBank := bank) (fun i hi => kept _ (bank.injective.ne hi))
    intro k
    rw [zl,zr,sub_zero]
    rw [← List.map_ofFn,encodedOwnerCell,readAt_nil_left,putWord_blank_zero]
  · intro k hk
    have ne : k ≠ bank 24 := fun eq => by
      have h := congrArg Fin.val eq
      change k.val = 24 at h
      omega
    obtain ⟨l,r⟩ := (suffixClean fits F).1 fresh k hk
    exact ⟨(kept k ne).1.trans l,(kept k ne).2.trans r⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
