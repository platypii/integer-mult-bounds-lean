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


/-- Share only the routed payload with the selected owner. The returned bank
represents the updated family, including its two volume counters. -/
theorem RoutedPhaseMove.ownerCall {U P : Type} {T H Q k : ℕ}
    {stage : Fin 9} {run : StageRun} {afterCopy : Bool}
    {j : Fin (selectedPhaseSchedule afterCopy).1.length} {fits : rowSwapBlock.tapes+35 ≤ T}
    {body : P → Pr P T Q prime U} {entry : P} {D leafRate : ℝ} {rate base swaps : ℕ}
    {p : CutoffNodeInput} {blocks : ℕ}
    (move : RoutedPhaseMove stage run afterCopy j fits body entry D leafRate rate base swaps p blocks)
    (root : p.root.Positive) (rows : 142080^(p.depth+1) ∣ p.root.rows)
    (label : p.root.beforeH = blocks*prime^(64*p.root.width)) (band : 49*(p.w+1) ≤ 64*p.cutoff)
    (owner : Fin k) (place : Fin T ↪ Fin H) (fan : Fin (k+2) ↪ Fin H)
    (shared : place (scheduledRecordPorts (Fin.castLEEmb fits) 24) = fan (owner.castAdd 2))
    (apart : ∀ i, i ≠ owner.castAdd 2 → ∀ l, place l ≠ fan i) :
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
    let code := (Prog.call entry).seq (compactOwner (bank 24) (bank 0) (bank 1))
    ∃ size : volume prime lane = V, ∀ (data : Fin k → Fin V → ZMod 2) u S,
      HelperFan fan data S → (∃ old, stored old (embStk place S)) →
      (∀ i, 35 ≤ i.val → S.L (place i) = [] ∧ S.R (place i) = []) →
      let after := fun i : Fin V => Shared50RecursiveNodeRows.transpose (v := lane)
        (one_dvd _) (fun h => data owner (h.cast size)) (i.cast size.symm)
      ∃ z F t, Exec (embTab place body) (embProg place id code) (mk u S) t (mk z F) ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          (price+rate*p.cells+6+(base+swaps*swapVolumeRate p.w)*V+16*V+23+
            tapeCharge cleanupWeight (frameSlots fan) S) ∧
        z.user = u.user ∧ HelperFan fan (Function.update data owner after) F ∧
        stored after (embStk place F) ∧ (∀ i, 35 ≤ i.val → F.L (place i) = [] ∧ F.R (place i) = []) ∧
        ∀ i, (∀ l, place l ≠ i) → F.L i = S.L i ∧ F.R i = S.R i := by
  intro edge a b lane V bank stored child price code
  obtain ⟨size,call⟩ := move.call root rows label band
  refine ⟨size,?_⟩
  intro data u S live previous free after
  obtain ⟨old,prepared⟩ := previous
  change place (bank 24) = _ at shared
  have ready : stored (data owner) (embStk place S) := by
    apply prepared.returnPayload (outBank := bank) (fun _ _ => ⟨rfl,rfl⟩)
    intro h
    have cell := fanPayload live owner h
    change _ = readAt blank (S.L (place (bank 24))) (S.R (place (bank 24))) _
    rw [shared]
    simpa only [List.map_ofFn] using cell.symm
  obtain ⟨v,B,t,exec,bill,user,out,zl,zr,fresh⟩ := call (data owner) (embDn place u) (embStk place S) ready free
  have payload : RecordPayload (bank 24) (fun _ => blank) 0 after B := fun h => by simpa only [List.map_ofFn] using out.src h
  obtain ⟨z,F,run,same,result,view,frame⟩ := placeIdleOwner_exec place (bank 24) fan owner shared apart
    body (embTab place body) id (fun _ => rfl) code u S data live v B t after exec payload
  rw [← view] at bill out fresh zl zr
  have paid := CleanupBound.place place frame bill
  refine ⟨z,F,t,run,?_,same.trans user,result,out,fresh,frame⟩
  let target := fan (owner.castAdd 2)
  have left : F.L target = [] := by
    change F.L (fan (owner.castAdd 2)) = []
    rw [← shared]
    exact zl
  have right : (F.R target).length = V := by
    change (F.R (fan (owner.castAdd 2))).length = V
    rw [← shared]
    change ((embStk place F).R (bank 24)).length = V
    rw [zr,List.length_ofFn]
  let weight := cleanupWeight (S.L target) (S.R target)
  have balance (js : List (Fin H)) (nd : js.Nodup) (inside : ∀ l ∈ js, ∃ i, fan i = l) :
      tapeCharge cleanupWeight js F+(if target ∈ js then weight else 0) =
      tapeCharge cleanupWeight js S+(if target ∈ js then 2*V+4 else 0) := by
    induction js with
    | nil => simp [tapeCharge]
    | cons l js ih =>
      have tail := ih nd.of_cons (fun a ha => inside a (List.mem_cons_of_mem _ ha))
      by_cases eq : l = target
      · subst l
        simp [tapeCharge,cleanupWeight,nd.notMem,left,right,weight] at tail ⊢
        omega
      · obtain ⟨i,rfl⟩ := inside l List.mem_cons_self
        have ne : i ≠ owner.castAdd 2 := fun h => eq (congrArg fan h)
        obtain ⟨l,r⟩ := frame _ (apart i ne)
        simp [tapeCharge,l,r,Ne.symm eq] at tail ⊢
        omega
  have total := balance (frameSlots fan) (frameSlots_nodup fan) (fun l => (mem_frameSlots fan l).mp)
  have member : target ∈ frameSlots fan := (mem_frameSlots fan _).mpr ⟨_,rfl⟩
  simp only [member,ite_true] at total
  intro js nd
  have h := paid js nd
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
    (price+rate*p.cells+6+(base+swaps*swapVolumeRate p.w)*V+
      cleanupWeight (S.L (place (bank 24))) (S.R (place (bank 24)))+14*V+19) at h
  rw [shared] at h
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  dsimp only [weight,target] at total
  omega


/-- Place both clean basis programs and the routed worker on one owner.
The disjointness facts follow the execution order so that later programs
retain their prepared private tapes. -/
theorem phaseMoveBanks {T k : ℕ} (src : Fin T) (owner : Fin k)
    (A B : List (FlatCoordinateSchedule.Op 16)) :
    ∃ (H : ℕ) (place : Fin T ↪ Fin H) (fan : Fin (k+2) ↪ Fin H)
      (a : Fin (FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin H)
      (b : Fin (FlatCoordinateCleanSchedule.tapeCount B) ↪ Fin H),
      place src = fan (owner.castAdd 2) ∧ a (segmentSource A) = fan (owner.castAdd 2) ∧
      b (segmentSource B) = fan (owner.castAdd 2) ∧
      (∀ i, i ≠ owner.castAdd 2 → (∀ l, place l ≠ fan i) ∧ (∀ l, a l ≠ fan i) ∧ (∀ l, b l ≠ fan i)) ∧
      (∀ i, i ≠ src → ∀ l, a l ≠ place i) ∧
      ∀ i, i ≠ segmentSource B → (∀ l, a l ≠ b i) ∧ (∀ l, place l ≠ b i) := by
  let m := FlatCoordinateCleanSchedule.tapeCount A
  let n := FlatCoordinateCleanSchedule.tapeCount B
  have hm : 0 < m := (segmentSource A).isLt
  have hn : 0 < n := (segmentSource B).isLt
  obtain ⟨place,fan,a,b,shared,enter,leave,off,later,owners,controls⟩ :=
    copyWorkspacePlacement src owner (m-1) (n-1)
  let am := Fin.castLEEmb (show m ≤ 1+(m-1) by omega)
  let bn := Fin.castLEEmb (show n ≤ 1+(n-1) by omega)
  refine ⟨_,place,fan,am.trans a,bn.trans b,shared.symm,enter.trans shared.symm,leave.trans shared.symm,?_,?_,?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i =>
      intro ne
      obtain ⟨ha,hp,hb⟩ := owners i (fun eq => ne (congrArg (Fin.castAdd 2) eq))
      exact ⟨hp,fun l => ha (am l),fun l => hb (bn l)⟩
    | right i =>
      intro _
      obtain ⟨ha,hp,hb⟩ := controls i
      exact ⟨hp,fun l => ha (am l),fun l => hb (bn l)⟩
  · exact fun i ne l => off i (place.injective.ne ne) (am l)
  · intro i ne
    have pos : 0 < i.val := Nat.pos_of_ne_zero (fun eq => ne (Fin.ext eq))
    let r : Fin (n-1) := ⟨i.val-1,by have h : i.val < n := i.isLt; omega⟩
    have eq : bn i = r.natAdd 1 := Fin.ext (by change i.val = 1+(i.val-1); omega)
    obtain ⟨ha,hp⟩ := later r
    change (∀ l, a (am l) ≠ b (bn i)) ∧ (∀ l, place l ≠ b (bn i))
    rw [eq]
    exact ⟨fun l => ha (am l),hp⟩

noncomputable def phaseBasisTapes {w W : ℕ} (stages : List (FlatCoordinateSchedule.Op 16))
    (word : Fin ((prime^w)^16*W) → ZMod 2) :=
  SharedBankStageInput.raw (FlatCoordinateShiftSharedBank.common (d := 16) (b := w) (W := W)
    (fun i => SparseRoleCircuit.encode (word i))) (FlatCoordinateCleanSchedule.tapeCount stages)

/-- Away from its source, a basis pass has the same initial tapes for every
owner word. Thus both workspaces can be prepared before the MOVE. -/
theorem phaseBasisTapes_off {w W : ℕ} (stages : List (FlatCoordinateSchedule.Op 16))
    (x y : Fin ((prime^w)^16*W) → ZMod 2) (i : Fin (FlatCoordinateCleanSchedule.tapeCount stages))
    (other : i ≠ segmentSource stages) :
    (phaseBasisTapes stages x).head i = (phaseBasisTapes stages y).head i ∧
      (phaseBasisTapes stages x).tape i = (phaseBasisTapes stages y).tape i := by
  have same := basisWorkspace_eq stages x y
  refine ⟨rfl,?_⟩
  simpa only [basisWorkspace,SharedPlacementAlphabet.setTape,Function.update_of_ne other,phaseBasisTapes]
    using congrArg (fun (bank : Tapes _ prime) => bank.tape i) same

/-- Execute a certified basis pass on one represented owner. Only the
private registers need an entry representation distinct from the owner bank. -/
theorem phaseBasisOwnerPass {P U : Type} {T Q k w W : ℕ} (stages : List (FlatCoordinateSchedule.Op 16))
    (ports : Fin (FlatCoordinateCleanSchedule.tapeCount stages) ↪ Fin T)
    (fan : Fin (k+2) ↪ Fin T) (owner : Fin k)
    (shared : ports (segmentSource stages) = fan (owner.castAdd 2))
    (apart : ∀ i, i ≠ owner.castAdd 2 → ∀ l, ports l ≠ fan i)
    (body : P → Pr P T Q prime U) (capacity : _ ≤ Q)
    (data : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (y : Fin ((prime^w)^16*W) → ZMod 2)
    (pass : HoareTime (FlatCoordinateCleanSchedule.program stages) (fun z => z = phaseBasisTapes stages (data owner))
      (fun z => z = phaseBasisTapes stages y) (FlatCoordinateCleanSchedule.constant stages*((prime^w)^16*W))) :
    let code := embProg ports (Empty.elim : Empty → P) (foreign (U := U) (liftQ (FlatCoordinateCleanSchedule.program stages) capacity))
    let rate := 26*(FlatCoordinateCleanSchedule.constant stages*(FlatCoordinateCleanSchedule.tapeCount stages+5))
    ∀ u S, HelperFan fan data S →
      (∀ i, i ≠ segmentSource stages → ∀ h, (phaseBasisTapes stages (fun _ => 0 : Fin ((prime^w)^16*W) → ZMod 2)).tape i h =
        readAt blank (S.L (ports i)) (S.R (ports i)) (h-(phaseBasisTapes stages (fun _ => 0 : Fin ((prime^w)^16*W) → ZMod 2)).head i)) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          (rate*((prime^w)^16*W)+156+tapeCharge cleanupWeight (frameSlots fan) S) ∧
        HelperFan fan (Function.update data owner y) F ∧
        RepT (phaseBasisTapes stages y) (embStk ports F).L (embStk ports F).R ∧
        ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro code rate u S live work
  have source (x : Fin ((prime^w)^16*W) → ZMod 2) (h : ℤ) :
      (phaseBasisTapes stages x).tape (segmentSource stages) h =
        RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
          ((List.ofFn x).map SparseRoleCircuit.encode) h) := by
    rw [List.map_ofFn]
    rfl
  have input : RepT (phaseBasisTapes stages (data owner)) (embStk ports S).L (embStk ports S).R := by
    intro i h
    by_cases eq : i = segmentSource stages
    · subst i
      rw [source]
      change _ = readAt blank (S.L (ports _)) (S.R (ports _)) (h-0)
      rw [shared]
      exact (fanPayload live owner h).symm
    · obtain ⟨head,tape⟩ := phaseBasisTapes_off stages (data owner) (fun _ => 0) i eq
      rw [head,tape]
      exact work i eq h
  obtain ⟨z,F,t,exec,time,user,out,frame⟩ := placedHoare_exec _ ports capacity body pass u S input
  have payload : RecordPayload (fan (owner.castAdd 2)) (fun _ => blank) 0 y F := by
    intro h
    rw [← shared,← source]
    exact (out (segmentSource stages) h).symm
  refine ⟨z,F,t,exec,user,?_,fanUpdate owner y live payload (fun i ne => frame _ (apart i ne)),out,frame⟩
  intro js nd
  have paid := foreignCleanupBound exec
  have h := paid js nd
  have stock := paid (frameSlots fan) (frameSlots_nodup fan)
  have scaled : 26*t ≤ rate*((prime^w)^16*W)+156 := by
    apply (Nat.mul_le_mul_left 26 time).trans
    dsimp only [rate]
    exact le_of_eq (by ring)
  change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+13*t at h
  change t+tapeCharge cleanupWeight (frameSlots fan) F ≤ tapeCharge cleanupWeight (frameSlots fan) S+13*t at stock
  change _+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  omega

open M8.Machine.Segments in
/-- The certified basis programs turn the interval transpose returned by
the owner call into the selected scalar MOVE, with linear cost on each side. -/
theorem selectedOwnerBasis (afterCopy : Bool) (j : Fin (selectedPhaseSchedule afterCopy).1.length) :
    let edge := selectedMoveEdge afterCopy j
    let a := Geometry.Dimensions.value edge.1
    let b := Geometry.Dimensions.value edge.2
    ∃ (C : Matrix (Fin 8) (Fin 8) ℚ) (rev : CopyBasisPass C.adjugate) (fwd : CopyBasisPass C),
    let A := description _ rev.good
    let B := description _ fwd.good
    ∀ (p : CutoffNodeInput) (k : ℕ) (owners : Fin 661 ↪ Fin k),
    let w := p.w+1
    let W := p.stageWidth
    let V := (prime^w)^16*W
    let lane := phaseIntervalChild (min a b) (max a b) w W
    let bank := fun stages (word : Fin V → ZMod 2) => phaseBasisTapes stages word
    let i := selectedPhaseIndex afterCopy j
    let owner := owners (paidRegister i.val)
    ∀ (data : Fin k → Fin V → ZMod 2) (size : volume prime lane = V),
      ∃ loaded y : Fin V → ZMod 2,
        HoareTime (FlatCoordinateCleanSchedule.program A) (fun z => z = bank A (data owner))
          (fun z => z = bank A loaded) (FlatCoordinateCleanSchedule.constant A*V) ∧
        let moved := fun h : Fin V => Shared50RecursiveNodeRows.transpose (v := lane) (one_dvd _)
          (fun l => loaded (l.cast size)) (h.cast size.symm)
        HoareTime (FlatCoordinateCleanSchedule.program B) (fun z => z = bank B moved)
          (fun z => z = bank B y) (FlatCoordinateCleanSchedule.constant B*V) ∧
        Function.update data owner y = moveOwnerEffect owners data i.val edge := by
  intro edge a b
  have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove)
    (selectedPhaseIndex afterCopy j).isLt)
  have checked := Geometry.Moves.phase_checked edge mem.1
  have pos : 0 < Geometry.moveRank edge.1 edge.2 := Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  obtain ⟨C,shape,rev,fwd⟩ := modular_move_profile.choose_spec.1 edge checked
  refine ⟨C,rev,fwd,?_⟩
  intro A B p k owners w W V lane bank i owner data size
  have cells : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    (Nat.mul_pos p.idlePositive (by decide))
  have positive : 0 < W := Nat.pos_of_mul_pos_left (p.stageCells ▸ cells)
  obtain ⟨loaded,y,first,last,read⟩ := phaseBasis_runs (w := w) (phaseInterval_bounds checked pos).1.le
    (phaseInterval_bounds checked pos).2 positive C rev fwd (data owner)
  refine ⟨loaded,y,first,last,moveOwnerEffect_of_exec owners data i.val edge checked y ?_⟩
  intro s h
  simp only [copyAddress_index,selectedWord,selectedRaw,shape]
  exact read s h

/-- The basis programs and the routed worker execute consecutively on the
same host. The middle call pays the recursive price once. -/
theorem basisRoutedMove {T k : ℕ} (stage : Fin 9) (run : StageRun) (afterCopy : Bool)
    (j : Fin (selectedPhaseSchedule afterCopy).1.length) (fits : rowSwapBlock.tapes+35 ≤ T)
    (owners : Fin 661 ↪ Fin k) :
    let bank := scheduledRecordPorts (Fin.castLEEmb fits)
    ∃ (A B : List (FlatCoordinateSchedule.Op 16)) (H : ℕ) (place : Fin T ↪ Fin H)
      (fan : Fin (k+2) ↪ Fin H) (a : Fin (FlatCoordinateCleanSchedule.tapeCount A) ↪ Fin H)
      (b : Fin (FlatCoordinateCleanSchedule.tapeCount B) ↪ Fin H) (localRate : ℕ),
    ∀ {P U : Type} {Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
      (capA : _ ≤ Q) (capB : _ ≤ Q),
    let host := embTab place body
    let enter := embProg a (Empty.elim : Empty → P) (foreign (U := U) (liftQ (FlatCoordinateCleanSchedule.program A) capA))
    let leave := embProg b (Empty.elim : Empty → P) (foreign (U := U) (liftQ (FlatCoordinateCleanSchedule.program B) capB))
    let mid := embProg place id ((Prog.call entry).seq (compactOwner (bank 24) (bank 0) (bank 1)))
    ∀ (p : CutoffNodeInput) blocks D leafRate rate base swaps,
    RoutedPhaseMove stage run afterCopy j fits body entry D leafRate rate base swaps p blocks →
    p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
    p.root.beforeH = blocks*prime^(64*p.root.width) → 49*(p.w+1) ≤ 64*p.cutoff →
    let V := (prime^(p.w+1))^16*p.stageWidth
    let stored := RecordReady (b := prime) (w := p.w) (W := p.stageWidth) (d := 16) bank
      (prime^(p.w+1)).size p.stageWidth.size (binSyms p.root.width.size p.cutoff) SparseRoleCircuit.encode
      (fun _ => blank) (fun _ => blank) 0 0
    let child := scheduledChild prime p.node (phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j))
    let price := cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child
    let work := fun stages (ports : Fin (FlatCoordinateCleanSchedule.tapeCount stages) ↪ Fin H) (S : Stacks H prime) =>
      let seed := phaseBasisTapes (w := p.w+1) (W := p.stageWidth) stages (fun _ => 0)
      ∀ i, i ≠ segmentSource stages → ∀ h, seed.tape i h = readAt blank (S.L (ports i)) (S.R (ports i)) (h-seed.head i)
    ∀ (data : Fin k → Fin V → ZMod 2) u S, HelperFan fan data S →
      (∃ old, stored old (embStk place S)) → (∀ i, 35 ≤ i.val → S.L (place i) = [] ∧ S.R (place i) = []) →
      work A a S → work B b S →
      ∃ z F t, Exec host (enter.seq (mid.seq leave)) (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F (t+tapeCharge cleanupWeight (frameSlots fan) F)
          (price+(rate+localRate)*V+(base+swaps*swapVolumeRate p.w)*V+341+tapeCharge cleanupWeight (frameSlots fan) S) ∧
        HelperFan fan (moveOwnerEffect owners data (selectedPhaseIndex afterCopy j).val (selectedMoveEdge afterCopy j)) F := by
  intro bank
  let owner := owners (paidRegister (selectedPhaseIndex afterCopy j).val)
  obtain ⟨C,rev,fwd,basis⟩ := selectedOwnerBasis afterCopy j
  let A := M8.Machine.Segments.description _ rev.good
  let B := M8.Machine.Segments.description _ fwd.good
  obtain ⟨H,place,fan,a,b,shared,sa,sb,off,pre,post⟩ := phaseMoveBanks (bank 24) owner A B
  let coeff (stages : List (FlatCoordinateSchedule.Op 16)) := 26*(FlatCoordinateCleanSchedule.constant stages*(FlatCoordinateCleanSchedule.tapeCount stages+5))
  refine ⟨A,B,H,place,fan,a,b,coeff A+16+coeff B,?_⟩
  intro P U Q body entry capA capB host enter leave mid p blocks D leafRate rate base swaps move root rows label band V stored child price work data u S live old free readyA readyB
  obtain ⟨size,call⟩ := move.ownerCall root rows label band owner place fan shared (fun i ne => (off i ne).1)
  obtain ⟨loaded,y,first,last,effect⟩ := basis p k owners data size
  obtain ⟨v,E,l,runA,userA,billA,liveA,_,frameA⟩ :=
    phaseBasisOwnerPass A a fan owner sa (fun i ne => (off i ne).2.1) host capA data loaded first u S live readyA
  have keep i (ne : i ≠ bank 24) := frameA (place i) (pre i ne)
  have record : stored loaded (embStk place E) := by
    obtain ⟨x,hx⟩ := old
    apply hx.returnPayload (outBank := bank) (fun i ne => keep _ (bank.injective.ne ne))
    intro h
    have cell := fanPayload liveA owner h
    change _ = readAt blank (E.L (place (bank 24))) (E.R (place (bank 24))) _
    rw [shared]
    simpa only [Function.update_self,List.map_ofFn] using cell.symm
  obtain ⟨q,G,m,runM,billM,userM,liveM,_,_,frameM⟩ := call _ v E liveA ⟨_,record⟩ (by
    intro i hi
    have ne : i ≠ bank 24 := fun eq => by have h := congrArg Fin.val eq; change i.val = 24 at h; omega
    exact ⟨(keep i ne).1.trans (free i hi).1,(keep i ne).2.trans (free i hi).2⟩)
  simp only [Function.update_self,Function.update_idem] at liveM
  obtain ⟨z,F,n,runB,userB,billB,out,_⟩ :=
    phaseBasisOwnerPass B b fan owner sb (fun i ne => (off i ne).2.2) host capB _ y
      (by simpa only [Function.update_self] using last) q G liveM (by
        intro i ne h
        obtain ⟨ha,hp⟩ := post i ne
        obtain ⟨lm,rm⟩ := frameM _ hp
        obtain ⟨la,ra⟩ := frameA _ ha
        rw [lm,rm,la,ra]
        exact readyB i ne h)
  refine ⟨z,F,_,runA.seq (runM.seq runB),userB.trans (userM.trans userA),?_,?_⟩
  · intro js nd
    have hA := billA js nd
    have hM := billM js nd
    have hB := billB js nd
    let stock := fun X => tapeCharge cleanupWeight (frameSlots fan) X
    let charge := fun X => tapeCharge cleanupWeight js X
    change l+stock E+charge E ≤ charge S+(coeff A*V+156+stock S) at hA
    change m+stock G+charge G ≤ charge E+(price+rate*p.cells+6+(base+swaps*swapVolumeRate p.w)*V+16*V+23+stock E) at hM
    change n+stock F+charge F ≤ charge G+(coeff B*V+156+stock G) at hB
    change l+(m+n)+stock F+charge F ≤ charge S+_
    rw [← p.stageCells] at hM
    change m+stock G+charge G ≤ charge E+(price+rate*V+6+(base+swaps*swapVolumeRate p.w)*V+16*V+23+stock E) at hM
    change _ ≤ charge S+(price+(rate+(coeff A+16+coeff B))*V+(base+swaps*swapVolumeRate p.w)*V+341+stock S)
    simp only [Nat.add_mul] at hM ⊢
    omega
  · simpa only [Function.update_idem,← effect] using out

end IntegerMultBounds.MathlibTM2.M6.BitNode
