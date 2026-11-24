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
    let edge := selectedMoveEdge afterCopy
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ (T : ℕ) (fits : rowSwapBlock.tapes+35 ≤ T) (P : J → Type)
        (tables : ∀ j, Option (P j) → Pr (Option (P j)) T Q prime U) (rate : ℕ) (base swaps : J → ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (j : J),
        RoutedPhaseMove stage run afterCopy j fits (tables j) none D leafRate rate (base j) (swaps j) p blocks := by
  intro inst J edge
  classical
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
