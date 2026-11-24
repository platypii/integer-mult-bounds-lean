module

public import IntegerMultBounds.MathlibTM2.M6.BitBandMoveDispatch
public import IntegerMultBounds.MathlibTM2.M6.BitSweepChildWidth

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)

/-- All selected MOVE positions share a tape count and a linear allowance.
The procedure table and code at each position specialize to its certified rank. -/
theorem selectedBandMoves {U : Type} (stage : Fin 9) (run : StageRun) (afterCopy : Bool) :
    let _ := BinaryRadixEqualShared.supplierNet
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ N : ℕ, ∀ {H : ℕ} (port : J → Fin (N+35) ↪ Fin H),
      ∃ (P : J → Type) (tables : ∀ j, P j → Pr (P j) H Q prime U) (codes : ∀ j, Pr (P j) H Q prime U) (rate : ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (j : J),
        let i := phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)
        let ports := port j
        let table := tables j
        let code := codes j
        let child := scheduledChild prime p.node i
        let V := (prime^(p.w+1))^16*p.stageWidth
        let n := CopyChildLayout.spectators child
        let archive := binSyms n.size n ++ separator :: binSyms p.root.width.size p.cutoff
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) →
        49*(p.w+1) ≤ 64*p.cutoff →
        ∃ position : Fin (volume prime child) ≃ Fin V,
          (∀ j, (position j).val = (CopyChildLayout.packActive child j).val) ∧
          let price := cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child
          let bank := scheduledRecordPorts ports
          let stored := RecordReady (b := prime) (w := p.w) (W := p.stageWidth) (d := 16) bank
            (prime^(p.w+1)).size p.stageWidth.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
          let clean := fun S : Stacks H prime => ∀ j : Fin (N+35), 35 ≤ j.val → S.L (ports j) = [] ∧ S.R (ports j) = []
          ∀ u S word, stored word S → clean S →
            ∃ z F t y, Exec table code (mk u S) t (mk z F) ∧
              CleanupBound S F t (price+rate*p.cells) ∧
              z.user = u.user ∧ stored y F ∧ clean F ∧
              (∀ j, (∀ k, ports k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
              ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro inst J
  classical
  obtain ⟨q,compile⟩ := dispatchedBandMove (U := U)
  refine ⟨q,?_⟩
  intro Q enough
  obtain ⟨minimum,R,build⟩ := compile enough
  let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  let leaf := max R (391*(163+core))
  refine ⟨minimum,leaf,?_⟩
  intro D large
  obtain ⟨N,place⟩ := build D large
  refine ⟨N,?_⟩
  intro H port
  let index (j : J) := selectedPhaseIndex afterCopy j
  let childIndex (j : J) := phaseChildPositions.choose (stage,run,index j)
  let rank (j : J) := nodeChildren5[(childIndex j).val]
  have positive (j : J) : 0 < rank j := by
    dsimp only [rank,childIndex]
    rw [(phaseChildPositions.choose_spec stage run (index j)).1]
    have mem := List.mem_filter.mp (List.getElem_mem (l := Geometry.Moves.phaseEdges.filter positiveMove) (index j).isLt)
    exact Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2)
  choose P table code rate call using fun j => place (port j) (rank j) (positive j) (phaseChildRank_le stage run (index j))
  refine ⟨P,table,code,Finset.univ.sup rate,?_⟩
  intro p blocks j i ports body worker child V n archive root rows label band
  have size : (prime^child.width*prime^child.width)*n = V := by
    calc
      _ = volume prime child := by dsimp only [volume,n,CopyChildLayout.spectators]; ring
      _ = p.cells := scheduledChildVolume p i
      _ = V := p.stageCells.symm
  let position := (CopyChildLayout.packActive child).trans (finCongr size)
  have packed (h) : (position h).val = (CopyChildLayout.packActive child h).val := rfl
  refine ⟨position,packed,?_⟩
  intro price bank stored clean u S x ready free
  have smaller : child.width < p.node.width := by
    have width : child.width = rank j*(p.w+1) := by
      change nodeChildren5[i.val]*(p.node.width/64) = _
      rw [p.width,Nat.mul_div_cancel_left _ (by decide)]
    have bound : rank j ≤ 7 := phaseChildRank_le stage run (index j)
    have span := Nat.mul_le_mul_right (p.w+1) bound
    rw [width,p.width]
    omega
  obtain ⟨z,F,t,y,exec,paid,user,out,fresh,frame,action⟩ :=
    call j p blocks i root rows label rfl band position packed leaf (le_max_right ..) smaller u S x ready free
  refine ⟨z,F,t,y,exec,?_,user,out,fresh,frame,action⟩
  intro js nd
  apply (paid js nd).trans (Nat.add_le_add_left ?_ _)
  apply Nat.add_le_add _ (Nat.mul_le_mul_right p.cells (Finset.le_sup (s := Finset.univ) (f := rate) (Finset.mem_univ j)))
  change (if p.cutoff < child.width then _ else _) ≤ price
  split
  · exact cutoffTreeBudget_leaf_mono D (le_max_left ..) _ _ _
  · rename_i stop
    dsimp only [price]
    cases p.depth-(p.path.length+1) <;> simp [cutoffTreeBudget,stop] <;> exact le_rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
