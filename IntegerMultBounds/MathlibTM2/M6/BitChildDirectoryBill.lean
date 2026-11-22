module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Partition the child-time directory by physical program position. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks Certificates.PR589

private theorem rangeBill (start n : ℕ) (time : ℕ → ℕ) :
    ((List.range' start n).map time).sum = ∑ j : Fin n, time (start+j.val) := by
  have eq : (List.range' start n).map time = List.ofFn (fun j : Fin n => time (start+j.val)) := by
    apply List.ext_getElem
    · simp
    · intro j hj hk
      simp [List.getElem_range']
  rw [eq,List.sum_ofFn]

private theorem positionBill {α : Type} (xs : List α) (entries : α → List ℕ) (time : ℕ → ℕ) :
    (∑ p : Fin xs.length, ((List.range' ((xs.take p.val).flatMap entries).length
        (entries xs[p.val]).length).map time).sum) =
      ∑ j : Fin (xs.flatMap entries).length, time j.val := by
  let ids := List.finRange xs.length
  let atPos := fun p : Fin xs.length => xs[p.val]
  have allEntries : ids.map atPos = xs := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem
  have earlier (p : Fin xs.length) : ((ids.take p.val).flatMap (entries ∘ atPos)) =
      (xs.take p.val).flatMap entries := by
    convert congrArg (fun ys => (ys.take p.val).flatMap entries) allEntries using 1 <;> simp [← List.map_take,List.flatMap_map,Function.comp_def]
  have full : ids.flatMap (entries ∘ atPos) = xs.flatMap entries := by
    simpa [List.flatMap_map,Function.comp_def] using congrArg (List.flatMap entries) allEntries
  have total := scheduledChildBill (entries ∘ atPos) time ids (List.nodup_finRange _) 0
  simp only [ids,List.idxOf_finRange,Nat.zero_add] at total
  simp only [ids] at earlier full
  rw [full,rangeBill] at total
  simp only [earlier,Nat.zero_add] at total
  rw [← List.sum_ofFn,List.ofFn_eq_map]
  exact total

/-- Sweep ranges and idle-directory offsets partition the actual child list,
including the terminal remainder, whose child list is empty. -/
theorem nodeChildDirectoryBill (time : ℕ → ℕ) :
    (∑ i : Fin 9, ((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum) +
    (∑ i : Fin 9, ∑ j : Fin idleCopies.length, time (idleDirectoryIndex (i,j)).val) =
    ∑ j : Fin nodeChildren5.length, time j.val := by
  let stage (i : Fin 9) : Fin nodeProgram.length := ⟨stagePos i.val,(stagePos_le _ i.isLt).1⟩
  let idle (i : Fin 9) : Fin nodeProgram.length := ⟨idlePos i.val,idlePos_le _ (by omega)⟩
  letI : NeZero nodeProgram.length := ⟨by decide⟩
  let other : List (Fin nodeProgram.length) := [3,6,9,12,15,18,24,25,26,27,28]
  let bill (p : Fin nodeProgram.length) := ((List.range' ((nodeProgram.take p.val).flatMap Piece.children).length
      nodeProgram[p.val].children.length).map time).sum
  have perm : (List.finRange nodeProgram.length).Perm
      ((List.finRange 9).map stage ++ (List.finRange 9).map idle ++ other) := by decide +kernel
  have stageAt (i : Fin 9) : nodeProgram[(stage i).val] = .stage i :=
    (List.getD_eq_getElem _ _ (stage i).isLt).symm.trans (nodeProgram_at.1 i)
  have idleAt (i : Fin 9) : nodeProgram[(idle i).val] = .remainder i.val :=
    (List.getD_eq_getElem _ _ (idle i).isLt).symm.trans (nodeProgram_at.2.1 _ (by omega))
  have idleBill i : bill (idle i) = ∑ j : Fin idleCopies.length, time (idleDirectoryIndex (i,j)).val := by
    have len := congrArg List.length (idleCopies_ranks i)
    rw [List.length_map] at len
    have count := (congrArg (fun p : Piece => p.children.length) (idleAt i)).trans len.symm
    change ((List.range' (idleChildStart i) nodeProgram[(idle i).val].children.length).map time).sum = _
    rw [count,rangeBill]
    rfl
  let emptyPiece : Piece → Bool
    | .stage _ => false | .remainder i => i == 9 | _ => true
  have inactive : ∀ p ∈ other, emptyPiece nodeProgram[p.val] = true := by decide +kernel
  have free p (h : p ∈ other) : bill p = 0 := by
    have fact := inactive p h
    cases eq : nodeProgram[p.val] with
    | stage i => simp [eq,emptyPiece] at fact
    | remainder i =>
      simp [eq,emptyPiece] at fact
      subst i
      simp [bill,eq,Piece.children,remainderRanks_eq.2,List.flatMap_def]
    | bridge d s => simp [bill,eq,Piece.children]
    | exchangeSides => simp [bill,eq,Piece.children]
  have zero : (other.map bill).sum = 0 := by
    have eq := List.map_congr_left (g := fun _ => 0) free
    rw [eq]
    simp
  have stages i : bill (stage i) = ((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum := by
    have count := congrArg (fun p : Piece => p.children.length) (stageAt i)
    change ((List.range' (stageChildStart i) nodeProgram[(stage i).val].children.length).map time).sum = _
    rw [count]
    rfl
  have total := positionBill nodeProgram Piece.children time
  change (∑ p, bill p) = _ at total
  have listed {n : ℕ} (f : Fin n → ℕ) : ((List.finRange n).map f).sum = ∑ j, f j := by
    rw [← List.ofFn_eq_map,List.sum_ofFn]
  rw [← listed bill,(perm.map bill).sum_eq,List.map_append,List.sum_append,zero,Nat.add_zero,
    List.map_append,List.sum_append,List.map_map,List.map_map,listed,listed] at total
  have size : (nodeProgram.flatMap Piece.children).length = nodeChildren5.length := by rw [nodeChildren5]
  exact (by simpa only [Function.comp_apply,stages,idleBill] using total : _ = _).trans
    (congrArg (fun n => ∑ j : Fin n, time j.val) size)

end IntegerMultBounds.MathlibTM2.M6.BitNode
