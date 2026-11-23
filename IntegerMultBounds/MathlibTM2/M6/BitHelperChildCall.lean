module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperSlotSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Call an inherited helper interval using the scheduled worker's record contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open Certificates.PR589 in
/-- A paid helper MOVE calls the scheduled worker with its record, restores its scratch,
and preserves the stacks outside the worker ports. -/
theorem helperRecordCall_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U)
    (f : Fin nodeChildren5.length → P) (budget : Fin nodeChildren5.length → ℕ)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (record : List (Fin (prime+4)))
    (parent : Descriptor) (stage : Fin 9) (run : Fin 32 × Fin 5) (helper : Fin 439)
    (w : ℕ) (width : parent.width = 64*(w+1)) :
    let edges := Geometry.Moves.phaseEdges.filter fun p => Geometry.moveRank p.1 p.2 != 0
    ∀ j : Fin edges.length, let edge := edges[j.val]
      let a := Geometry.Dimensions.value edge.1
      let d := Geometry.Dimensions.value edge.2
      let lo := min a d
      let hi := max a d
      let start := (helperPosition (stage,helper)).val
      let physical := inheritedInterval (role parent 142080) ((start+lo)*(w+1)) ((hi-lo)*(w+1)) ((64-(start+hi))*(w+1))
      let i := phaseChildPositions.choose (stage,run,j)
      let child := scheduledChild prime parent i
      let W := (prime^(w+1))^112 * CopyChildLayout.spectators (role parent 142080)
      ∃ size : volume prime physical = (prime^(w+1))^16*W,
        let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) (scheduledRecordPorts ports)
          (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
        let clean := fun (S : Stacks T prime) => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
          S.L (ports j) = [] ∧ S.R (ports j) = []
        ∃ position, ScheduledChildExec parent child w W ports record position body (f i) (budget i) →
          ∀ u S word, stored word S → clean S →
          ∃ z F n, Exec body (.call (f i)) (mk u S) n (mk z F) ∧ n ≤ budget i+2 ∧ z.user = u.user ∧
            stored (fun k => Shared50RecursiveNodeRows.transpose (one_dvd physical.rows)
              (fun j => word (j.cast size)) (k.cast size.symm)) F ∧ clean F ∧
            ∀ j, (∀ l, ports l ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro edges j edge a d lo hi start physical i child W
  have shape := helperMove_shape parent stage run helper (w+1) width j
  have mem := List.mem_filter.mp (List.getElem_mem (l := edges) (n := j.val) j.isLt)
  have bounds := phaseInterval_bounds (Geometry.Moves.phase_checked edge mem.1)
    (Nat.pos_of_ne_zero (bne_iff_ne.mp mem.2))
  have ordered : lo ≤ hi := bounds.1.le
  have fits : hi ≤ 8 := bounds.2
  have lower : start < 56 := (helperPosition (stage,helper)).isLt
  have split : (role parent 142080).width = (start+lo)*(w+1)+(hi-lo)*(w+1)+(64-(start+hi))*(w+1) := by
    rw [← Nat.add_mul,← Nat.add_mul]
    change parent.width = _
    rw [width]
    congr 1
    omega
  have size : volume prime physical = (prime^(w+1))^16*W := by
    rw [inheritedInterval_volume _ _ _ _ split]
    simp only [volume,role,CopyChildLayout.spectators,W,width,Nat.mul_comm 64 (w+1),pow_mul]
    ring
  refine ⟨size,?_⟩
  intro stored clean
  obtain ⟨e,_,transpose⟩ := scheduledTranspose_onOwner shape
  let position := e.trans (finCongr size)
  refine ⟨position,?_⟩
  intro worker u S word ready free
  have smaller : child.width < parent.width := by
    simpa only [child,scheduledChild,rankDescriptor,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
      using Nat.mul_lt_mul_of_pos_right ((nodeChildren5_le i).trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)
  obtain ⟨z,F,n,y,run,cost,user,out,blank,frame,reads⟩ := worker smaller u S word ready free
  refine ⟨z,F,_,Exec.call run,by omega,user,?_,blank,frame⟩
  convert out using 1
  funext k
  obtain ⟨h,rfl⟩ := position.surjective k
  exact ((reads h).trans (congrFun (transpose (fun j => word (j.cast size))) h)).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
