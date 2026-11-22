module

public import IntegerMultBounds.MathlibTM2.Host.GatherRecords

/-! Read a selected PR589 routing record without disturbing the inherited block. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node

private theorem selectRecord {α : Type} (before after : List (List α)) (record : List α) :
    gatherSymbols (before ++ record :: after)
      (List.replicate before.length false ++ true :: List.replicate after.length false) = [record] := by
  rw [gatherSymbols_append _ _ _ _ (by simp)]
  simp [gatherSymbols_replicate,gatherSymbols]

/-- A single fixed program prepends the selected record to the destination.
It restores the input, the selector and the work registers, so another
selection can read the same block. -/
theorem sweepGatherRecord_exec {P U : Type} {T Q A W : ℕ} (body : P → Pr P T Q A U)
    {src mask width symbols ts tm acc out cs : Fin T}
    (regs : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (before after : List (List (Fin (A+4)))) (record tail : List (Fin (A+4)))
    (sizes : ∀ row ∈ before ++ record :: after, row.length = W)
    (v : HS T Q A U) (S : Stacks T A)
    (input : S.R src = (before ++ record :: after).flatten ++ tail)
    (selector : S.R mask = (List.replicate before.length false ++ true :: List.replicate after.length false).map bitSymbol)
    (recordWidth : (S.R width).length = W) (fresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ z steps, z.user = v.user ∧ steps ≤ (before.length+1+after.length)*(16*W+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs (fun x => decide (x = bitSymbol true)))
        (mk v S) steps (mk z {S with R := Function.update S.R out (record ++ S.R out)}) := by
  let flags := List.replicate before.length false ++ true :: List.replicate after.length false
  have decode (b : Bool) : decide (bitSymbol (a := A) b = bitSymbol true) = b := by cases b <;> rfl
  obtain ⟨z,t,user,paid,run⟩ := gatherRecords_exec (body := body) (cs := cs) regs (flags.map bitSymbol)
    (before ++ record :: after) W (fun x => decide (x = bitSymbol true))
    (by simp [flags]) sizes tail v S input selector recordWidth fresh
  refine ⟨z,t,user,?_,?_⟩
  · simpa [flags,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using paid
  · have decoded : (flags.map (bitSymbol (a := A))).map (fun x => decide (x = bitSymbol true)) = flags := by
      simp [List.map_map,Function.comp_def,decode]
    simpa only [decoded,flags,selectRecord,List.flatten_cons,List.flatten_nil,List.append_nil] using run

end IntegerMultBounds.MathlibTM2.M6.BitNode
