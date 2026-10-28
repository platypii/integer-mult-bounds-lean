module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank

/-! Packet scanning is linear in the physical tape; reversing the saved tape restores it. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem descriptorBankTape_length (fields : List (Fin T × List (Fin (A+4)))) :
    (descriptorBankTape fields).length = 2*(fields.map (fun f => f.2.length)).sum+fields.length := by
  induction fields with
  | nil => simp [descriptorBankTape]
  | cons f fields ih =>
    change (descriptorPacket f.2++descriptorBankTape fields).length = _
    rw [List.length_append,ih]
    simp only [descriptorPacket,preFld,List.length_append,List.length_replicate,List.length_singleton,
      List.map_cons,List.sum_cons,List.length_cons,List.length_nil]
    omega

theorem takeDescriptorBankCost_eq (fields : List (Fin T × List (Fin (A+4)))) :
    takeDescriptorBankCost fields = 23*(fields.map (fun f => f.2.length)).sum+24*fields.length+1 := by
  induction fields with
  | nil => simp [takeDescriptorBankCost]
  | cons f fields ih =>
    simp only [takeDescriptorBankCost,List.map_cons,List.sum_cons,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem takeDescriptorBankCost_le_tape (fields : List (Fin T × List (Fin (A+4)))) :
    takeDescriptorBankCost fields ≤ 24*(descriptorBankTape fields).length+1 := by
  rw [takeDescriptorBankCost_eq,descriptorBankTape_length]
  omega

theorem takePlacedDescriptorBankCost_eq (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4))) :
    takeDescriptorBankCost (placedDescriptorFields work words) =
      23*(∑ i, (words i).length)+24*N+1 := by
  rw [takeDescriptorBankCost_eq]
  simp only [placedDescriptorFields,List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn]

theorem restoreDescriptorTape_exec (src saved : Fin T) (hreg : saved ≠ src)
    (v : HS T Q A U) (S : Stacks T A) (consumed : List (Fin (A+4)))
    (hsaved : S.R saved = consumed.reverse) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveR saved src id) (mk v S) (2*consumed.length+2)
        (mk v' {S with R := Function.update (Function.update S.R saved []) src (consumed++S.R src)}) := by
  obtain ⟨v',hu,he⟩ := moveR_exec body saved src hreg id v S
  refine ⟨v',hu,?_⟩
  simpa only [movedR,hsaved,List.length_reverse,List.map_id,List.reverse_reverse] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
