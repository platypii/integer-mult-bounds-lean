module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish

/-! Physical descriptor schedules and their exact final frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {N T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def descriptorScheduleTape (work : Fin N → Fin T) (words : β → Fin N → List (Fin (A+4)))
    (records : List β) : List (Fin (A+4)) :=
  records.flatMap (fun r => descriptorBankTape (placedDescriptorFields work (words r)))

def descriptorLoopFinal (work : Fin N → Fin T) (words : β → Fin N → List (Fin (A+4)))
    (records : List β) (src saved result clock : Fin T)
    (rest : List (Fin (A+4))) (outputs : List (List (Fin (A+4)))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R src rest)
    saved ((descriptorScheduleTape work words records).reverse++S.R saved))
    result (outputs.reverse.flatten++S.R result)) clock [])}

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
