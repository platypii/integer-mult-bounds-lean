module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage

/-! A small register layout for grouped execution, independent of numerical
construction history. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def batchRuntimeRegisters {A : ℕ} (q l B L : ℕ) (page result : List (Fin (A+4))) : Regs 117 A :=
  fun k => if k.val = 94 then List.replicate (2*q+8) tick else
    if k.val = 100 then List.replicate q tick else if k.val = 101 then List.replicate l tick else
    if k.val = 102 then List.replicate L tick else if k.val = 103 then List.replicate L tick else
    if k.val = 108 then List.replicate (2*B) tick else if k.val = 110 then page else
    if k.val = 93 then result else []

theorem batchRuntimeRegisters_update_result {A : ℕ} (q l B L : ℕ)
    (page old result : List (Fin (A+4))) :
    Function.update (batchRuntimeRegisters q l B L page old) 93 result =
      batchRuntimeRegisters q l B L page result := by
  funext k
  by_cases hk : k.val = 93
  · have he : k = 93 := Fin.ext hk
    subst k; simp [batchRuntimeRegisters]
  have hn : k ≠ (93 : Fin 117) := fun he => hk (congrArg Fin.val he)
  simp [batchRuntimeRegisters, hn, hk]

theorem inputSourceBank_R {A : ℕ} (q l B L : ℕ) (X Z : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) (k : Fin 117) :
    (inputSourceBank q l (2*q+8) B L 0 X Z [] [] tail tailX inp out).R k =
      batchRuntimeRegisters q l B L
        (cstream A (2*q+8) ((List.range (B+B)).flatMap (rowBank B X Z)) ++ tailX) tail k := by
  by_cases hk : k.val ∈ [93, 94, 96, 100, 101, 102, 103, 108, 110, 111, 116]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h | h | h | h | h
    all_goals simp [inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, batchRuntimeRegisters,
      Function.update_apply, Fin.ext_iff, h, cstream, show 2*B = B+B by omega]
  · have hn (n : ℕ) (h : n ∈ [93, 94, 96, 100, 101, 102, 103, 108, 110, 111, 116]) : k.val ≠ n :=
      fun he => hk (he ▸ h)
    simp [inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, batchRuntimeRegisters,
      Fin.ext_iff, hn 93 (by decide), hn 94 (by decide), hn 96 (by decide),
      hn 100 (by decide), hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 108 (by decide), hn 110 (by decide), hn 111 (by decide), hn 116 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
