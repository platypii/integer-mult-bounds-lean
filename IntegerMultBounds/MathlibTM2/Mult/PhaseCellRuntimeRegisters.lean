module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalCellRuntime

/-! A small register layout for the canonical single-cell runtime bank. This
keeps cleanup proofs independent of the construction bank's nested updates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def cellRuntimeRegisters {A : ℕ} (q l L : ℕ) (page result : List (Fin (A + 4))) : Regs 117 A :=
  fun k => if k.val = 94 then List.replicate (2 * q + 8) tick else
    if k.val = 100 then List.replicate q tick else if k.val = 101 then List.replicate l tick else
    if k.val = 102 then List.replicate L tick else if k.val = 103 then List.replicate L tick else
    if k.val = 108 then List.replicate 2 tick else if k.val = 110 then page else
    if k.val = 93 then result else []

theorem cellRuntimeBank_R {A : ℕ} (P s t u band L q l W M : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (k : Fin 117) :
    (cellRuntimeBank P s t u band L q l W M outs factors rhs borrowed outTail inp out).R k =
      cellRuntimeRegisters q l L ((generatorPage A P s t u band L q (M + 1) ++ outs) ++
        (rhs ++ (factors ++ borrowed))) outTail k := by
  by_cases hk : k.val ∈ [94, 100, 101, 102, 103, 108, 110, 93]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with h | h | h | h | h | h | h | h <;>
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        cellRuntimeRegisters, Function.update_apply, Fin.ext_iff, h]
  · have hn (n : ℕ) (h : n ∈ [94, 100, 101, 102, 103, 108, 110, 93]) : k.val ≠ n :=
      fun he => hk (he ▸ h)
    simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
      cellRuntimeRegisters, Fin.ext_iff,
      hn 94 (by decide), hn 100 (by decide), hn 101 (by decide), hn 102 (by decide),
      hn 103 (by decide), hn 108 (by decide), hn 110 (by decide), hn 93 (by decide)]
    intro h109 h112 h114 _
    simp [h109, h112, h114]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
