module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage

/-! Identify the executed construction-to-runtime transition with the canonical
single-cell arithmetic ABI, including all empty work buffers and spectators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- The state underneath the generated factor/generator banks. Numeric controls
and the per-call RHS are ordinary inputs; weights have already been generated. -/
def cellConstructionBank {A : ℕ} (P M q l L W : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A where
  inp := inp
  out := out
  L := fun _ => []
  R := fun k => if k.val = 94 then List.replicate W tick else
    if k.val = 101 then List.replicate M tick else if k.val = 102 then List.replicate L tick else
    if k.val = 103 then List.replicate L tick else if k.val = 109 then List.replicate l tick else
    if k.val = 112 then List.replicate q tick else if k.val = 114 then List.replicate P tick else
    if k.val = 110 then outs ++ (factors ++ (rhs ++ borrowed)) else if k.val = 93 then outTail else []

def cellRuntimeBank {A : ℕ} (P s t u band L q l W M : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := cellConstructionBank P M q l L W outs factors rhs borrowed outTail inp out
  let B := cellHeaderBank (retainedGeneratorBank S P s t u band L q (M + 1)) q l
  { B with R := (Function.update B.R 110
    ((generatorPage A P s t u band L q (M + 1) ++ outs) ++ (rhs ++ (factors ++ borrowed)))) }

theorem cellRuntimeBank_eq_inputSourceBank {A : ℕ} (P s t u band L q l W M : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    cellRuntimeBank P s t u band L q l W M outs factors rhs borrowed outTail inp out =
      inputSourceBank q l (2 * q + 8) 1 L 0
        (fun _ => columnWords P s t u band L q (M + 1))
        (fun _ => reversedColumnWords P s t u band L q (M + 1)) [] [] outTail
        (csyms A (2 * q + 8) (reciprocalWord P s t u band L q (M + 1)) ++
          (outs ++ (rhs ++ (factors ++ borrowed)))) inp out := by
  have hrow (xs zs : List GaussianInt) :
      (List.range (1 + 1)).flatMap (rowBank 1 (fun _ => xs) (fun _ => zs)) = xs ++ zs := by
    simp [rowBank, List.range_succ]
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h110 : k.val = 110
    · have he : k = 110 := Fin.ext h110
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails,
        Fixed.start, Fixed.inputBank, hrow, generatorPage, cstream_append, List.append_assoc]
    by_cases h94 : k.val = 94
    · have he : k = 94 := Fin.ext h94
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    by_cases h100 : k.val = 100
    · have he : k = 100 := Fin.ext h100
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    by_cases h101 : k.val = 101
    · have he : k = 101 := Fin.ext h101
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    by_cases h102 : k.val = 102
    · have he : k = 102 := Fin.ext h102
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    by_cases h103 : k.val = 103
    · have he : k = 103 := Fin.ext h103
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    by_cases h108 : k.val = 108
    · have he : k = 108 := Fin.ext h108
      subst k
      simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    simp [cellRuntimeBank, cellHeaderBank, retainedGeneratorBank, cellConstructionBank,
      inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails,
      Fixed.start, Fixed.inputBank, Function.update_apply, Fin.ext_iff,
      h110, h94, h100, h101, h102, h103, h108, hrow]
    split_ifs <;> first | rfl | omega

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- The actual transition establishes the bank identified above, with all setup
workspace released and the RHS staged in the retained page. -/
theorem prepareCanonicalCellRuntime_exec (P s t u band L q l W M : ℕ)
    (outs factors rhs borrowed outTail : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) (v : HS 117 Q A U)
    (houts : outs.length = L * (2 * q + 8)) (hfactors : factors.length = L * (2 * q + 8))
    (hrhs : rhs.length = L * (2 * q + 8)) :
    let S := cellConstructionBank P M q l L W outs factors rhs borrowed outTail inp out
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCellRuntimeCost P M L q l W ∧
      Exec body prepareCellRuntime
        (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W)
          P s t u band L q W (M + 1))) m
        (mk v' (cellRuntimeBank P s t u band L q l W M outs factors rhs borrowed outTail inp out)) := by
  let S := cellConstructionBank P M q l L W outs factors rhs borrowed outTail inp out
  have hblank : ∀ r, S.R (cr r) = [] := by
    intro r
    obtain ⟨hlo, hhi, h93, h94⟩ := cr_range r
    have hne (n : ℕ) (hn : 96 ≤ n) : (cr r).val ≠ n := by omega
    simp [S, cellConstructionBank, h93, h94, hne 101 (by decide), hne 102 (by decide),
      hne 103 (by decide), hne 109 (by decide), hne 112 (by decide),
      hne 114 (by decide), hne 110 (by decide)]
  have hrun := prepareCellRuntime_exec (body := body) P s t u band L q l W M
    outs factors rhs borrowed v S
    (by simp [S, cellConstructionBank]) (by simp [S, cellConstructionBank])
    (by simp [S, cellConstructionBank]) (by simp [S, cellConstructionBank])
    (by simp [S, cellConstructionBank]) (by simp [S, cellConstructionBank])
    (by simp [S, cellConstructionBank]) houts hfactors hrhs
    (by simp [S, cellConstructionBank]) hblank (by simp [S, cellConstructionBank]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S, cellConstructionBank])
  exact hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
