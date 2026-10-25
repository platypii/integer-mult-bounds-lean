module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage

/-! The ordinary unary/raw-RHS batch input and the exact arithmetic ABI
produced by its executed numerical setup and payload routing. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def unaryBatchBank {A : ℕ} (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A where
  inp := inp
  out := out
  L := fun _ => []
  R := fun k => if k.val = 101 then List.replicate N tick else
    if k.val = 102 then List.replicate L tick else if k.val = 103 then List.replicate L tick else
    if k.val = 97 then List.replicate s tick else if k.val = 98 then List.replicate t tick else
    if k.val = 99 then List.replicate u tick else if k.val = 100 then List.replicate band tick else
    if k.val = 109 then (List.range B).flatMap (fun i => originPacket A (lo i)) ++ List.replicate l tick else
    if k.val = 112 then List.replicate q tick else if k.val = 114 then List.replicate P tick else
    if k.val = 116 then List.replicate B tick else
    if k.val = 110 then rhs ++ borrowed else if k.val = 93 then outTail else []

theorem generatedBatchBank_eq_inputSourceBank {A : ℕ} (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    generatedBatchBank (unaryBatchBank P N q l s t u band L B lo rhs borrowed outTail inp out)
      P s t u band L q N l B lo rhs borrowed (List.replicate l tick) =
      inputSourceBank q l (2*q+8) B L 0
        (fun _ => columnWords P s t u band L q (N+1))
        (fun _ => reversedColumnWords P s t u band L q (N+1)) [] [] outTail
        (csyms A (2*q+8) (reciprocalWord P s t u band L q (N+1)) ++
          (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L (lo i)) ++ rhs ++
          (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L (lo i)) ++ borrowed) inp out := by
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k.val ∈ [93, 94, 96, 97, 98, 99, 100, 101, 102, 103, 108, 109, 110, 112, 114, 115, 116]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals simp [generatedBatchBank, batchHeaderBank, batchWeightedBank, batchInverseBank,
        batchWeightedBase, consumedGeometryBank, geometryHeaderPorts, unaryBatchBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails,
        Fixed.start, Fixed.inputBank, Function.update_apply, Fin.ext_iff, h,
        batchGeneratorPage_eq_rowBank, List.append_assoc, show 2*B = B+B by omega]
    · have hn (n : ℕ) (h : n ∈ [93, 94, 96, 97, 98, 99, 100, 101, 102, 103, 108, 109, 110, 112, 114, 115, 116]) :
          k.val ≠ n := fun he => hk (he ▸ h)
      simp [generatedBatchBank, batchHeaderBank, batchWeightedBank, batchInverseBank,
        batchWeightedBase, consumedGeometryBank, geometryHeaderPorts, unaryBatchBank,
        inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails,
        Fixed.start, Fixed.inputBank, Function.update_apply, Fin.ext_iff,
        hn 93 (by decide), hn 94 (by decide), hn 96 (by decide), hn 97 (by decide), hn 98 (by decide),
        hn 99 (by decide), hn 100 (by decide), hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
        hn 108 (by decide), hn 109 (by decide), hn 110 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 115 (by decide), hn 116 (by decide)]
      split_ifs <;> simp [cstream]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem unaryBatchBank_setup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L) (hLs : L ≤ s) (hlo : ∀ i < B, lo i < s)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 117 Q A U) (hrhs : rhs.length = B*L*(2*q+8)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBatchSetupCost P N q s t u band l L B lo ∧
      Exec body (generatedBatchSetup hQ)
        (mk v (unaryBatchBank P N q l s t u band L B lo rhs borrowed outTail inp out)) m
        (mk v' (inputSourceBank q l (2*q+8) B L 0
          (fun _ => columnWords P s t u band L q (N+1))
          (fun _ => reversedColumnWords P s t u band L q (N+1)) [] [] outTail
          (csyms A (2*q+8) (reciprocalWord P s t u band L q (N+1)) ++
            (List.range B).flatMap (fun i => outputWeightRow A (2*q+8) q P s t u L (lo i)) ++ rhs ++
            (List.range B).flatMap (fun i => inputWeightRow A (2*q+8) q P s t u L (lo i)) ++ borrowed) inp out)) := by
  let S := unaryBatchBank P N q l s t u band L B lo rhs borrowed outTail inp out
  have hlow (k : Fin 117) (hk : k.val < 93) : S.R k = [] := by
    have hn (n : ℕ) (h : 93 ≤ n) : k.val ≠ n := by omega
    simp [S, unaryBatchBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 112 (by decide), hn 114 (by decide), hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]
  have hc : CClean mul S := by
    intro i
    refine ⟨rfl, hlow (mul i) ?_⟩
    have hi := i.isLt
    dsimp [mul]
    omega
  have hb : ∀ r, S.R (cr r) = [] := by
    intro r
    obtain ⟨_, hhi, h93, _⟩ := cr_range r
    have hn (n : ℕ) (h : 97 ≤ n) : (cr r).val ≠ n := by omega
    simp [S, unaryBatchBank, hn 101 (by decide), hn 102 (by decide), hn 103 (by decide),
      hn 97 (by decide), hn 98 (by decide), hn 99 (by decide), hn 100 (by decide), hn 109 (by decide),
      hn 112 (by decide), hn 114 (by decide), hn 116 (by decide), hn 110 (by decide), h93]
  obtain ⟨v', m, hu', hm, he⟩ := generatedBatchSetup_exec (body := body) (band := band) (l := l) (B := B)
    hQ hA lo hP hqMax hs hst hu hL hLs hlo v S rhs borrowed (List.replicate l tick)
    (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank])
    (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank])
    (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank]) (by simp [S, unaryBatchBank])
    (by simp [S, unaryBatchBank]) (by simp) (by simp [S, unaryBatchBank])
    (by simp [S, unaryBatchBank]) hrhs hc hb (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S, unaryBatchBank])
  exact ⟨v', m, hu', hm, he.cast rfl (congrArg (mk v')
    (generatedBatchBank_eq_inputSourceBank P N q l s t u band L B lo rhs borrowed outTail inp out))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
