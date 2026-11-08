module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualBatchInput

/-! Residual packets and their replica counter may be installed without changing
the ordinary factor factory's geometry, arithmetic, or workspace prerequisites. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem CyclicResidualBatchInput.of_packet_frame
    {A p l s t u target a n : ℕ} [NeZero s]
    {tail pageTail : List (Fin (A+4))} {S F : Stacks 234 A}
    (h : CyclicResidualBatchInput p l s t u target a n tail pageTail S)
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hL : F.L = S.L)
    (hR : ∀ k : Fin 234, k ≠ 226 → k ≠ 229 → F.R k = S.R k) :
    CyclicResidualBatchInput p l s t u target a n tail pageTail F := by
  have hsmall (k : Fin 234) (hk : k.val < 226) : F.R k = S.R k := by
    apply hR k <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega
  have hcore : embStk preparedBoundaryBatchCoreReg F = embStk preparedBoundaryBatchCoreReg S := by
    refine Stacks.ext hin hout ?_ ?_
    · funext i; exact congrFun hL (preparedBoundaryBatchCoreReg i)
    · funext i; exact hsmall _ i.isLt
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsmall 116 (by decide)]; exact h.rows
  · rw [hsmall 115 (by decide)]; exact h.pageWidth
  · rw [hsmall 109 (by decide)]; exact h.page
  · simpa only [hcore] using h.arithmetic
  · rw [hsmall 144 (by decide)]; exact h.origin
  · rw [hsmall 145 (by decide)]; exact h.leftEnd
  · rw [hsmall 146 (by decide)]; exact h.rightEnd
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hsmall _ (by decide)]; exact h.fresh _ (by simp)
  · intro i; rw [hL]; exact h.left i
  · intro i hi
    rw [hsmall _ (by change i.val < 226; omega)]
    exact h.new i hi
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hR _ (by decide) (by decide)]; exact h.privateFresh _ (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
