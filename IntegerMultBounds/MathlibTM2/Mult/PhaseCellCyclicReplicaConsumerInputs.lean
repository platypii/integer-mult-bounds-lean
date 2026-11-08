module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaConsumerHandoff
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportCyclicResidualRows

/-! Export readiness uses retained masters and preserves the already generated
masks. Only ordinary geometry and blank workspace are required from the bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement

private theorem consumerRows_read {A : ℕ} (S : Stacks 834 A) (r : Fin 180)
    (hr : r ∉ [(130 : Fin 180),168,169,171,172,179]) :
    (embStk cyclicResidualRowsReg (embStk factorReg (cyclicReplicaConsumerState S))).R r =
      S.R (factorReg (cyclicResidualRowsReg r)) := by
  apply cyclicReplicaConsumerState_factor_read
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr ⊢
  have hval : ∀ k : Fin 180, r ≠ k → r.val ≠ k.val :=
    fun k hk he => hk (Fin.ext he)
  have h130 := hval 130 hr.1
  have h168 := hval 168 hr.2.1
  have h169 := hval 169 hr.2.2.1
  have h171 := hval 171 hr.2.2.2.1
  have h172 := hval 172 hr.2.2.2.2.1
  have h179 := hr.2.2.2.2.2
  simp only [cyclicResidualRowsReg,ite_eq_right h179]
  split_ifs <;> simp_all only [ne_eq,Fin.ext_iff] <;> omega

theorem CyclicReplicaConsumerPost.exportInputs {s : ℕ} [NeZero s] {A : ℕ}
    (H K : ReplicaHaloProblem s) (leftBuffers rightBuffers : ReplicaLoopBuffers A)
    (S : Stacks 834 A) (Cs Ds : List (ZMod s → GaussianInt))
    (post : CyclicReplicaConsumerPost H K leftBuffers rightBuffers S
      (cyclicReplicaConsumerState S) Cs Ds)
    (t band a n : ℕ) (hspanL : H.span = min n (s-a))
    (hspanR : K.span = n-min n (s-a)) (hw : K.wordWidth = H.wordWidth)
    (hleft : S.R (factorReg 170) = couplingSourceIntervalMaskSymbols true A s t band
      a (a+min n (s-a)) a (min n (s-a)))
    (hright : S.R (factorReg 173) = couplingSourceIntervalMaskSymbols true A s t band
      0 (n-min n (s-a)) 0 (n-min n (s-a)))
    (hcount : (S.R (factorReg 116)).length = (cyclicPrincipalBoundary s t band a n).card)
    (hblank : ∀ r : Fin 180, 6 ≤ r.val → r.val < 80 →
      S.R (factorReg (cyclicResidualRowsReg r)) = [])
    (hfresh : ∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175],
      S.R (factorReg (cyclicResidualRowsReg r)) = []) :
    CyclicReplicaBoundaryInputs (s := s) t band a n H.wordWidth
      (embStk cyclicResidualRowsReg (embStk factorReg (cyclicReplicaConsumerState S))) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [embStk,cyclicResidualRowsReg,hspanL] using congrArg List.length post.leftVolume
  · simpa [embStk,cyclicResidualRowsReg,hspanR,hw] using congrArg List.length post.rightVolume
  · rw [consumerRows_read S 170 (by decide)]
    simpa [cyclicResidualRowsReg] using hleft
  · rw [consumerRows_read S 173 (by decide)]
    simpa [cyclicResidualRowsReg] using hright
  · simpa [embStk,cyclicResidualRowsReg] using congrArg List.length post.width
  · rw [consumerRows_read S 116 (by decide)]
    simpa [cyclicResidualRowsReg] using hcount
  · intro r hr6 hr80
    have hoff : r ∉ [(130 : Fin 180),168,169,171,172,179] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      repeat' constructor
      all_goals intro he; have hv := congrArg Fin.val he; simp at hv; omega
    rw [consumerRows_read S r hoff]
    exact hblank r hr6 hr80
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [consumerRows_read S _ (by decide)]; exact hfresh _ (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
