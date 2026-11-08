module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Construct a private replica clock and one-window byte ruler from retained
ordinary dimensions. No archive is counted and all borrowed rulers restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def bulkSelectionCounts (replicas span wide clock volume saved tmp : Fin T) : Pr P T Q A U :=
  .seq (ucopy replicas clock tmp) (unaryProduct span wide volume saved tmp)

def bulkSelectionCountsCost (N H W : ℕ) : ℕ := (4*N+4)+(H*(4*W+9)+4)

theorem bulkSelectionCounts_native (replicas span wide clock volume saved tmp : Fin T) :
    mnNativePushBound 2 (bulkSelectionCounts (P := P) (Q := Q) (A := A) (U := U)
      replicas span wide clock volume saved tmp) := by
  refine ⟨?_,unaryProduct_native ..⟩
  simp [ucopy,umulSym,scanR,drainR,keepIn,pushN,moveR,moveStep,whileR,popDo,peekR,
    mnNativePushBound,mnActPush]

theorem bulkSelectionCounts_exec (replicas span wide clock volume saved tmp : Fin T)
    (hreg : [replicas,span,wide,clock,volume,saved,tmp].Nodup)
    (N H W : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R replicas).length = N) (hH : (S.R span).length = H) (hW : (S.R wide).length = W)
    (hblank : ∀ k ∈ [clock,volume,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ bulkSelectionCountsCost N H W ∧
      Exec body (bulkSelectionCounts replicas span wide clock volume saved tmp) (Host.mk v S) m
        (Host.mk v' {S with R := (Function.update (Function.update S.R clock (List.replicate N tick))
          volume (List.replicate (H*W) tick))}) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        2*bulkSelectionCountsCost N H W) depth
        (bulkSelectionCounts replicas span wide clock volume saved tmp) (Host.mk v S) m
        (Host.mk v' {S with R := (Function.update (Function.update S.R clock (List.replicate N tick))
          volume (List.replicate (H*W) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) ‹replicas ≠ clock› ‹replicas ≠ tmp› ‹clock ≠ tmp›
    v S (hblank tmp (by simp))
  let F : Stacks T A := {S with R := Function.update S.R clock (List.replicate N tick)}
  have he₁' : Exec body (ucopy replicas clock tmp) (Host.mk v S) (4*N+4) (Host.mk v₁ F) := by
    simpa only [hN,hblank clock (by simp),List.append_nil,F] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryProduct_exec (body := body)
    (by regs_nodup : [span,wide,volume,saved,tmp].Nodup) v₁ F
    (by simpa [F,‹clock ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [F,‹clock ≠ tmp›.symm] using hblank tmp (by simp))
  have hm₂' : m₂ ≤ H*(4*W+9)+4 := by
    simpa only [F,Function.update_of_ne ‹span ≠ clock›,Function.update_of_ne ‹wide ≠ clock›,hH,hW] using hm₂
  have he₂' : Exec body (unaryProduct span wide volume saved tmp) (Host.mk v₁ F) m₂
      (Host.mk v₂ {F with R := Function.update F.R volume (List.replicate (H*W) tick)}) := by
    simpa only [F,Function.update_of_ne ‹span ≠ clock›,Function.update_of_ne ‹wide ≠ clock›,
      Function.update_of_ne ‹clock ≠ volume›.symm,hH,hW,hblank volume (by simp),List.append_nil] using he₂
  have hex := Exec.seq he₁' he₂'
  have hm : (4*N+4)+m₂ ≤ bulkSelectionCountsCost N H W := by unfold bulkSelectionCountsCost; omega
  refine ⟨v₂,_,hu₂.trans hu₁,hm,hex,fun depth => ?_⟩
  exact mn_native_exec_within hex 2 (bulkSelectionCounts_native ..) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
