module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScatterData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterBatch

/-! Execute sparse boundary publication with borrowed source and output suffixes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem boundaryScatter_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (boundaryScatterGaps s B w))
    (hdst : S.R dst = cstream A w (List.replicate s 0)++outputTail)
    (hsrc : S.R src = cstream A w ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map G)++sourceTail)
    (hwidth : (S.R window).length = w)
    (hclean : ∀ i ∈ [savedControl,gap,acc,trash,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 35*s*w+6 ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (cstream A w (chirpLine s G)++outputTail))}) := by
  let E := cstream A w (List.replicate s (0 : GaussianInt))
  let X := cstream A w ((IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder s B).map G)
  let ds := boundaryScatterGaps s B w
  have hE : E.length = s*w := by simp [E]
  have hX : X.length = B.card*w := by simp [X,IntegerMultBounds.NLogN.PhaseCellMatrix.bOrder_length]
  have hf : ScatterFits w E ds := boundaryScatterGaps_fits s B w E (by rw [hE])
  have hf' : ScatterFits w (E++outputTail) ds := boundaryScatterGaps_fits s B w _ (by simp [hE])
  obtain ⟨v',hu,he⟩ := scatterBatch_exec (body := body) hreg w ds (E++outputTail) (X++sourceTail) hf'
    (by simp [ds,hX]) v S hc hdst hsrc hwidth hclean
  refine ⟨v',_,hu,boundaryScatterCost_le s B w hw,he.cast (by simp [ds]) ?_⟩
  have hsource : (X++sourceTail).drop (ds.length*w) = sourceTail := by simp [ds,hX]
  have hdest : scatterRows w (E++outputTail) (X++sourceTail) ds =
      cstream A w (chirpLine s G)++outputTail := by
    rw [scatterRows_append w ds E (X++sourceTail) outputTail hf,
      scatterRows_source_suffix w E X sourceTail ds (by simp [ds,hX])]
    rw [boundary_scatter_cstream s B A w G hoff]
  rw [hsource,hdest]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
