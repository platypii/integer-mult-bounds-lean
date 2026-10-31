module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter

/-! The publication executor is independent of the construction of its cores.
The source suffix and ambient suffix are borrowed and restored exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem windowScatter_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (windows : PublicationWindows s L) (w : ℕ)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = windows.origins.length*(L*w))
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (windows.gaps w))
    (hdst : S.R dst = E++outputTail) (hsrc : S.R src = ys++sourceTail)
    (hw : (S.R window).length = L*w)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S)
        (windows.cost w)
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (scatterRows (L*w) E ys (windows.gaps w)++outputTail))}) := by
  have hf := windows.gaps_fits w E (by omega)
  have hf' := windows.gaps_fits w (E++outputTail) (by simp only [List.length_append]; omega)
  obtain ⟨v',hu,he⟩ := scatterBatch_exec (body := body) hreg (L*w) (windows.gaps w)
    (E++outputTail) (ys++sourceTail) hf' (by simp [List.length_append,hys]) v S hc hdst hsrc hw hclean
  have hsuffix : scatterRows (L*w) E (ys++sourceTail) (windows.gaps w) =
      scatterRows (L*w) E ys (windows.gaps w) := by
    apply scatterRows_source_suffix
    rw [windows.gaps_length,hys]
  refine ⟨v',hu,?_⟩
  simpa only [PublicationWindows.gaps_length,← hys,List.drop_append_length,
    PublicationWindows.cost,scatterRows_append (L*w) (windows.gaps w) E (ys++sourceTail) outputTail hf,
    hsuffix] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
