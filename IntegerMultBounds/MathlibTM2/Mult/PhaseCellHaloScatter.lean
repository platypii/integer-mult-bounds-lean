module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterBatch
public import IntegerMultBounds.NLogN.PhaseCellHaloGroupVolume

/-! Execute natural-group publication from its delimited gap stream. The
solver output prefix is consumed, the borrowed suffix restored, and ambient
output outside the selected windows remains available for the next class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def haloScatterCost (s t band a b L w : ℕ) : ℕ :=
  (haloLengthGroup s t band a b L).length*(12*(L*w)+23)+
    12*(haloScatterGaps s t band a b L w).sum+6

theorem haloScatterCost_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ) (hw : 1 ≤ w) :
    haloScatterCost s t band a b L w ≤ 35*s*w+6 := by
  let B := (haloLengthGroup s t band a b L).length
  have hvol := haloScatterGaps_volume s t band a b L w
  simp only [scatterVolume,haloScatterGaps_length] at hvol
  have hBs : B ≤ s := by
    by_cases hB : B = 0
    · simp [hB]
    have hL : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
      (haloGroupPhase_mem s t band a b L ⟨0,by omega⟩)).2.1
    have hh : B*L ≤ s := haloGroup_volume_le hst band a b L
    nlinarith only [hh,hL]
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  dsimp only [haloScatterCost]
  dsimp only [B] at hBs
  nlinarith only [hvol,hBs,hsw]

theorem haloScatter_exec {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (s t band a b L w : ℕ) (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (haloLengthGroup s t band a b L).length*(L*w))
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R dst = E++outputTail) (hsrc : S.R src = ys++sourceTail)
    (hw : (S.R window).length = L*w)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S)
        (haloScatterCost s t band a b L w)
        (mk v' { S with R := (Function.update (Function.update S.R src sourceTail)
          dst (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail)) }) := by
  have hf := haloScatterGaps_fits s t band a b L w E (by omega)
  have hf' := haloScatterGaps_fits s t band a b L w (E++outputTail) (by simp only [List.length_append]; omega)
  obtain ⟨v',hu,he⟩ := scatterBatch_exec (body := body) hreg (L*w) (haloScatterGaps s t band a b L w)
    (E++outputTail) (ys++sourceTail) hf' (by simp [List.length_append,hys]) v S hc hdst hsrc hw hclean
  refine ⟨v',hu,?_⟩
  simpa only [haloScatterGaps_length,← hys,List.drop_append_length,
    haloScatterCost,scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E (ys++sourceTail) outputTail hf] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
