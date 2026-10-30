module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponentsAccuracy

/-! Transfer complex packed-row accuracy to the physically published
ambient line, with the same error and original core coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloScatterRows_complex_errorOn {A s : ℕ} [NeZero s] (t band a b L q w : ℕ)
    (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (haloLengthGroup s t band a b L).length*(L*w) ≤ X.length)
    (x : ZMod s → ℂ) (error : ℝ)
    (hlocal : ∀ n : Fin (haloLengthGroup s t band a b L).length, ∀ i : Fin L,
      ‖value q (decodeWord ((X.drop ((n.val*L+i.val)*w)).take w)) -
        x (haloGroupOrigin s t band a b L n+(i.val : ZMod s))‖ ≤ error)
    (n : Fin (haloLengthGroup s t band a b L).length) :
    PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
      (pairedCellRead q w (scatterRows (L*w) E X (haloScatterGaps s t band a b L w))) x error := by
  let lo := haloGroupOrigin s t band a b L n
  have hfit : lo.val+L ≤ s := by
    dsimp only [lo]
    rw [haloGroupOrigin_val band a b L n]
    exact haloOrigins_fit s t band a b L _ (List.mem_map.mpr
      ⟨_,haloGroupPhase_mem s t band a b L n,rfl⟩)
  intro k hk
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
  have hiL : i < L := Finset.mem_range.mp hi
  have his : i < s := by omega
  have hsum : lo.val+i < s := by omega
  have hval : (lo+(i : ZMod s)).val = lo.val+i := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt his,Nat.mod_eq_of_lt hsum]
  change ‖pairedCellRead q w
    (scatterRows (L*w) E X (haloScatterGaps s t band a b L w)) (lo+(i : ZMod s)) - x (lo+(i : ZMod s))‖ ≤ error
  simp only [pairedCellRead,hval]
  rw [haloScatterRows_word t band a b L w E X hE hX n ⟨i,hiL⟩]
  exact hlocal n ⟨i,hiL⟩

/-- The existing forward sweep publishes complex results with unchanged error,
restored controls and borrowed suffixes, at the same linear cost. -/
theorem haloScatter_complex_accuracy_exec {T Q A s : ℕ} [NeZero s]
    {P U : Type} {body : P → Pr P T Q A U}
    {control savedControl gap window src dst acc trash tmp : Fin T}
    (hreg : [control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (t band a b L q w : ℕ) (hst : s < t) (hw1 : 1 ≤ w)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = s*w) (hys : ys.length = (haloLengthGroup s t band a b L).length*(L*w))
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (haloScatterGaps s t band a b L w))
    (hdst : S.R dst = E++outputTail) (hsrc : S.R src = ys++sourceTail)
    (hw : (S.R window).length = L*w)
    (hclean : ∀ k ∈ [savedControl,gap,acc,trash,tmp], S.R k = [])
    (x : ZMod s → ℂ) (error : ℝ)
    (hlocal : ∀ n : Fin (haloLengthGroup s t band a b L).length, ∀ i : Fin L,
      ‖value q (decodeWord (((ys++sourceTail).drop ((n.val*L+i.val)*w)).take w)) -
        x (haloGroupOrigin s t band a b L n+(i.val : ZMod s))‖ ≤ error) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 35*s*w+6 ∧
      Exec body (scatterBatch control savedControl gap window src dst acc trash tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail))}) ∧
      ∀ k : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L k) L)
          (pairedCellRead q w
            (scatterRows (L*w) E (ys++sourceTail) (haloScatterGaps s t band a b L w)++outputTail)) x error := by
  obtain ⟨v',hu,he⟩ := haloScatter_exec (body := body) hreg s t band a b L w E ys sourceTail
    outputTail hE hys v S hc hdst hsrc hw hclean
  refine ⟨v',haloScatterCost s t band a b L w,hu,haloScatterCost_le hst band a b L w hw1,he,?_⟩
  have hf := haloScatterGaps_fits s t band a b L w E (by omega)
  have hgood := haloScatterRows_complex_errorOn t band a b L q w (E++outputTail) (ys++sourceTail)
    (by simp only [List.length_append]; omega)
    (by simp only [List.length_append,hys]; omega) x error hlocal
  simpa only [scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E
    (ys++sourceTail) outputTail hf] using hgood

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
