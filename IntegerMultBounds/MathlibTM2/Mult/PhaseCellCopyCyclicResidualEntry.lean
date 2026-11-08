module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualIndex
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyIndexedWord
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! Restoring access to the selected row in the two executed residual streams. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem copyCyclicResidualEntry_exec {index width src dst skip savedSkip saved tmp work₁ work₂ : Fin T}
    (hreg : [index,width,src,dst,skip,savedSkip,saved,tmp,work₁,work₂].Nodup)
    {s : ℕ} [NeZero s] (w a b : ℕ) (i : ZMod s) (C D : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hindex : (S.R index).length = cyclicResidualIndex s a b i.val)
    (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A w (chirpLine s D)++(cstream A w (chirpLine s C)++tail))
    (hfresh : ∀ r ∈ [skip,savedSkip,saved,tmp,work₁,work₂], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicResidualIndex s a b i.val*(12*w+9)+10*w+22 ∧
      Exec body (copyIndexedWord index width src dst skip savedSkip saved tmp work₁ work₂) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (csyms A w (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R dst))}) := by
  have hlen : cyclicResidualIndex s a b i.val < (chirpLine s D++chirpLine s C).length := by
    simpa [chirpLine] using cyclicResidualIndex_lt (a := a) (b := b) i.val_lt
  obtain ⟨v',m,huser,hm,hex⟩ := copyIndexedWord_exec (body := body) hreg w
    (cyclicResidualIndex s a b i.val) (chirpLine s D++chirpLine s C) hlen tail v S hindex hwidth
    (by simpa only [cstream_append,List.append_assoc] using hsrc) hfresh
  have hword : (chirpLine s D++chirpLine s C)[cyclicResidualIndex s a b i.val] =
      if a ≤ i.val ∧ i.val < b then C i else D i := by
    have hh := getElem_cyclicResidualIndex (chirpLine s D) (chirpLine s C) s a b i.val
      (by simp [chirpLine]) (by simp [chirpLine]) i.val_lt
    simpa [chirpLine] using hh
  exact ⟨v',m,huser,hm,by simpa only [hword] using hex⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
