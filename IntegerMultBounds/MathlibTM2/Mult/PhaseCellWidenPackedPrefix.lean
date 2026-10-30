module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransformPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls

/-! Publish one local key at the router's common word width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def widenPackedPrefix (wide width count src work saved tmp extra : Fin T) : Pr P T Q A U :=
  transformPrefix count src work saved tmp (generatedWidenPackets wide width work saved extra tmp)

def widenPackedPrefixCost (w W coefficients : ℕ) : ℕ :=
  4*W+4*w+2*(W-w)+24+coefficients*(6*w+10*W+10)

/-- Sign extension preserves the coefficient list. Only the counted key enters
the common-width pass; later keys and retained dimension symbols restore. -/
theorem widenPackedPrefix_exec {wide width count src work saved tmp extra : Fin T}
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (xs : List GaussianInt) (hfit : ∀ z ∈ xs, TopFitsZ w z)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hcount : (S.R count).length = xs.length*w)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenPackedPrefixCost w W xs.length ∧
      Exec body (widenPackedPrefix wide width count src work saved tmp extra) (mk v S) n
        (mk v' {S with R := Function.update S.R src (cstream A W xs++tail)}) := by
  have hr := hreg
  regs_ne hr
  let X := cstream A w xs
  let Y := cstream A W xs
  let S₂ := isolatedPrefixState S src work saved X tail
  have hrun : ∀ v₂ : HS T Q A U, ∃ v₃ n₃, v₃.user = v₂.user ∧
      n₃ ≤ 4*W+4*w+2*(W-w)+(xs.length*(6*W+10)+4)+10 ∧
      Exec body (generatedWidenPackets wide width work saved extra tmp) (mk v₂ S₂) n₃
        (mk v₃ {S₂ with R := Function.update S₂.R work Y}) := by
    intro v₂
    obtain ⟨v₃,hu₃,he₃⟩ := generatedWidenPackets_exec (body := body)
      (show [wide,width,work,saved,extra,tmp].Nodup by regs_nodup) w W hw hwidth xs hfit v₂ S₂
      (by simpa [S₂,isolatedPrefixState, *, Ne.symm] using hwide)
      (by simpa [S₂,isolatedPrefixState, *, Ne.symm] using hword)
      (by simp [S₂,isolatedPrefixState,X])
      (by simp [S₂,isolatedPrefixState, *, Ne.symm])
      (by simp [S₂,isolatedPrefixState, *, Ne.symm])
      (by simp [S₂,isolatedPrefixState, *, Ne.symm])
    exact ⟨v₃,_,hu₃,le_rfl,he₃⟩
  obtain ⟨v',n,hu,hn,he⟩ := transformPrefix_exec (body := body)
    (show [count,src,work,saved,tmp].Nodup by regs_nodup) _ X Y tail _ v S hsrc
    (by simpa [X] using hcount) (hblank work (by simp)) (hblank saved (by simp))
    (hblank tmp (by simp)) hrun
  refine ⟨v',n,hu,?_,he⟩
  simp only [X,Y,length_cstream] at hn
  unfold widenPackedPrefixCost
  nlinarith only [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
