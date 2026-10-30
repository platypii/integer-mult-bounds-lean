module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketWidthControls
public import IntegerMultBounds.MathlibTM2.Mult.ChirpScaleExec

/-! Width and scale conversion on the packed numerical bank, with no ambient scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedScalePackets (width shift rest src buf savedShift savedRest : Fin T) : Pr P T Q A U :=
  withWidthDifference width shift rest savedRest
    (shiftInto src buf src shift rest savedShift savedRest (pairSym A false false))

/-- Generate the remaining word width and scale only the owned local stream.
The shift header is borrowed; the rest counter is generated and cleared. -/
theorem generatedScalePackets_exec {width shift rest src buf savedShift savedRest : Fin T}
    (hreg : [width,shift,rest,src,buf,savedShift,savedRest].Nodup)
    (w d : ℕ) (hw : 1 ≤ w) (hd : d ≤ w) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = w) (hshift : (S.R shift).length = d)
    (hsrc : S.R src = cstream A w xs) (hrest : S.R rest = []) (hbuf : S.R buf = [])
    (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (generatedScalePackets width shift rest src buf savedShift savedRest) (mk v S)
        (4*w+4*d+2*(w-d)+(xs.length*(6*w+4*d+14)+4)+10)
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z))))}) := by
  have hr := hreg
  regs_ne hr
  apply withWidthDifference_exec (body := body) (by regs_nodup)
    _ w d _ _ S hwidth hshift hrest hsavedRest ?_ v
  intro v₀
  apply chirpScale_exec (body := body) (by regs_nodup) w d hw hd xs v₀
  · simpa [‹rest ≠ src›.symm] using hsrc
  · simpa [‹shift ≠ rest›] using hshift
  · simp
  · simpa [‹rest ≠ buf›.symm] using hbuf
  · simpa [‹rest ≠ savedShift›.symm] using hsavedShift
  · simpa [‹rest ≠ savedRest›.symm] using hsavedRest

def packedInputConversionCost (W w d N : ℕ) : ℕ :=
  (4*W+4*w+2*(W-w)+(N*(4*W+2*w+14)+4)+10)+
    (4*w+4*d+2*(w-d)+(N*(6*w+4*d+14)+4)+10)

def packedInputConversion (commonWidth width shift src buf zero extra savedShift savedRest : Fin T) : Pr P T Q A U :=
  .seq (generatedNarrowPackets commonWidth width src buf zero extra savedRest)
    (generatedScalePackets width shift extra src buf savedShift savedRest)

/-- Isolated packed halos can be converted on any numerical bank. The bill
uses the actual local coefficient count; no ambient line is read or supplied. -/
theorem packedInputConversion_exec {commonWidth width shift src buf zero extra savedShift savedRest : Fin T}
    (hreg : [commonWidth,width,shift,src,buf,zero,extra,savedShift,savedRest].Nodup)
    (W w d : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W) (hd : d ≤ w)
    (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hcommon : (S.R commonWidth).length = W) (hword : (S.R width).length = w)
    (hshift : (S.R shift).length = d) (hsrc : S.R src = cstream A W xs)
    (hbuf : S.R buf = []) (hzero : S.R zero = []) (hextra : S.R extra = [])
    (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packedInputConversion commonWidth width shift src buf zero extra savedShift savedRest) (mk v S)
        (packedInputConversionCost W w d xs.length)
        (mk v' {S with R := (Function.update S.R src
          (cstream A w (xs.map (fun z => (2 : GaussianInt)^d*z))))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := generatedNarrowPackets_exec (body := body) (by regs_nodup)
    W w (hw.trans hwidth) hwidth xs v S hcommon hword hsrc hbuf hzero hextra hsavedRest
  let M : Stacks T A := {S with R := Function.update S.R src (cstream A w xs)}
  obtain ⟨v₂,hu₂,he₂⟩ := generatedScalePackets_exec (body := body) (width := width) (shift := shift) (rest := extra)
    (src := src) (buf := buf) (savedShift := savedShift) (savedRest := savedRest) (by regs_nodup)
    w d hw hd xs v₁ M
    (by simpa [M,‹width ≠ src›] using hword)
    (by simpa [M,‹shift ≠ src›] using hshift) (by simp [M])
    (by simpa [M,‹src ≠ extra›.symm] using hextra)
    (by simpa [M,‹src ≠ buf›.symm] using hbuf)
    (by simpa [M,‹src ≠ savedShift›.symm] using hsavedShift)
    (by simpa [M,‹src ≠ savedRest›.symm] using hsavedRest)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  simp [M]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
