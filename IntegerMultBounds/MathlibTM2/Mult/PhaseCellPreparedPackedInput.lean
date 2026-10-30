module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInputConversion
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInputShiftHeader

/-! The packed numerical entry derives its scale shift and restores all work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparedPackedInput (precision inputPrecision commonWidth width shift src buf zero extra savedShift savedRest : Fin T) : Pr P T Q A U :=
  .seq (packedInputShiftHeader precision inputPrecision shift savedShift)
    (.seq (packedInputConversion commonWidth width shift src buf zero extra savedShift savedRest) (uclear shift))

/-- Convert an isolated local batch using retained numerical/input precisions.
No scalar table, ambient source, supplied shift or supplied rest counter is
needed; only the local source changes. -/
theorem preparedPackedInput_exec {precision inputPrecision commonWidth width shift src buf zero extra savedShift savedRest : Fin T}
    (hreg : [precision,inputPrecision,commonWidth,width,shift,src,buf,zero,extra,savedShift,savedRest].Nodup)
    (p q W : ℕ) (hp : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R precision).length = q) (hpHeader : (S.R inputPrecision).length = p)
    (hcommon : (S.R commonWidth).length = W) (hword : (S.R width).length = 2*q+8)
    (hsrc : S.R src = cstream A W xs) (hshift : S.R shift = [])
    (hbuf : S.R buf = []) (hzero : S.R zero = []) (hextra : S.R extra = [])
    (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (preparedPackedInput precision inputPrecision commonWidth width shift src buf zero extra savedShift savedRest)
        (mk v S) ((4*q+4*p+9)+packedInputConversionCost W (2*q+8) (q-p-1) xs.length+(2*(q-p-1)+2))
        (mk v' {S with R := (Function.update S.R src
          (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z))))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := packedInputShiftHeader_exec (body := body)
    (show [precision,inputPrecision,shift,savedShift].Nodup by regs_nodup)
    q p v S hq hpHeader hshift hsavedShift
  let M : Stacks T A := {S with R := Function.update S.R shift (List.replicate (q-p-1) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := packedInputConversion_exec (body := body)
    (show [commonWidth,width,shift,src,buf,zero,extra,savedShift,savedRest].Nodup by regs_nodup)
    W (2*q+8) (q-p-1) (by omega) hW (by omega) xs v₁ M
    (by simpa [M,‹commonWidth ≠ shift›] using hcommon)
    (by simpa [M,‹width ≠ shift›] using hword) (by simp [M])
    (by simpa [M,‹shift ≠ src›.symm] using hsrc)
    (by simpa [M,‹shift ≠ buf›.symm] using hbuf)
    (by simpa [M,‹shift ≠ zero›.symm] using hzero)
    (by simpa [M,‹shift ≠ extra›.symm] using hextra)
    (by simpa [M,‹shift ≠ savedShift›.symm] using hsavedShift)
    (by simpa [M,‹shift ≠ savedRest›.symm] using hsavedRest)
  let F : Stacks T A := {M with R := (Function.update M.R src
    (cstream A (2*q+8) (xs.map (fun z => (2 : GaussianInt)^(q-p-1)*z))))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) shift v₂ F
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [F,M,‹shift ≠ src›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [F,M,‹shift ≠ src›.symm]
    by_cases hishift : i = shift
    · subst i; simp [F,M,‹shift ≠ src›,hshift]
    · simp [F,M,his,hishift]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
