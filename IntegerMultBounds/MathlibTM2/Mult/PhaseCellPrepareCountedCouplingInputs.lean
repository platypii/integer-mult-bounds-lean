module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine

/-! Prepare the row count and aligned input window independently of the coefficient supplier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareCountedCouplingInputs : Pr P₀ 117 Q A U :=
  .seq (.act (.push (.rt 102) (fun _ => tick) .done))
    (.seq (umul 2 100 102 109) (copyCountedLine 102 94 92 110 109 104 105))

def prepareCountedCouplingInputsCost (band w : ℕ) : ℕ :=
  4*band+5+copyCountedLineCost (2*band+1) w

theorem prepareCountedCouplingInputs_exec (band w : ℕ) (xs tail : List (Fin (A+4)))
    (hlen : xs.length = (2*band+1)*w) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hb : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 92 = xs++tail) (h102 : S.R 102 = [])
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCountedCouplingInputsCost band w ∧
      Exec body prepareCountedCouplingInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 102
          (List.replicate (2*band+1) tick)) 110 (xs++S.R 110))}) := by
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 102 [tick]}
  have he₁ : Exec body (.act (.push (.rt 102) (fun _ => tick) .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,h102,Action.run,update_rt] using
      Exec.act (body := body) (.push (.rt 102) (fun _ => tick) .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := umul_exec (body := body) 2 (a := 100) (b := 102) (t := 109)
    (by decide) (by decide) (by decide) v S₁ (by simpa [S₁] using h109)
  let S₂ : Stacks 117 A := {S with R := Function.update S.R 102 (List.replicate (2*band+1) tick)}
  have he₂' : Exec body (umul 2 100 102 109) (mk v S₁) (4*band+4) (mk v₂ S₂) := by
    convert he₂ using 1 <;> simp [S₂,S₁,hb,List.replicate_add]
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := copyCountedLine_exec (body := body)
    102 94 92 110 109 104 105 (by decide) (2*band+1) w xs tail hlen v₂ S₂
    (by simp [S₂]) (by simpa [S₂] using hw) (by simpa [S₂] using hsrc)
    (by simpa [S₂] using h109) (by simpa [S₂] using h104) (by simpa [S₂] using h105)
  exact ⟨v₃,1+((4*band+4)+m₃),hu₃.trans hu₂,
    by dsimp [prepareCountedCouplingInputsCost]; omega,Exec.seq he₁ (Exec.seq he₂' he₃)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
