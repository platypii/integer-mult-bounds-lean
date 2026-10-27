module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetPowerWord

/-! Generate the encoded Newton starting value from retained precision and generated word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorSeed : Pr P 224 Q A U :=
  .seq (copyR 160 218 184 (fun _ => pairSym A false false))
    (.seq (ucopy 119 223 0) (.seq (.act (dropTop 223 (dropTop 223 .done)))
      (.seq (setPowerWord 223 218 221 184 0) (uclear 223))))

def boundaryFactorSeedCost (q : ℕ) : ℕ :=
  (4*(2*q+8)+4)+((4*q+4)+(1+((8*(q-2)+9)+(2*(q-2)+2))))

theorem boundaryFactorSeed_exec (q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (hw : (S.R 160).length = 2*q+8)
    (h0 : S.R 0 = []) (h184 : S.R 184 = []) (h218 : S.R 218 = [])
    (h221 : S.R 221 = []) (h223 : S.R 223 = []) :
    ∃ v', v'.user = v.user ∧ Exec body boundaryFactorSeed (mk v S) (boundaryFactorSeedCost q)
      (mk v' {S with R := Function.update S.R 218 (csyms A (2*q+8) (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt))}) := by
  let w := 2*q+8
  let e := q-2
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body 160 218 184 (by decide) (by decide) (by decide)
    (fun _ => pairSym A false false) v S h184
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 218 (csyms A w 0)}
  have he₁' : Exec body (copyR 160 218 184 (fun _ => pairSym A false false)) (mk v S) (4*w+4) (mk v₁ S₁) := by
    simpa [S₁,w,csyms_zero,hw,h218] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 119) (b := 223) (t := 0) (by decide) (by decide) (by decide)
    v₁ S₁ (by simpa [S₁] using h0)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 223 (List.replicate q tick)}
  have he₂' : Exec body (ucopy 119 223 0) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hq,h223] using he₂
  let S₃ : Stacks 224 A := {S₁ with R := Function.update S₁.R 223 (List.replicate e tick)}
  have he₃ : Exec body (.act (dropTop 223 (dropTop 223 .done))) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    simpa [S₃,S₂,e,dropTop,Action.run,update_rt,Nat.sub_sub] using
      Exec.act (body := body) (dropTop 223 (dropTop 223 .done)) (mk v₂ S₂)
  obtain ⟨v₄,hu₄,he₄⟩ := setPowerWord_exec (body := body)
    (show [(223 : Fin 224),218,221,184,0].Nodup by decide) w e (by dsimp [e,w]; omega) [] v₂ S₃
    (by simp [S₃]) (by simp [S₃,S₁])
    (by simpa [S₃,S₁] using h221) (by simpa [S₃,S₁] using h184) (by simpa [S₃,S₁] using h0)
  let output := csyms A w (⟨(2 : ℤ)^e,0⟩ : GaussianInt)
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 218 output}
  have he₄' : Exec body (setPowerWord 223 218 221 184 0) (mk v₂ S₃) (8*e+9) (mk v₄ S₄) := by
    simpa [S₄,output] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 223 v₄ S₄
  have hlen : (S₄.R 223).length = e := by simp [S₄,S₃]
  refine ⟨v₅,hu₅.trans (hu₄.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' he₅)))).cast (by rw [hlen]; rfl) ?_⟩
  apply congrArg (mk v₅)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi223 : i = 223 <;> by_cases hi218 : i = 218 <;> simp [S₄,S₃,S₁,output,w,e,hi223,hi218,h223]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
