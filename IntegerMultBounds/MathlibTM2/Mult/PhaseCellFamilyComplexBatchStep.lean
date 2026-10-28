module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexComponent
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Park one cached complex solve while retaining its coefficient key and the shared factor page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 263 Q A U}

def familyComplexBatchNext {A : ℕ} (S : Stacks 263 A)
    (input output tail : List (Fin (A+4))) : Stacks 263 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 110 tail)
    241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}

def familyComplexBatchPark : Pr P 263 Q A U :=
  .seq (transfer 243 110 241 244) (transfer 243 132 242 244)

theorem familyComplexBatchPark_exec (v : HS 263 Q A U) (S : Stacks 263 A)
    (input output inputTail page : List (Fin (A+4)))
    (hinput : S.R 110 = input++inputTail) (houtput : S.R 132 = output++page)
    (hclock : (S.R 243).length = input.length) (hlen : output.length = input.length)
    (htmp : S.R 244 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body familyComplexBatchPark (mk v S) (8*input.length+8)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 inputTail) 241 (input.reverse++S.R 241)) 132 page) 242 (output.reverse++S.R 242))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := 243) (src := 110)
    (dst := 241) (tmp := 244) (by decide) v S input inputTail hinput hclock htmp
  let S₁ : Stacks 263 A := {S with R := (Function.update (Function.update S.R
    110 inputTail) 241 (input.reverse++S.R 241))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 243) (src := 132)
    (dst := 242) (tmp := 244) (by decide) v₁ S₁ output page
    (by simpa [S₁] using houtput) (by simpa [S₁,hlen] using hclock) (by simpa [S₁] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  have he := Exec.seq he₁ he₂
  have hcost : 8*input.length+8 = (4*input.length+4)+(4*output.length+4) := by rw [hlen]; omega
  rw [hcost]
  exact he

noncomputable def familyComplexBatchStep (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (familyComplexComponent recovery hR hQ) familyComplexBatchPark

theorem familyComplexBatchStep_of_exec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (v : HS 263 Q A U) (S : Stacks 263 A) (v₁ : HS 263 Q A U) (n : ℕ)
    (input output inputTail : List (Fin (A+4)))
    (hinput : S.R 110 = input++inputTail)
    (hclock : (S.R 243).length = input.length) (hlen : output.length = input.length)
    (htmp : S.R 244 = []) (hu : v₁.user = v.user)
    (he : Exec body (familyComplexComponent recovery hR hQ) (mk v S) n
      (mk v₁ {S with R := Function.update S.R 132 (output++S.R 132)})) :
    ∃ v', v'.user = v.user ∧
      Exec body (familyComplexBatchStep recovery hR hQ) (mk v S) (n+(8*input.length+8))
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          110 inputTail) 241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}) := by
  let M : Stacks 263 A := {S with R := Function.update S.R 132 (output++S.R 132)}
  obtain ⟨v₂,hu₂,he₂⟩ := familyComplexBatchPark_exec (body := body) v₁ M
    input output inputTail (S.R 132) (by simpa [M] using hinput)
    (by simp [M]) (by simpa [M] using hclock) hlen (by simpa [M] using htmp)
  refine ⟨v₂,hu₂.trans hu,?_⟩
  have hframe :
      {M with R := (Function.update (Function.update (Function.update (Function.update M.R
        110 inputTail) 241 (input.reverse++M.R 241)) 132 (S.R 132))
          242 (output.reverse++M.R 242))} =
      {S with R := (Function.update (Function.update (Function.update S.R
        110 inputTail) 241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h110 : i = 110 <;> by_cases h132 : i = 132 <;>
      by_cases h241 : i = 241 <;> by_cases h242 : i = 242 <;> simp [M,h110,h132,h241,h242]
  exact (Exec.seq he he₂).cast rfl (congrArg (mk v₂) hframe)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
