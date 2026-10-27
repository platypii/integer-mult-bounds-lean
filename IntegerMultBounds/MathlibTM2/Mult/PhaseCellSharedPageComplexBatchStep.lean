module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexComponent
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Park one solved complex line while keeping the prepared page in place. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def sharedComplexBatchCoreReg (i : Fin 240) : Fin 248 := ⟨i.val, by omega⟩

theorem sharedComplexBatchCoreReg_injective : Function.Injective sharedComplexBatchCoreReg := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 248 => k.val) he)

theorem sharedComplexBatchCoreReg_off (i : Fin 240) (j : Fin 248) (hj : 240 ≤ j.val) :
    sharedComplexBatchCoreReg i ≠ j := by
  intro he
  have hv := congrArg (fun k : Fin 248 => k.val) he
  change i.val = j.val at hv
  have hi := i.isLt
  omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def sharedComplexBatchPark : Pr P 248 Q A U :=
  .seq (transfer 243 110 241 244) (transfer 243 132 242 244)

noncomputable def sharedComplexBatchStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 248 Q A U :=
  .seq (embProg sharedComplexBatchCoreReg Empty.elim (sharedPageComplexComponent (P := Empty) hR hQ))
    sharedComplexBatchPark

theorem sharedComplexBatchPark_exec (v : HS 248 Q A U) (S : Stacks 248 A)
    (input output inputTail page : List (Fin (A+4)))
    (hinput : S.R 110 = input++inputTail) (houtput : S.R 132 = output++page)
    (hclock : (S.R 243).length = input.length) (hlen : output.length = input.length)
    (htmp : S.R 244 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body sharedComplexBatchPark (mk v S) (8*input.length+8)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          110 inputTail) 241 (input.reverse++S.R 241)) 132 page) 242 (output.reverse++S.R 242))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := 243) (src := 110)
    (dst := 241) (tmp := 244) (by decide) v S input inputTail hinput hclock htmp
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update S.R
    110 inputTail) 241 (input.reverse++S.R 241))}
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 243) (src := 132)
    (dst := 242) (tmp := 244) (by decide) v₁ S₁ output page
    (by simpa [S₁] using houtput) (by simpa [S₁,hlen] using hclock) (by simpa [S₁] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,?_⟩
  have he := Exec.seq he₁ he₂
  have hcost : 8*input.length+8 = (4*input.length+4)+(4*output.length+4) := by rw [hlen]; omega
  rw [hcost]
  exact he

theorem sharedComplexBatchStep_of_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (v : HS 248 Q A U) (S : Stacks 248 A) (v₁ : HS 240 Q A U) (n : ℕ)
    (input output inputTail : List (Fin (A+4)))
    (hinput : S.R 110 = input++inputTail)
    (hclock : (S.R 243).length = input.length) (hlen : output.length = input.length)
    (htmp : S.R 244 = []) (hu : v₁.user = v.user)
    (he : Exec (fun p : Empty => nomatch p) (sharedPageComplexComponent hR hQ)
      (mk (embDn sharedComplexBatchCoreReg v) (embStk sharedComplexBatchCoreReg S)) n
      (mk v₁ {(embStk sharedComplexBatchCoreReg S) with R :=
        (Function.update (embStk sharedComplexBatchCoreReg S).R 132 (output++S.R 132))})) :
    ∃ v', v'.user = v.user ∧
      Exec body (sharedComplexBatchStep hR hQ) (mk v S) (n+(8*input.length+8))
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          110 inputTail) 241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242))}) := by
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedComplexBatchCoreReg_injective (fun p => nomatch p) he v rfl S rfl
  let M : Stacks 248 A := {S with R := Function.update S.R 132 (output++S.R 132)}
  have he₂' : Exec body
      (embProg sharedComplexBatchCoreReg Empty.elim (sharedPageComplexComponent (P := Empty) hR hQ))
      (mk v S) n (mk v₂ M) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR sharedComplexBatchCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₃,hu₃,he₃⟩ := sharedComplexBatchPark_exec (body := body) v₂ M
    input output inputTail (S.R 132) (by simpa [M] using hinput)
    (by simp [M]) (by simpa [M] using hclock) hlen (by simpa [M] using htmp)
  refine ⟨v₃,hu₃.trans (hu₂.trans hu),?_⟩
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
  exact (Exec.seq he₂' he₃).cast rfl (congrArg (mk v₃) hframe)

theorem sharedComplexBatchPark_coreFrame {A : ℕ} (S : Stacks 248 A)
    (input output inputTail page : List (Fin (A+4))) (i : Fin 240)
    (h110 : i ≠ 110) (h132 : i ≠ 132) :
    ({S with R := (Function.update (Function.update (Function.update (Function.update S.R
      110 inputTail) 241 (input.reverse++S.R 241)) 132 page) 242 (output.reverse++S.R 242))} : Stacks 248 A).R
      (sharedComplexBatchCoreReg i) = S.R (sharedComplexBatchCoreReg i) := by
  have hn110 : sharedComplexBatchCoreReg i ≠ 110 := sharedComplexBatchCoreReg_injective.ne h110
  have hn132 : sharedComplexBatchCoreReg i ≠ 132 := sharedComplexBatchCoreReg_injective.ne h132
  simp only [Function.update_of_ne (sharedComplexBatchCoreReg_off i 242 (by decide)),
    Function.update_of_ne hn132, Function.update_of_ne (sharedComplexBatchCoreReg_off i 241 (by decide)),
    Function.update_of_ne hn110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
