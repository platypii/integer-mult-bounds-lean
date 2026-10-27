module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectWeightKey

/-! Form a counted packet from the generated page and its actual replay clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def storeGeneratedWeightKey : Pr P 151 Q A U :=
  .seq (ucopy 145 149 146)
    (.seq (.act (.push (.rt 149) (fun _ => blank) .done)) collectWeightKey)

theorem storeGeneratedWeightKey_exec (v : HS 151 Q A U) (S : Stacks 151 A)
    (page : List (Fin (A+4))) (hpage : S.R 144 = page)
    (hclock : S.R 145 = List.replicate page.length tick)
    (h146 : S.R 146 = []) (h147 : S.R 147 = []) (h149 : S.R 149 = []) :
    ∃ v', v'.user = v.user ∧ Exec body storeGeneratedWeightKey (mk v S) (14*page.length+24)
      (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        144 []) 145 []) 149 []) 150 ((weightKeyPacket page).reverse++S.R 150))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 145) (b := 149) (t := 146)
    (by decide) (by decide) (by decide) v S h146
  let T : Stacks 151 A := {S with R := Function.update S.R 149 (List.replicate page.length tick)}
  have he₁' : Exec body (ucopy 145 149 146) (mk v S) (4*page.length+4) (mk v₁ T) := by
    simpa [T,hclock,h149] using he₁
  let U : Stacks 151 A := {T with R := Function.update T.R 149 (blank::T.R 149)}
  have he₂ : Exec body (.act (.push (.rt 149) (fun _ => blank) .done)) (mk v₁ T) 1 (mk v₁ U) := by
    simpa [U,Action.run,update_rt] using Exec.act (body := body)
      (.push (.rt 149) (fun _ => blank) .done) (mk v₁ T)
  obtain ⟨v₂,hu₂,he₃⟩ := collectWeightKey_exec (body := body) v₁ U page
    (by simpa [U,T] using hpage) (by simpa [U,T] using hclock)
    (by simp [U,T]) (by simp [U,T,h146]) (by simp [U,T,h147])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 149 <;> simp [U,T,Function.update_apply,hi]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
