module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightKeyFamily
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherControl

/-! Load the next counted page, retaining its reversed header for exact family restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def loadWeightKey : Pr P 151 Q A U :=
  .seq (gatherRead 148 145 149) (takePrefix 145 148 144 146 147)

theorem loadWeightKey_exec (v : HS 151 Q A U) (S : Stacks 151 A)
    (page rest : List (Fin (A+4))) (hsource : S.R 148 = weightKeyPacket page++rest)
    (hfresh : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = []) :
    ∃ v', v'.user = v.user ∧ Exec body loadWeightKey (mk v S) (8*page.length+9)
      (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        148 rest) 144 page) 145 (List.replicate page.length tick))
        149 (blank::List.replicate page.length tick))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := gatherRead_exec (body := body)
    (show [(148 : Fin 151),145,149].Nodup by decide) page.length (page++rest) v S
    (by simpa [weightKeyPacket,List.append_assoc] using hsource)
  let T : Stacks 151 A := {S with R := (Function.update (Function.update (Function.update S.R
    148 (page++rest)) 145 (List.replicate page.length tick)) 149 (blank::List.replicate page.length tick))}
  have he₁' : Exec body (gatherRead 148 145 149) (mk v S) (2*page.length+3) (mk v₁ T) := by
    simpa [T,hfresh 145 (by simp),hfresh 149 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (show [(145 : Fin 151),148,144,146,147].Nodup by decide) v₁ T page rest
    (by simp [T]) (by simp [T]) (by simp [T,hfresh 146 (by simp)]) (by simp [T,hfresh 147 (by simp)])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h144 : i = 144 <;> by_cases h145 : i = 145 <;> by_cases h148 : i = 148 <;>
    by_cases h149 : i = 149 <;> simp [T,Function.update_apply,h144,h145,h148,h149,hfresh 144 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
