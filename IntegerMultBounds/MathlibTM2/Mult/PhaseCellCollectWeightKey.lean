module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLoadWeightKey

/-! Collect one used page in reverse packet order, releasing the active page and clock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def collectWeightKey : Pr P 151 Q A U :=
  .seq (.act (.push (.rt 145) (fun _ => tick) .done))
    (.seq (takePrefix 145 149 150 146 147) (.seq (moveR 144 150 id) (uclear 145)))

theorem collectWeightKey_exec (v : HS 151 Q A U) (S : Stacks 151 A)
    (page : List (Fin (A+4))) (hpage : S.R 144 = page)
    (hclock : S.R 145 = List.replicate page.length tick)
    (hheader : S.R 149 = blank::List.replicate page.length tick)
    (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    ∃ v', v'.user = v.user ∧ Exec body collectWeightKey (mk v S) (10*page.length+19)
      (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        144 []) 145 []) 149 []) 150 ((weightKeyPacket page).reverse++S.R 150))}) := by
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 145 (tick::S.R 145)}
  have he₁ : Exec body (.act (.push (.rt 145) (fun _ => tick) .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,Action.run,update_rt] using Exec.act (body := body)
      (.push (.rt 145) (fun _ => tick) .done) (mk v S)
  let header := blank::List.replicate page.length (tick : Fin (A+4))
  have hlen : header.length = page.length+1 := by simp [header]
  obtain ⟨v₂,hu₂,he₂⟩ := takePrefix_exec (body := body)
    (show [(145 : Fin 151),149,150,146,147].Nodup by decide) v S₁ header []
    (by simpa [S₁,header] using hheader) (by simp [S₁,header,hclock])
    (by simp [S₁,h146]) (by simp [S₁,h147])
  let T : Stacks 151 A := {S₁ with R := (Function.update (Function.update S₁.R 149 [])
    150 (header++S₁.R 150))}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 144 150 (by decide) id v₂ T
  let U : Stacks 151 A := {T with R := movedR T.R 144 150 id (T.R 144)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 145 v₃ U
  refine ⟨v₄,hu₄.trans (hu₃.trans hu₂),(Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [U,T,S₁,movedR,hpage,hclock,hlen]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h144 : i = 144 <;> by_cases h145 : i = 145 <;>
      by_cases h149 : i = 149 <;> by_cases h150 : i = 150 <;>
      simp [U,T,S₁,movedR,Function.update_apply,h144,h145,h149,h150,hpage,
        weightKeyPacket,header,List.reverse_append,List.append_assoc]

def restoreWeightKeyFamily : Pr P 151 Q A U := moveR 150 148 id

theorem restoreWeightKeyFamily_exec (v : HS 151 Q A U) (S : Stacks 151 A)
    (pages : List (List (Fin (A+4)))) (tail : List (Fin (A+4)))
    (hcomplete : S.R 150 = (weightKeyFamily pages).reverse) (hsource : S.R 148 = tail) :
    ∃ v', v'.user = v.user ∧
      Exec body restoreWeightKeyFamily (mk v S) (2*(weightKeyFamily pages).length+2)
        (mk v' {S with R := (Function.update (Function.update S.R 148
          (weightKeyFamily pages++tail)) 150 [])}) := by
  obtain ⟨v',hu,he⟩ := moveR_exec body 150 148 (by decide) id v S
  refine ⟨v',hu,he.cast (by simp [hcomplete]) ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h148 : i = 148 <;> by_cases h150 : i = 150 <;>
    simp [movedR,Function.update_apply,h148,h150,hcomplete,hsource]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
