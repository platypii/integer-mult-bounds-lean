module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady

/-! Derive page-generation clocks from ordinary band and ambient-length masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareCouplingPageCounts : Pr P₀ 144 Q A U :=
  .seq (.act (.push (.rt 140) (fun _ => tick) .done))
    (.seq (umul 2 100 140 109) (ucopy 97 143 104))

def prepareCouplingPageCountsCost (s band : ℕ) : ℕ := 4*band+4*s+9

theorem prepareCouplingPageCounts_exec (s band : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hb : (S.R 100).length = band)
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) (h109 : S.R 109 = []) (h104 : S.R 104 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body prepareCouplingPageCounts (mk v S) (prepareCouplingPageCountsCost s band)
        (mk v' {S with R := (Function.update (Function.update S.R 140 (List.replicate (2*band+1) tick))
          143 (List.replicate s tick))}) := by
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 140 [tick]}
  have he₁ : Exec body (.act (.push (.rt 140) (fun _ => tick) .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,h140,Action.run,update_rt] using Exec.act (body := body) (.push (.rt 140) (fun _ => tick) .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := umul_exec (body := body) 2 (a := 100) (b := 140) (t := 109)
    (by decide) (by decide) (by decide) v S₁ (by simpa [S₁] using h109)
  let S₂ : Stacks 144 A := {S with R := Function.update S.R 140 (List.replicate (2*band+1) tick)}
  have he₂' : Exec body (umul 2 100 140 109) (mk v S₁) (4*band+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hb,List.replicate_add] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 97) (b := 143) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂] using h104)
  have he₃' : Exec body (ucopy 97 143 104) (mk v₂ S₂) (4*s+4)
      (mk v₃ {S with R := (Function.update (Function.update S.R 140 (List.replicate (2*band+1) tick))
        143 (List.replicate s tick))}) := by
    simpa [S₂,hs,h143] using he₃
  exact ⟨v₃,hu₃.trans hu₂,(Exec.seq he₁ (Exec.seq he₂' he₃')).cast (by unfold prepareCouplingPageCountsCost; omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
