module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady

/-! Derive page-generation clocks from ordinary band and ambient-length masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareCouplingPageCountsOn {T : ℕ} (bandSrc lengthSrc rows count tmp saved : Fin T) : Pr P₀ T Q A U :=
  .seq (.act (.push (.rt rows) (fun _ => tick) .done))
    (.seq (umul 2 bandSrc rows tmp) (ucopy lengthSrc count saved))

def prepareCouplingPageCounts : Pr P₀ 144 Q A U :=
  prepareCouplingPageCountsOn 100 97 140 143 109 104

def prepareCouplingPageCountsCost (s band : ℕ) : ℕ := 4*band+4*s+9

theorem prepareCouplingPageCountsOn_exec {T : ℕ} {body : P₀ → Pr P₀ T Q A U}
    (bandSrc lengthSrc rows count tmp saved : Fin T)
    (hreg : [bandSrc,lengthSrc,rows,count,tmp,saved].Nodup) (s band : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R lengthSrc).length = s) (hb : (S.R bandSrc).length = band)
    (h140 : S.R rows = []) (h143 : S.R count = []) (h109 : S.R tmp = []) (h104 : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (prepareCouplingPageCountsOn bandSrc lengthSrc rows count tmp saved) (mk v S) (prepareCouplingPageCountsCost s band)
        (mk v' {S with R := (Function.update (Function.update S.R rows (List.replicate (2*band+1) tick))
          count (List.replicate s tick))}) := by
  have hreg' := hreg
  regs_ne hreg'

  let S₁ : Stacks T A := {S with R := Function.update S.R rows [tick]}
  have he₁ : Exec body (.act (.push (.rt rows) (fun _ => tick) .done)) (mk v S) 1 (mk v S₁) := by
    simpa [S₁,h140,Action.run,update_rt] using Exec.act (body := body) (.push (.rt rows) (fun _ => tick) .done) (mk v S)
  obtain ⟨v₂,hu₂,he₂⟩ := umul_exec (body := body) 2 (a := bandSrc) (b := rows) (t := tmp)
    (by assumption) (by assumption) (by assumption) v S₁ (by simpa [S₁,‹rows ≠ tmp›.symm] using h109)
  let S₂ : Stacks T A := {S with R := Function.update S.R rows (List.replicate (2*band+1) tick)}
  have he₂' : Exec body (umul 2 bandSrc rows tmp) (mk v S₁) (4*band+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hb,List.replicate_add,‹bandSrc ≠ rows›] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := lengthSrc) (b := count) (t := saved)
    (by assumption) (by assumption) (by assumption) v₂ S₂ (by simpa [S₂,‹rows ≠ saved›.symm] using h104)
  have he₃' : Exec body (ucopy lengthSrc count saved) (mk v₂ S₂) (4*s+4)
      (mk v₃ {S with R := (Function.update (Function.update S.R rows (List.replicate (2*band+1) tick))
        count (List.replicate s tick))}) := by
    simpa [S₂,hs,h143,‹lengthSrc ≠ rows›,‹rows ≠ count›.symm] using he₃
  exact ⟨v₃,hu₃.trans hu₂,(Exec.seq he₁ (Exec.seq he₂' he₃')).cast (by unfold prepareCouplingPageCountsCost; omega) rfl⟩

theorem prepareCouplingPageCounts_exec (s band : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hb : (S.R 100).length = band)
    (h140 : S.R 140 = []) (h143 : S.R 143 = []) (h109 : S.R 109 = []) (h104 : S.R 104 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body prepareCouplingPageCounts (mk v S) (prepareCouplingPageCountsCost s band)
        (mk v' {S with R := (Function.update (Function.update S.R 140 (List.replicate (2*band+1) tick))
          143 (List.replicate s tick))}) := by
  exact prepareCouplingPageCountsOn_exec 100 97 140 143 109 104 (by decide) s band v S
    hs hb h140 h143 h109 h104

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
