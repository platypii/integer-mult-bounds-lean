module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Execute a geometry program with one-symbol emissions, publish its stream and release its bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def originStreamHost (code : TblCode 16) : Pr P₀ 117 Q A U :=
  .seq (uclear 17) (.seq (.act (.push (.rt 17) (fun _ => tick) .done))
    (.seq (tblHost originReg code 109) releaseOriginBank))

theorem originStreamHost_exec {V K : ℕ} (hV : 1 ≤ V) (code : TblCode 16) (st : TblSt 16 A)
    (xs : List (Fin (A+4))) (hacc : st.acc = [])
    (hc : TblDo A V 1 code st (fun st' => st'.acc = xs.reverse++st.acc) K)
    (hbound : ∀ r, st.val r < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V 1+64*V+2*xs.length+68 ∧
      Exec body (originStreamHost code) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then xs++S.R r else S.R r}) := by
  have h17 : S.R 17 = List.replicate V tick := by simpa [originReg,tblRho] using hS .wn
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) 17 v S
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 17 []}
  have he₁' : Exec body (uclear 17) (mk v S) (2*V+2) (mk v₁ S₁) := by simpa [S₁,h17] using he₁
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 17 [tick]}
  have he₂ : Exec body (.act (.push (.rt 17) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,Action.run,update_rt] using
      Exec.act (body := body) (.push (.rt 17) (fun _ => tick) .done) (mk v₁ S₁)
  have hh₂ : tblHolds originReg S₂ (tblRho V (List.replicate V tick) [tick] st) := by
    intro r
    by_cases hr : r = .wn
    · subst r; simp [S₂,S₁,originReg,tblRho]
    · have hne : originReg r ≠ (17 : Fin 117) := by
        change originReg r ≠ originReg .wn
        exact originReg_injective.ne hr
      have hh := hS r
      cases r <;> simp_all [S₂,S₁,tblRho]
  obtain ⟨v₃,S₃,m₃,st',hpost,hu₃,hm₃,he₃,hout,hh₃,hin₃,ho₃,hl₃,hf₃⟩ := tblHost_runs (body := body) (out := 109)
    originReg_injective (by intro r; have hr := originReg_range r; intro h; rw [h] at hr; norm_num at hr)
    (List.replicate V tick) [tick] (by simp) (by simp) hV hc hbound v₁ S₂ hh₂
  rw [hpost,hacc,List.append_nil,List.length_reverse] at hm₃
  rw [hpost,hacc,List.append_nil,List.reverse_reverse] at hout
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := releaseOriginBank_width_exec (body := body) V 1 hV st'.val v₃ S₃ hh₃
  refine ⟨v₄,(2*V+2)+(1+(m₃+m₄)),hu₄.trans (hu₃.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext hin₃ ho₃ hl₃ ?_
  funext r
  by_cases hr : r.val < 31
  · simp [hr]
  · by_cases h109 : r = 109
    · subst r; simpa [S₂,S₁] using hout
    · have h17r : r ≠ 17 := by intro h; subst r; norm_num at hr
      have hsep : ∀ k, originReg k ≠ r := by
        intro k he
        have hk := originReg_range k
        rw [he] at hk
        omega
      simp [hr,h109,hf₃ r h109 hsep,S₂,S₁,h17r]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
