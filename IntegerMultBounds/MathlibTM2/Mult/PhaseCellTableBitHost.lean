module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainBinaryBit
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Publish a computed table bit as one unary control, then release the table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def tableBitHost (code : TblCode 16) : Pr P₀ 117 Q A U :=
  .seq (tblCompile originReg code)
    (.seq (retainBinaryBit 15 109) (.seq releaseOriginBank (.act (peekR 109))))

theorem tableBitHost_exec {V K : ℕ} (code : TblCode 16) (st : TblSt 16 A) (flag : Bool)
    (hc : TblDo A V V code st (fun st' => st'.val 15 = (if flag then 1 else 0) ∧ st'.acc = []) K)
    (hbound : ∀ r, st.val r < 2^V) (hV : 0 < V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (h109 : S.R 109 = [])
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = flag ∧ m ≤ K*tblC V V+62*V+65 ∧
      Exec body (tableBitHost code) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          (if flag then [tick] else []) else S.R r}) := by
  obtain ⟨st',⟨hp,_⟩,hrun⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl
    (hc.bounded hbound) hbound
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := hrun v S hS
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun x he => by have hx := originReg_range x; rw [he] at hx; omega)
  have hsrc : S₁.R 15 = binSyms V (if flag then 1 else 0) := by
    simpa [tblRho,originReg,hp.1] using hh₁ (.v 15)
  have he₂ := retainBinaryBit_exec (body := body) 15 109 V hV flag v₁ S₁ hsrc
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    ((if flag then [tick] else [])++S₁.R 109))}
  have hh₂ : tblHolds originReg S₂
      (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val,[]⟩) := by
    intro r
    have hne : originReg r ≠ 109 := by have hx := originReg_range r; intro he; rw [he] at hx; omega
    have hh := hh₁ r
    cases r <;> simpa [S₂,hne,tblRho,hp.2] using hh
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseOriginBank_exec (body := body) V st'.val {v₁ with flag := flag} S₂ hh₂
  let S₃ : Stacks 117 A := {S₂ with R := fun r => if r.val < 31 then [] else S₂.R r}
  have hflag : (S₃.R 109).head?.isSome = flag := by
    cases flag <;> simp [S₃,S₂,hoff 109 (by decide),h109]
  have he₄ := Exec.act (body := body) (peekR 109) (mk v₃ S₃)
  rw [peekR_run,hflag] at he₄
  refine ⟨{v₃ with flag := flag},m₁+(1+(m₃+1)),hu₃.trans hu₁,rfl,by omega,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  apply congrArg (mk {v₃ with flag := flag})
  refine Stacks.ext ?_ ?_ ?_ ?_
  · exact hf₁.1
  · exact hf₁.2.1
  · exact hf₁.2.2.1
  · funext r
    by_cases hr : r.val < 31
    · simp [S₃,hr]
    · have hr' : 31 ≤ r.val := by omega
      by_cases h109' : r = 109
      · subst r; simp [S₃,S₂,hoff 109 (by decide),h109]
      · simp [S₃,S₂,hr,h109',hoff r hr']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
