module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryWindowCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Publish computed recovery-window bounds as owned unary counters, then release the table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def recoveryWindowCounters (ambient : Bool) : Pr P 117 Q A U :=
  .seq (tblCompile originReg (recoveryWindowCode ambient))
    (.seq (toUnary 8 108 25 26 27) (.seq (toUnary 9 106 25 26 27) releaseOriginBank))

def recoveryWindowCountersCost (ambient : Bool) (W s B a b : ℕ) : ℕ :=
  9*tblC W W+6*(recoveryWindowLower ambient s B a+recoveryWindowUpper ambient s B b)+84*W+75

theorem recoveryWindowCounters_exec {W s B a b : ℕ} (ambient : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (hB : st.val 2 = B) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hwide : 2*s+2*B+8 < 2^W)
    (hbound : ∀ r, st.val r < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate W tick) st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryWindowCountersCost ambient W s B a b ∧
      Exec body (recoveryWindowCounters ambient) (mk v S) n
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 108 then
          List.replicate (recoveryWindowLower ambient s B a) tick else if r = 106 then
            List.replicate (recoveryWindowUpper ambient s B b) tick else S.R r}) := by
  let ready := recoveryWindowState ambient s B a b st
  let lo := recoveryWindowLower ambient s B a
  let hi := recoveryWindowUpper ambient s B b
  have hsep (r : Fin 117) (hr : 31 ≤ r.val) : ∀ x, originReg x ≠ r := by
    intro x he
    have hx := originReg_range x
    rw [he] at hx
    omega
  have hsW : s < 2^W := by omega
  have hbnds := recoveryWindow_bounds ambient s B a b has
  have hloW : lo < 2^W := hbnds.1.trans_lt hsW
  have hhiW : hi < 2^W := hbnds.2.trans_lt hsW
  have hc := recoveryWindowCode_do (A := A) (W := W) (w := W) ambient st hs hB ha hb has hbs hwide
  obtain ⟨st',heq,hr⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate W tick) (List.replicate W tick) (by simp) (by simp) le_rfl hc hbound
  subst heq
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hf₁⟩ := hr v S hS
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear (body := body)
    (show [(8 : Fin 117),108,25,26,27].Nodup by decide) hloW v₁ S₁
    (by simpa [originReg,tblRho,recoveryWindowState,lo] using hh₁ (.v 8))
    (by simpa [originReg,tblRho] using hh₁ (.z 6))
    (by simpa [originReg,tblRho] using hh₁ (.z 7))
    (by simpa [originReg,tblRho] using hh₁ (.z 8))
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 108 (List.replicate lo tick)}
  have he₂' : Exec body (toUnary 8 108 25 26 27) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,hf₁.2.2.2 108 (hsep 108 (by decide)),h108] using he₂
  have hh₂ : tblHolds originReg S₂ (tblRho W (List.replicate W tick) (List.replicate W tick) ready) := by
    intro r
    simp [S₂,(hsep 108 (by decide)) r,hh₁ r,ready]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := toUnary_exec_linear (body := body)
    (show [(9 : Fin 117),106,25,26,27].Nodup by decide) hhiW v₂ S₂
    (by simpa [originReg,tblRho,ready,recoveryWindowState,hi] using hh₂ (.v 9))
    (by simpa [originReg,tblRho] using hh₂ (.z 6))
    (by simpa [originReg,tblRho] using hh₂ (.z 7))
    (by simpa [originReg,tblRho] using hh₂ (.z 8))
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 106 (List.replicate hi tick)}
  have he₃' : Exec body (toUnary 9 106 25 26 27) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,hf₁.2.2.2 106 (hsep 106 (by decide)),h106] using he₃
  have hh₃ : tblHolds originReg S₃ (tblRho W (List.replicate W tick) (List.replicate W tick) ⟨ready.val,[]⟩) := by
    intro r
    simpa [S₃,(hsep 106 (by decide)) r,ready,recoveryWindowState,hacc] using hh₂ r
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := releaseOriginBank_width_exec (body := body) W W le_rfl ready.val v₃ S₃ hh₃
  refine ⟨v₄,n₁+(n₂+(n₃+n₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl ?_⟩
  · dsimp only [recoveryWindowCountersCost]
    dsimp only [lo,hi] at hn₂ hn₃
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
    funext r
    by_cases hr31 : r.val < 31
    · simp [hr31]
    by_cases hr108 : r = 108
    · subst r; simp [hr31,S₃,S₂,lo]
    by_cases hr106 : r = 106
    · subst r; simp [hr31,hr108,S₃,hi]
    have hroff : 31 ≤ r.val := by omega
    simp [hr31,hr108,hr106,S₃,S₂,hf₁.2.2.2 r (hsep r hroff)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
