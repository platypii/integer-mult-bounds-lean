module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSavedHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare

/-! Generate multiplication readiness from the coupling precision header,
while preserving the geometry header occupying the setup precision port. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def couplingReadinessCore : Pr P₀ 117 Q A U :=
  .seq (ucopy 112 100 109) (.seq prepare (uclear 100))

def couplingReadiness : Pr P₀ 117 Q A U := withSavedHeader 100 couplingReadinessCore

theorem couplingReadiness_exec (q w : ℕ) (hw5 : 5 ≤ w) (hw : q+4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q) (hwR : (S.R 94).length = w)
    (hL : S.L 100 = []) (h109 : S.R 109 = [])
    (hclean : ∀ k : Fin 117, k.val < 26 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w+6*q+4*(S.R 100).length+10 ∧
      Exec body couplingReadiness (mk v S) m (mk v' {S with R := counterR q w S.R}) := by
  have hoff (r : CR) : cr r ≠ (100 : Fin 117) := by
    have hr := (cr_range r).2.1
    intro he
    have hv := congrArg Fin.val he
    omega
  have hcount : counterR q w S.R 100 = S.R 100 := by simp [counterR,Ne.symm (hoff _)]
  have hcall : ∀ v₀ : HS 117 Q A U, v₀.user = v.user →
      ∃ v₁ m, v₁.user = v₀.user ∧ m ≤ prepareCost q w+6*q+6 ∧
        Exec body couplingReadinessCore (mk v₀ (parkedHeader S 100)) m
          (mk v₁ (parkedHeader {S with R := counterR q w S.R} 100)) := by
    intro v₀ hu₀
    let B := parkedHeader S 100
    obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (show (112 : Fin 117) ≠ 100 by decide)
      (show (112 : Fin 117) ≠ 109 by decide) (show (100 : Fin 117) ≠ 109 by decide)
      v₀ B (by simpa [B,parkedHeader] using h109)
    let B₁ : Stacks 117 A := {B with R := Function.update B.R 100 (List.replicate q tick)}
    have he₁' : Exec body (ucopy 112 100 109) (mk v₀ B) (4*q+4) (mk v₁ B₁) := by
      simpa [B₁,B,parkedHeader,hq] using he₁
    obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := prepare_exec_of_width (body := body) q w hw5 hw v₁ B₁
      (by simp [B₁]) (by simpa [B₁,B,parkedHeader] using hwR)
      (by intro k hk
          have hn : k ≠ 100 := by intro he; subst k; norm_num at hk
          simpa [B₁,B,parkedHeader,hn] using hclean k hk)
      (by intro r hr; simpa [B₁,B,parkedHeader,hoff r] using hcounters r hr)
    let B₂ : Stacks 117 A := {B₁ with R := counterR q w B₁.R}
    obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 100 v₂ B₂
    have hb₂ : B₂.R 100 = List.replicate q tick := by simp [B₂,B₁,counterR,Ne.symm (hoff _)]
    refine ⟨v₃,(4*q+4)+(m₂+(2*q+2)),hu₃.trans (hu₂.trans hu₁),by omega,
      (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hb₂]; simp) ?_⟩
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl ?_ ?_
    · funext k
      simp [B₂,B₁,B,parkedHeader,hcount]
    · funext k
      simp only [B₂,B₁,B,parkedHeader,counterR,Function.update_apply]
      split_ifs <;> rfl
  obtain ⟨v',m,hu,hm,he⟩ := withSavedHeader_exec (body := body) 100 couplingReadinessCore v S
    {S with R := counterR q w S.R} (prepareCost q w+6*q+6) hL hL hcount hcall
  exact ⟨v',m,hu,by omega,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
