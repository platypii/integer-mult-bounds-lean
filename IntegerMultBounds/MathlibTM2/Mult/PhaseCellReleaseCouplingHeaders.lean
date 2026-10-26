module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Release the installed coupling headers, retaining the original master bank and payloads. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def couplingHeaderRegisters : List (Fin 144) := [114,112,97,98,99,100,101,103,94]

def releaseCouplingHeaders : Pr P₀ 144 Q A U := clearWords couplingHeaderRegisters

def releaseCouplingHeadersCost (P q s t u band a b : ℕ) : ℕ :=
  2*(P+3*q+s+t+u+band+a+b)+35

theorem releaseCouplingHeaders_exec (P q s t u band a b : ℕ)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hblank : ∀ k ∈ couplingHeaderRegisters, S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseCouplingHeaders
        (mk v {S with R := couplingHeadersR P q s t u band a b S.R})
        (releaseCouplingHeadersCost P q s t u band a b) (mk v' S) := by
  let S₁ : Stacks 144 A := {S with R := couplingHeadersR P q s t u band a b S.R}
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) couplingHeaderRegisters (by decide) v S₁
  refine ⟨v',hu,he.cast ?_ ?_⟩
  · simp [S₁,couplingHeaderRegisters,couplingHeadersR,unaryCopiesR,couplingHeaderCopies,
      couplingHeaderValue,releaseCouplingHeadersCost,
      hblank 114 (by decide),
      hblank 112 (by decide),
      hblank 97 (by decide),
      hblank 98 (by decide),
      hblank 99 (by decide),
      hblank 100 (by decide),
      hblank 101 (by decide),
      hblank 103 (by decide)]
    omega
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ couplingHeaderRegisters
    · simpa only [hk,ite_true] using (hblank k hk).symm
    · simpa only [hk,ite_false] using couplingHeadersR_off P q s t u band a b S.R k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
