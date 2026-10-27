module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedResidualControls

/-! Generate the ordinary coupling headers without touching either retained coefficient key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedCouplingHeadersInstall : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (installCouplingHeaders (P₀ := Empty))

theorem placedCouplingHeadersInstall_exec (P N q l s t u band a b : ℕ)
    (input : List (Fin (A+4))) (v : HS 256 Q A U) (S : Stacks 256 A)
    (h : LengthKeyReady P N q l s t u band 0 0 input (embStk couplingSourceReg S))
    (ha : ((embStk couplingSourceReg S).R 141).length = a)
    (hb : ((embStk couplingSourceReg S).R 142).length = b) :
    let T := embStk couplingSourceReg S
    let H : Stacks 144 A := {T with R := couplingHeadersR P q s t u band a b T.R}
    let G := embOvr couplingSourceReg H.get S
    ∃ v', v'.user = v.user ∧
      Exec body placedCouplingHeadersInstall (mk v S) (installCouplingHeadersCost P q s t u band a b) (mk v' G) ∧
      CouplingReady P q (2*q+8) s t u band a b input (embStk groupReg (embStk couplingSourceReg G)) := by
  dsimp only
  obtain ⟨vi,hu,he,hready⟩ := installCouplingHeaders_exec (body := fun p : Empty => nomatch p)
    P N q l s t u band a b input (embDn couplingSourceReg v) (embStk couplingSourceReg S) h ha hb
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',hu'.trans hu,he',?_⟩
  rw [embStk_ovr couplingSourceReg_injective]
  exact hready

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
