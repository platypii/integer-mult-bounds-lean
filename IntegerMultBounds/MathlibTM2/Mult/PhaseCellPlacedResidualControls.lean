module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeInteriorOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! Ordinary output allocation and header release preserve both retained cache banks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem embOvr_overwrite {T T' A : ℕ} (e : Fin T → Fin T')
    (X Y : Stacks T A) (S : Stacks T' A) :
    embOvr e X.get (embOvr e Y.get S) = embOvr e X.get S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; simp [embOvr,embExt]; cases embInv e i <;> rfl
  · funext i; simp [embOvr,embExt]; cases embInv e i <;> rfl

theorem embOvr_updateR_base {T T' A : ℕ} (e : Fin T → Fin T')
    (he : Function.Injective e) (X : Stacks T A) (S : Stacks T' A)
    (i : Fin T) (words : List (Fin (A+4))) :
    embOvr e X.get {S with R := Function.update S.R (e i) words} = embOvr e X.get S := by
  have hupdate : (embOvr e ({embStk e S with R := Function.update (embStk e S).R i words} : Stacks T A).get S) =
      {S with R := Function.update S.R (e i) words} := by
    rw [embOvr_updR he,embOvr_stk]
  rw [← hupdate,embOvr_overwrite]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 256 Q A U}

def placedInteriorOutputInitialize : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (initializeInteriorOutput (P₀ := Empty))

def placedCouplingHeadersRelease : Pr P₀ 256 Q A U :=
  embProg couplingSourceReg Empty.elim (releaseCouplingHeaders (P₀ := Empty))

theorem placedInteriorOutputInitialize_exec (q s : ℕ) (raw tail : List (Fin (A+4)))
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 110 = raw++tail) (hlen : raw.length = s*(2*q+8))
    (h94 : S.R 94 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeInteriorOutputCost q s ∧
      Exec body placedInteriorOutputInitialize (mk v S) m
        (mk v' {S with R := Function.update S.R 132 (raw++S.R 132)}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := initializeInteriorOutput_exec (body := fun p : Empty => nomatch p)
    q s raw tail (embDn couplingSourceReg v) (embStk couplingSourceReg S) hq hs hsrc hlen h94 h131 h134 h135
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR couplingSourceReg_injective,embOvr_stk]
  rfl

theorem placedCouplingHeadersRelease_exec (P q s t u band a b : ℕ)
    (v : HS 256 Q A U) (S : Stacks 256 A)
    (hblank : ∀ k ∈ couplingHeaderRegisters, (embStk couplingSourceReg S).R k = []) :
    let T := embStk couplingSourceReg S
    let H : Stacks 144 A := {T with R := couplingHeadersR P q s t u band a b T.R}
    ∃ v', v'.user = v.user ∧ Exec body placedCouplingHeadersRelease
      (mk v (embOvr couplingSourceReg H.get S))
      (releaseCouplingHeadersCost P q s t u band a b) (mk v' S) := by
  dsimp only
  let T := embStk couplingSourceReg S
  let H : Stacks 144 A := {T with R := couplingHeadersR P q s t u band a b T.R}
  let G := embOvr couplingSourceReg H.get S
  obtain ⟨vi,hu,he⟩ := releaseCouplingHeaders_exec (body := fun p : Empty => nomatch p)
    P q s t u band a b (embDn couplingSourceReg v) T hblank
  obtain ⟨v',hv',hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    couplingSourceReg_injective (fun p => nomatch p) he v rfl G
    (embStk_ovr couplingSourceReg_injective H S)
  refine ⟨v',hu'.trans hu,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [show G = embOvr couplingSourceReg H.get S from rfl,embOvr_overwrite,embOvr_stk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
