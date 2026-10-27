module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildMarkedRowCoefficientPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Keep coefficient packets outside row arithmetic, with independent setup and supplier views. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

/-- Relocate one native port outside the arithmetic bank. -/
def couplingViewReg (src : Fin 117) (dst : Fin 144) (i : Fin 117) : Fin 144 :=
  if i = src then dst else groupReg i

theorem couplingViewReg_injective (src : Fin 117) (dst : Fin 144) (hdst : 117 ≤ dst.val) :
    Function.Injective (couplingViewReg src dst) := by
  intro i j he
  by_cases hi : i = src <;> by_cases hj : j = src
  · exact hi.trans hj.symm
  · simp only [couplingViewReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (groupReg_off dst hdst j he.symm)
  · simp only [couplingViewReg,hi,hj,ite_true,ite_false] at he
    exact False.elim (groupReg_off dst hdst i he)
  · simp only [couplingViewReg,hi,hj,ite_false] at he
    exact groupReg_injective he

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def prepareRetainedCouplingPacket : Pr P₀ 144 Q A U :=
  embProg (couplingViewReg 109 135) Empty.elim (buildMarkedRowCoefficientPacket (P₀ := Empty))

def retainedCouplingCoefficients : Pr P₀ 144 Q A U :=
  embProg (couplingViewReg 113 135) Empty.elim (markedRowCoefficient (P₀ := Empty))

theorem prepareRetainedCouplingPacket_exec {P q w s t u band a b i : ℕ}
    (hP : 13 ≤ P) (hiRow : i < s)
    (raw : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hi : (S.R 107).length = i) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildMarkedRowCoefficientPacketCost P q w s t u band i ∧
      Exec body prepareRetainedCouplingPacket (mk v S) m
        (mk v' {S with R := (Function.update S.R 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++S.R 135))}) := by
  let e := couplingViewReg 109 135
  have hb : ∀ r ∈ rowCoefficientPorts, (embStk e S).R r = [] := by
    intro r hr
    have hn : r ≠ 109 := by intro h; subst r; simp at hr
    change S.R (e r) = []
    simp only [e,couplingViewReg,hn,ite_false]
    rcases (by simpa only [mem_rowCoefficientPorts] using hr : r.val < 63 ∨ r = 108 ∨ r = 116) with h | h | h
    · exact hready.low r h
    · subst r; exact hready.fresh 108 (by simp)
    · subst r; exact hready.fresh 116 (by simp)
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := buildMarkedRowCoefficientPacket_exec
    (body := fun p : Empty => nomatch p) (P := P) (q := q) (w := w) (s := s) (t := t)
    (u := u) (band := band) (i := i) hP hiRow (embDn e v) (embStk e S)
    hready.precision hready.fraction hready.axis hready.period hready.parameter hready.bandwidth hi
    (hready.fresh 115 (by simp)) hready.width (hready.fresh 104 (by simp))
    (hready.fresh 105 (by simp)) (hready.fresh 106 (by simp)) hb
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingViewReg_injective 109 135 (by decide)) (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [embOvr_updR (couplingViewReg_injective 109 135 (by decide)),embOvr_stk]
  rfl

theorem retainedCouplingCoefficients_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (raw tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b raw (embStk groupReg S))
    (hpacket : S.R 135 = markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ markedRowCoefficientCost P q (liftedCoefficientWidth P q w s t u band) w band ∧
      Exec body retainedCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111)) 135
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++tail))}) := by
  let e := couplingViewReg 113 135
  have hb : ∀ r ∈ rowCoefficientPorts, (embStk e S).R r = [] := by
    intro r hr
    have hn : r ≠ 113 := by intro h; subst r; simp at hr
    change S.R (e r) = []
    simp only [e,couplingViewReg,hn,ite_false]
    rcases (by simpa only [mem_rowCoefficientPorts] using hr : r.val < 63 ∨ r = 108 ∨ r = 116) with h | h | h
    · exact hready.low r h
    · subst r; exact hready.fresh 108 (by simp)
    · subst r; exact hready.fresh 116 (by simp)
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := markedRowCoefficient_exec
    (body := fun p : Empty => nomatch p) (P := P) (q := q) (w := w) (s := s) (t := t)
    (u := u) (band := band) (i := i) (NeZero.pos s) hst hP hi tail (embDn e v) (embStk e S)
    (hready.fresh 115 (by simp)) hready.width hpacket
    (hready.fresh 104 (by simp)) (hready.fresh 105 (by simp)) (hready.fresh 106 (by simp))
    (hready.fresh 109 (by simp)) hb
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    (couplingViewReg_injective 113 135 (by decide)) (fun p => nomatch p) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let T := embStk e S
  let T₁ : Stacks 117 A := {T with R := (Function.update T.R 111
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++T.R 111))}
  change embOvr e ({T₁ with R := (Function.update T₁.R 113
    (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band (i+1)++tail))} : Stacks 117 A).get S = _
  rw [embOvr_updR (couplingViewReg_injective 113 135 (by decide)),
    show T₁ = {T with R := (Function.update T.R 111
      (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++T.R 111))} from rfl,

    embOvr_updR (couplingViewReg_injective 113 135 (by decide)),embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
