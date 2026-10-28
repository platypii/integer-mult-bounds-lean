module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundView
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoundList

/-! Specialize the generic batch pass once to the inverse's fixed released core ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem placedInverseRound_exec (hA : 4 ≤ A) {W w q p j E : ℕ}
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt 8 A)
    (hval : st.val = ![w,q,p,j,E,0,0,0])
    (hp : p ≤ q) (hw : 1 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W)
    (hfit : ∀ i, st.val i < 2^W) (xs : List GaussianInt)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds inverseRoundScalarReg S (tblRho W wl [] st))
    (hsrc : S.R 132 = cstream A w xs)
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 13*tblC W 0+16*w+44*W+38+xs.length*(14*w+23) ∧
      Exec body (generatedFinalRound inverseRoundScalarReg inverseRoundPorts 132 4 5 6 7 8)
        (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A (p+E+5) (xs.map (finalRoundWord w q p j))))}) := by
  have hv (i : Fin 8) := congrFun hval i
  obtain ⟨v',n,hu,hn,he,hd,ht⟩ := generatedFinalRound_list_exec (body := body)
    (src := 132) (dst := 4) (tmp := 5) (sp := 6) (sg := 7) (cy := 8)
    (W := W) (w := w) (q := q) (p := p) (j := j) (E := E) hA
    inverseRoundScalarReg inverseRoundScalarReg_injective inverseRoundPorts inverseRoundPorts_injective
    inverseRoundScalarReg_ports (by decide) wl hwl st
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) hp hw hsize hroom hfit xs v S hS hsrc
    (by intro r hr; apply hblank; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; tauto)
    (by intro i; apply hblank; fin_cases i <;> decide)
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
