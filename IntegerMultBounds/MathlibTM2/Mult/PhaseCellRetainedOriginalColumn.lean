module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredOriginalColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentWorkspace

/-! Generate original columns while preserving the retained complex-component registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedOriginalColumn (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  embProg componentReg id (restoredOriginalColumn hQ)

theorem retainedOriginalColumn_spec (hQ : SS.states ≤ Q)
    {p q N l s t u a b : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hcoordinate : (S.R 139).length = j.val) (h143 : S.R 143 = []) (h138 : S.R 138 = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A (2*q+8) (chirpLine s column)++tail
    let S' : Stacks 148 A := {S with R := Function.update S.R 110 output}
    ∃ v' m, v'.user = v.user ∧ m ≤ restoredOriginalColumnCost p q s t u a b j.val ∧
      Exec (embTab componentReg (embTab groupReg body)) (retainedOriginalColumn hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      (∀ i, |publishedCellRead q (2*q+8) (0 : ZMod s) (S'.R 110) i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      LengthKeyReady (2^15*p) N q l s t u band 0 0 output (embStk componentReg S') := by
  dsimp only
  let band := PhaseCellBand.width p u
  let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let output := cstream A (2*q+8) (chirpLine s column)++tail
  obtain ⟨v₁,m,hu₁,hm,he₁,hreal,hnorm,herror,hready₁⟩ := restoredOriginalColumn_spec (body := body)
    hQ hA hp hwidth hα hst hαu hθ hgap hbudget hw haS hbS hbandS j hj tail
    (embDn componentReg v) (embStk componentReg S) hready
    (by simpa [embStk,componentReg] using haMaster) (by simpa [embStk,componentReg] using hbMaster)
    (by simpa [embStk,componentReg] using hcoordinate) (by simpa [embStk,componentReg] using h143)
    (by simpa [embStk,componentReg] using h138)
  have hbody : ∀ p, (embTab componentReg (embTab groupReg body)) (id p) =
      embProg componentReg id ((embTab groupReg body) p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id)
    (body' := embTab componentReg (embTab groupReg body)) componentReg_injective hbody he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,?_,hreal,hnorm,?_,?_⟩
  · unfold retainedOriginalColumn
    convert he₂ using 1
    apply congrArg (mk v₂)
    rw [embOvr_updR componentReg_injective (embStk componentReg S) S 110 output,embOvr_stk]
    rfl
  · simpa [componentReg,embStk,output,column,band] using herror
  · have hproject : embStk componentReg {S with R := Function.update S.R 110 output} =
        {(embStk componentReg S) with R := Function.update (embStk componentReg S).R 110 output} := by
      simpa [componentReg] using componentProject_updateR_inner S 110 output
    rw [hproject]
    exact hready.update_source output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
