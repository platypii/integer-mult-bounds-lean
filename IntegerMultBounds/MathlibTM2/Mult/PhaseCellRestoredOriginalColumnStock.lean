module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedOriginalColumnStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredOriginalColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingHeadersFrame

/-! Generate an original column from retained masters, releasing all coupling runtime headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem installCouplingHeaders_native :
    mnNativePushBound 8 (installCouplingHeaders (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [installCouplingHeaders,copyUnaryHeaders,couplingHeaderCopies,couplingHeaderWidth,
    generateWordWidth,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

@[irreducible] def restoredOriginalColumnWorkspace (R p q s t u a b j : ℕ) : ℕ :=
  8*installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) a b +
    (3*(4*j+4)+generatedOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      R p q (2*q+8) s t u a b)

/-- Compose header restoration over abstract stores before instantiating tape updates. -/
theorem restoredOriginalColumn_trace_within
    {B : P₀ → Pr P₀ 144 Q A U} (hQ : SS.states ≤ Q)
    {v₀ v₁ v₂ v₃ v₄ v₅ : HS 144 Q A U} {S₀ S₁ S₂ S₃ S₄ S₅ : Stacks 144 A}
    {n₁ n₂ n₃ n₄ n₅ work cap : ℕ}
    (he₁ : Exec B installCouplingHeaders (mk v₀ S₀) n₁ (mk v₁ S₁))
    (he₂ : Exec B (ucopy 139 136 135) (mk v₁ S₁) n₂ (mk v₂ S₂))
    (he₃ : ExecWithin B (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+0+work) 0
      (generatedOriginalColumn hQ) (mk v₂ S₂) n₃ (mk v₃ S₃))
    (he₄ : Exec B (uclear 136) (mk v₃ S₃) n₄ (mk v₄ S₄))
    (he₅ : Exec B releaseCouplingHeaders (mk v₄ S₄) n₅ (mk v₅ S₅))
    (hcap : 8*n₁+(3*n₂+work) ≤ cap) :
    ExecWithin B (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+0+cap) 0
      (restoredOriginalColumn hQ) (mk v₀ S₀) (n₁+(n₂+(n₃+(n₄+n₅)))) (mk v₅ S₅) := by
  have ht₁ := mn_native_exec_within he₁ 8 installCouplingHeaders_native 0 _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂ 3 (by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
    0 _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 0 (by
    simp [uclear,drainR,popDo,whileR,peekR,mnNativePushBound,mnActPush])
    0 (mnSize (mk v₃ S₃)+0+0) (by omega)
  have ht₅ := mn_native_exec_within he₅ 0 (clearWords_native_zero _) 0
    (mnSize (mk v₄ S₄)+0+0) (by omega)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add ht₂
    (mn_seq_within_add he₃ (mn_seq_within_add ht₄ ht₅)))).mono (by intro d z hz; omega)

theorem restoredOriginalColumn_spec_within (hQ : SS.states ≤ Q)
    {p q N l s t u a b : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (tail : List (Fin (A+4))) (R : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ R)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : LengthKeyReady (2^15*p) N q l s t u (PhaseCellBand.width p u) 0 0 tail S)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hcoordinate : (S.R 139).length = j.val) (h143 : S.R 143 = []) (h138 : S.R 138 = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A (2*q+8) (chirpLine s column)++tail
    let S' : Stacks 144 A := {S with R := Function.update S.R 110 output}
    ∃ v' m, v'.user = v.user ∧ m ≤ restoredOriginalColumnCost p q s t u a b j.val ∧
      ExecWithin (embTab groupReg body) (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        restoredOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u a b j.val) 0
        (restoredOriginalColumn hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      (∀ i, |publishedCellRead q (2*q+8) (0 : ZMod s) (S'.R 110) i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      LengthKeyReady (2^15*p) N q l s t u band 0 0 output S' := by
  dsimp only
  let band := PhaseCellBand.width p u
  let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let output := cstream A (2*q+8) (chirpLine s column)++tail
  have h136 : S.R 136 = [] := hready.fresh 136 (by simp)
  obtain ⟨v₁,hu₁,he₁,hcoupling⟩ := installCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) N q l s t u band a b tail v S hready haMaster hbMaster
  let S₁ : Stacks 144 A := {S with R := couplingHeadersR (2^15*p) q s t u band a b S.R}
  have hoff (k : Fin 144) (hk : k ∉ couplingHeaderRegisters) : S₁.R k = S.R k :=
    couplingHeadersR_off (2^15*p) q s t u band a b S.R k hk
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := embTab groupReg body) (a := 139) (b := 136) (t := 135)
    (by decide) (by decide) (by decide) v₁ S₁
    (by rw [hoff 135 (by decide)]; exact hready.fresh 135 (by simp))
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 136 (List.replicate j.val tick)}
  have he₂' : Exec (embTab groupReg body) (ucopy 139 136 135) (mk v₁ S₁) (4*j.val+4) (mk v₂ S₂) := by
    simpa [S₂,hoff 139 (by decide),hoff 136 (by decide),hcoordinate,h136] using he₂
  have hproject : embStk groupReg S₂ = embStk groupReg S₁ := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hne : groupReg k ≠ (136 : Fin 144) := by
      have := k.isLt
      simp [groupReg,Fin.ext_iff]
      omega
    simp [S₂,embStk,Function.comp_def,hne]
  have hcoupling₂ : CouplingReady (2^15*p) q (2*q+8) s t u band a b tail (embStk groupReg S₂) := by
    rw [hproject]
    exact hcoupling
  have hoff₂ (k : Fin 144) (hk : k ∉ couplingHeaderRegisters) (h136' : k ≠ 136) : S₂.R k = S.R k := by
    simp [S₂,h136',hoff k hk]
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃,hreal,hnorm,herror,_⟩ := generatedOriginalColumn_spec_within (body := body)
    hQ hA hp hwidth hα hst hαu hθ hgap hbudget hw haS hbS hbandS j hj tail R hpush v₂ S₂ hcoupling₂
    (by simp [S₂])
    (by rw [hoff₂ 107 (by decide) (by decide)]; exact hready.blank 107 (by decide) (by decide) (by decide))
    (by rw [hoff₂ 143 (by decide) (by decide)]; exact h143)
    (by rw [hoff₂ 131 (by decide) (by decide)]; exact hready.fresh 131 (by simp))
    (by rw [hoff₂ 134 (by decide) (by decide)]; exact hready.fresh 134 (by simp))
    (by rw [hoff₂ 135 (by decide) (by decide)]; exact hready.fresh 135 (by simp))
    (by rw [hoff₂ 137 (by decide) (by decide)]; exact hready.fresh 137 (by simp))
    (by rw [hoff₂ 138 (by decide) (by decide)]; exact h138)
  let S₃ : Stacks 144 A := {S₂ with R := Function.update S₂.R 110 output}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := embTab groupReg body) 136 v₃ S₃
  let S₄ : Stacks 144 A := {S₃ with R := Function.update S₃.R 136 []}
  let Sfinal : Stacks 144 A := {S with R := Function.update S.R 110 output}
  have hframe : S₄ = {Sfinal with R := couplingHeadersR (2^15*p) q s t u band a b Sfinal.R} := by
    refine Stacks.ext rfl rfl rfl ?_
    change Function.update (Function.update (Function.update S₁.R 136 (List.replicate j.val tick)) 110 output) 136 [] = _
    rw [show couplingHeadersR (2^15*p) q s t u band a b Sfinal.R =
      Function.update S₁.R 110 output from couplingHeadersR_update _ _ _ _ _ _ _ _ S.R 110 output (by decide)]
    funext k
    by_cases h136' : k = 136 <;> by_cases h110 : k = 110 <;>
      simp [h136',h110,hoff 136 (by decide),h136]
  have hreadyFinal : LengthKeyReady (2^15*p) N q l s t u band 0 0 output Sfinal := hready.update_source output
  have hblank : ∀ k ∈ couplingHeaderRegisters, Sfinal.R k = [] := by
    intro k hk
    have hlow : k.val < 117 ∧ k ≠ 93 ∧ k ≠ 110 := by
      simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hreadyFinal.blank k hlow.1 hlow.2.1 hlow.2.2
  obtain ⟨v₅,hu₅,he₅⟩ := releaseCouplingHeaders_exec (body := embTab groupReg body)
    (2^15*p) q s t u band a b v₄ Sfinal hblank
  have he₄' : Exec (embTab groupReg body) (uclear 136) (mk v₃ S₃) (2*j.val+2)
      (mk v₄ {Sfinal with R := couplingHeadersR (2^15*p) q s t u band a b Sfinal.R}) := by
    have hh : Exec (embTab groupReg body) (uclear 136) (mk v₃ S₃) (2*j.val+2) (mk v₄ S₄) := by
      simpa [S₄,S₃,S₂] using he₄
    rw [hframe] at hh
    exact hh
  have ht := restoredOriginalColumn_trace_within hQ he₁ he₂' he₃ he₄' he₅
    (cap := restoredOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u a b j.val)
    (by unfold restoredOriginalColumnWorkspace; exact le_refl _)
  refine ⟨v₅,installCouplingHeadersCost (2^15*p) q s t u band a b+
    ((4*j.val+4)+(m₃+((2*j.val+2)+releaseCouplingHeadersCost (2^15*p) q s t u band a b))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    ht,hreal,hnorm,?_,hreadyFinal⟩
  · change _ ≤ installCouplingHeadersCost (2^15*p) q s t u band a b+(6*j.val+6)+
      (generatedOriginalColumnCost p q (2*q+8) s t u a b+releaseCouplingHeadersCost (2^15*p) q s t u band a b)
    omega
  · intro i
    change |publishedCellRead q (2*q+8) (0 : ZMod s) output i-realMatrix s t p u i j| ≤ _
    simpa [S₃,output,column,band] using herror i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
