module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Reuse the fold counter generator at the retained numerical RHS width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def boundaryRhsCounterReg (i : Fin 117) : Fin 148 := Equiv.swap 115 94 ⟨i.val,by omega⟩

theorem boundaryRhsCounterReg_injective : Function.Injective boundaryRhsCounterReg := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun r : Fin 148 => r.val) ((Equiv.injective (Equiv.swap (115 : Fin 148) 94)) hij)

@[simp] theorem boundaryRhsCounterReg_zero : boundaryRhsCounterReg 0 = 0 := by norm_num [boundaryRhsCounterReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsCounterReg_two : boundaryRhsCounterReg 2 = 2 := by norm_num [boundaryRhsCounterReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsCounterReg_three : boundaryRhsCounterReg 3 = 3 := by norm_num [boundaryRhsCounterReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsCounterReg_width : boundaryRhsCounterReg 115 = 94 := by norm_num [boundaryRhsCounterReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsCounterReg_count : boundaryRhsCounterReg 116 = 116 := by norm_num [boundaryRhsCounterReg,Equiv.swap_apply_def]

def boundaryRhsFoldCounters : Pr P 148 Q A U :=
  embProg boundaryRhsCounterReg Empty.elim (boundaryFoldCounters (P₀ := Empty))

theorem boundaryRhsFoldCounters_exec (n w : ℕ) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hn : (S.R 116).length = n) (hw : (S.R 94).length = w)
    (hblank : ∀ r : Fin 148, r.val < 6 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryFoldCountersCost n w ∧
      Exec body boundaryRhsFoldCounters (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
          3 (List.replicate (((n+1)/2)*w) tick))}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := boundaryFoldCounters_exec (body := fun p : Empty => nomatch p) n w
    (embDn boundaryRhsCounterReg v) (embStk boundaryRhsCounterReg S)
    (by simpa [embStk] using hn) (by simpa [embStk] using hw) (by
      intro r hr
      have h115 : (⟨r.val,by omega⟩ : Fin 148) ≠ 115 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
      have h94 : (⟨r.val,by omega⟩ : Fin 148) ≠ 94 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
      simpa [embStk,boundaryRhsCounterReg,Equiv.swap_apply_def,h115,h94] using hblank ⟨r.val,by omega⟩ hr)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    boundaryRhsCounterReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T₀ := embStk boundaryRhsCounterReg S
  let T₁ : Stacks 117 A := {T₀ with R := Function.update T₀.R 0 (List.replicate (n/2) tick)}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 2 (List.replicate ((n+1)/2-n/2) tick)}
  let T₃ : Stacks 117 A := {T₂ with R := Function.update T₂.R 3 (List.replicate (((n+1)/2)*w) tick)}
  change embOvr boundaryRhsCounterReg T₃.get S = _
  dsimp only [T₃]
  rw [embOvr_updR boundaryRhsCounterReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR boundaryRhsCounterReg_injective]
  dsimp only [T₁,T₀]
  rw [embOvr_updR boundaryRhsCounterReg_injective,embOvr_stk]
  simp only [boundaryRhsCounterReg_zero,boundaryRhsCounterReg_two,boundaryRhsCounterReg_three]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
