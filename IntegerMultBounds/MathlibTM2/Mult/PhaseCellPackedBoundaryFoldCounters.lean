module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldCounters
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Reuse the fold counter generator at the retained numerical RHS width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedBoundaryFoldCounterReg (i : Fin 117) : Fin 168 :=
  if i = 115 then 130 else ⟨i.val,by omega⟩

theorem packedBoundaryFoldCounterReg_injective : Function.Injective packedBoundaryFoldCounterReg := by
  intro i j he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  have hj := j.isLt
  unfold packedBoundaryFoldCounterReg at hv
  split_ifs at hv <;> simp_all only
  all_goals omega

@[simp] theorem packedBoundaryFoldCounterReg_zero : packedBoundaryFoldCounterReg 0 = 0 := by norm_num [packedBoundaryFoldCounterReg]
@[simp] theorem packedBoundaryFoldCounterReg_two : packedBoundaryFoldCounterReg 2 = 2 := by norm_num [packedBoundaryFoldCounterReg]
@[simp] theorem packedBoundaryFoldCounterReg_three : packedBoundaryFoldCounterReg 3 = 3 := by norm_num [packedBoundaryFoldCounterReg]
@[simp] theorem packedBoundaryFoldCounterReg_width : packedBoundaryFoldCounterReg 115 = 130 := by norm_num [packedBoundaryFoldCounterReg]
@[simp] theorem packedBoundaryFoldCounterReg_count : packedBoundaryFoldCounterReg 116 = 116 := by norm_num [packedBoundaryFoldCounterReg]

def packedBoundaryFoldCounters : Pr P 168 Q A U :=
  embProg packedBoundaryFoldCounterReg Empty.elim (boundaryFoldCounters (P₀ := Empty))

theorem packedBoundaryFoldCounters_exec (n w : ℕ) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hn : (S.R 116).length = n) (hw : (S.R 130).length = w)
    (hblank : ∀ r : Fin 168, r.val < 6 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryFoldCountersCost n w ∧
      Exec body packedBoundaryFoldCounters (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
          3 (List.replicate (((n+1)/2)*w) tick))}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := boundaryFoldCounters_exec (body := fun p : Empty => nomatch p) n w
    (embDn packedBoundaryFoldCounterReg v) (embStk packedBoundaryFoldCounterReg S)
    (by simpa [embStk] using hn) (by simpa [embStk] using hw) (by
      intro r hr
      have hn : r ≠ 115 := by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
      simpa [embStk,packedBoundaryFoldCounterReg,hn] using hblank ⟨r.val,by omega⟩ hr)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    packedBoundaryFoldCounterReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let T₀ := embStk packedBoundaryFoldCounterReg S
  let T₁ : Stacks 117 A := {T₀ with R := Function.update T₀.R 0 (List.replicate (n/2) tick)}
  let T₂ : Stacks 117 A := {T₁ with R := Function.update T₁.R 2 (List.replicate ((n+1)/2-n/2) tick)}
  let T₃ : Stacks 117 A := {T₂ with R := Function.update T₂.R 3 (List.replicate (((n+1)/2)*w) tick)}
  change embOvr packedBoundaryFoldCounterReg T₃.get S = _
  dsimp only [T₃]
  rw [embOvr_updR packedBoundaryFoldCounterReg_injective]
  dsimp only [T₂]
  rw [embOvr_updR packedBoundaryFoldCounterReg_injective]
  dsimp only [T₁,T₀]
  rw [embOvr_updR packedBoundaryFoldCounterReg_injective,embOvr_stk]
  simp only [packedBoundaryFoldCounterReg_zero,packedBoundaryFoldCounterReg_two,packedBoundaryFoldCounterReg_three]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
