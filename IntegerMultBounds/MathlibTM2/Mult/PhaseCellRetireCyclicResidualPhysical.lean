module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCyclicResiduals
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Retire residual prefixes in the physical factor bank without changing its solved state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

def cyclicResidualRetireReg (i : Fin 151) : Fin 224 := ⟨i.val,by omega⟩

theorem cyclicResidualRetireReg_injective : Function.Injective cyclicResidualRetireReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 224 => k.val) h)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def retireCyclicResidualPhysical : Pr P 224 Q A U :=
  embProg cyclicResidualRetireReg Empty.elim (retireCyclicResiduals (P := Empty))

theorem retireCyclicResidualPhysical_exec (q s : ℕ) (right left tail : List (Fin (A+4)))
    (hR : right.length = s*(2*q+8)) (hL : left.length = s*(2*q+8))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (hsrc : S.R 132 = right++(left++tail))
    (hfresh : ∀ k ∈ [(94 : Fin 224),131,134,135,138], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireCyclicResidualsCost q s ∧
      Exec body retireCyclicResidualPhysical (mk v S) m
        (mk v' {S with R := Function.update S.R 132 tail}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := retireCyclicResiduals_exec (body := fun e : Empty => nomatch e)
    q s right left tail hR hL (embDn cyclicResidualRetireReg v) (embStk cyclicResidualRetireReg S)
    hq hs hsrc (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [embStk,cyclicResidualRetireReg] using hfresh _ (by simp))
  obtain ⟨vf,_,hv,hf⟩ := exec_emb_ovr (e := cyclicResidualRetireReg) (ι := Empty.elim) (body' := body)
    cyclicResidualRetireReg_injective (fun e => nomatch e) he v rfl S rfl
  refine ⟨vf,m,hv.trans hu,hm,hf.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR cyclicResidualRetireReg_injective (embStk cyclicResidualRetireReg S) S 132 tail,embOvr_stk]
  rfl

theorem boundaryFactorState_update_accumulator {A : ℕ} (S : Stacks 224 A) (tail : List (Fin (A+4))) :
    boundaryFactorState {S with R := Function.update S.R 132 tail} = boundaryFactorState S := by
  funext r
  exact Function.update_of_ne (boundaryFactorReg_off r 132 (by decide)) _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
