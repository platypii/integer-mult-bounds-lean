module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryRealUnfold

/-! Separate inverse-fold counters from the prepared factor page so recovery can reuse that page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

def sharedPageBoundaryUnfoldReg (i : Fin 224) : Fin 238 :=
  ⟨if i.val = 189 then 234 else if i.val = 191 then 235 else
    if i.val = 198 then 236 else if i.val = 204 then 237 else i.val, by
    split_ifs <;> omega⟩

theorem sharedPageBoundaryUnfoldReg_injective : Function.Injective sharedPageBoundaryUnfoldReg := by
  intro i j h
  have hh := congrArg (fun k : Fin 238 => k.val) h
  apply Fin.ext
  dsimp only [sharedPageBoundaryUnfoldReg] at hh
  split_ifs at hh <;> omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def sharedPageBoundaryRealUnfold : Pr P 238 Q A U :=
  embProg sharedPageBoundaryUnfoldReg id generatedBoundaryRealUnfold

theorem sharedPageBoundaryRealUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 238 Q A U) (S : Stacks 238 A)
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hsrc : S.R 217 = cstream A w solution)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([234,235,184,223,237,208,211,236,201,215] : List (Fin 238)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12 ∧
      Exec (embTab sharedPageBoundaryUnfoldReg body) sharedPageBoundaryRealUnfold (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 217 []) 237
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  let T := embStk sharedPageBoundaryUnfoldReg S
  have hcleanT : ∀ i ∈ ([189,191,184,223,204,208,211,198,201,215] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by simp [sharedPageBoundaryUnfoldReg])
  obtain ⟨v₁,n,hu₁,hn,he⟩ := generatedBoundaryRealUnfold_exec (body := body) hA w B solution hlen
    (embDn sharedPageBoundaryUnfoldReg v) T (fun i => hleft _) hmul hcount hsrc hw hcleanT
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab sharedPageBoundaryUnfoldReg body)
    sharedPageBoundaryUnfoldReg_injective (fun _ => rfl) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,?_,he₂.cast rfl ?_⟩
  · omega
  · apply congrArg (mk v₂)
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 217 []}
    change embOvr sharedPageBoundaryUnfoldReg
      ({T₀ with R := (Function.update T₀.R 204
        (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))} : Stacks 224 A).get S = _
    rw [embOvr_updR sharedPageBoundaryUnfoldReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR sharedPageBoundaryUnfoldReg_injective,embOvr_stk]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
