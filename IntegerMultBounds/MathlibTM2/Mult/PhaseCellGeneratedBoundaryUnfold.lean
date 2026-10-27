module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnfoldCounters

/-! Generate and retire inverse-fold controls around the actual physical execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def generatedBoundaryUnfold : Pr P 224 Q A U :=
  .seq boundaryUnfoldCounters (.seq (bandUnfoldLineP boundaryFactorReg) (clearWords [189,191]))

def generatedBoundaryUnfoldCost (N w : ℕ) : ℕ :=
  (16*N+22)+(60*(N+1)*w+60*N+60+(2*N+5))

theorem generatedBoundaryUnfold_exec (w : ℕ) (solution : List GaussianInt)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = solution.length) (hsrc : S.R 217 = cstream A w solution)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([189,191,184,223,204,208,211,198,201,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedBoundaryUnfoldCost solution.length w ∧
      Exec body generatedBoundaryUnfold (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 217 []) 204
          (cstream A w (unfoldList solution)))}) := by
  let N := solution.length
  let floor := List.replicate (N/2) (tick : Fin (A+4))
  let parity := List.replicate ((N+1)/2-N/2) (tick : Fin (A+4))
  let S₁ : Stacks 224 A := {S with R := Function.update (Function.update S.R 189 floor) 191 parity}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryUnfoldCounters_exec (body := body) N v S hcount
    (hclean 189 (by simp)) (hclean 184 (by simp)) (hclean 191 (by simp)) (hclean 223 (by simp))
  have hmul₁ : ∀ i : Fin 64, S₁.R (boundaryFactorMulReg i) = [] := by
    intro i
    have h189 : boundaryFactorMulReg i ≠ 189 := by
      intro h
      have hv := congrArg (fun j : Fin 224 => j.val) h
      change i.val = 189 at hv
      omega
    have h191 : boundaryFactorMulReg i ≠ 191 := by
      intro h
      have hv := congrArg (fun j : Fin 224 => j.val) h
      change i.val = 191 at hv
      omega
    simpa [S₁,h189,h191] using hmul i
  have hc : ∀ i ∈ ([204,208,211,198,201,215] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have ho : i ≠ 189 ∧ i ≠ 191 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,ho.1,ho.2] using hclean i (by simp_all)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundary_unfold_physical_exec (body := body) w solution v₁ S₁
    hleft hmul₁ (by simpa [S₁] using hsrc) (by simp [S₁,floor,N])
    (by simp [S₁,parity,N]) (by simpa [S₁] using hw) hc
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update S₁.R 217 []) 204
    (cstream A w (unfoldList solution)))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [189,191] (by decide) v₂ S₂
  have hcost : 2*(([189,191] : List (Fin 224)).map fun r => (S₂.R r).length).sum+2*2+1 ≤ 2*N+5 := by
    simp [S₂,S₁,floor,parity]
    omega
  refine ⟨v₃,n₁+(n₂+_),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add hn₁ (Nat.add_le_add hn₂ hcost),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h189 : i = 189 <;> by_cases h191 : i = 191 <;>
    by_cases h217 : i = 217 <;> by_cases h204 : i = 204 <;>
    simp [S₂,S₁,h189,h191,h217,h204,hclean 189 (by simp),hclean 191 (by simp)]

/-- Retire obsolete factor headers and unfold into a fresh natural-order destination. -/
def preparedBoundaryUnfold : Pr P 224 Q A U :=
  .seq (clearWords [189,191,198,204]) generatedBoundaryUnfold

theorem preparedBoundaryUnfold_exec (w : ℕ) (solution : List GaussianInt)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = solution.length) (hsrc : S.R 217 = cstream A w solution)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S.R i = []) :
    let retired : List (Fin 224) := [189,191,198,204]
    let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (2*(retired.map fun i => (S.R i).length).sum+9)+generatedBoundaryUnfoldCost solution.length w ∧
      Exec body preparedBoundaryUnfold (mk v S) n
        (mk v' {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
          (cstream A w (unfoldList solution)))}) := by
  dsimp only
  let retired : List (Fin 224) := [189,191,198,204]
  let S₀ : Stacks 224 A := {S with R := fun i => if i ∈ retired then [] else S.R i}
  obtain ⟨v₁,hu₁,he₁⟩ := clearWords_exec (body := body) retired (by decide) v S
  have hm : ∀ i : Fin 64, S₀.R (boundaryFactorMulReg i) = [] := by
    intro i
    have hoff : boundaryFactorMulReg i ∉ retired := by
      simp only [retired,List.mem_cons,List.not_mem_nil,or_false]
      have hlt := i.isLt
      change ¬(boundaryFactorMulReg i = 189 ∨ boundaryFactorMulReg i = 191 ∨
        boundaryFactorMulReg i = 198 ∨ boundaryFactorMulReg i = 204)
      intro h
      rcases h with h | h | h | h <;>
        have hv := congrArg (fun j : Fin 224 => j.val) h <;>
        change i.val = _ at hv <;> omega
    simpa [S₀,hoff] using hmul i
  have hc : ∀ i ∈ ([189,191,184,223,204,208,211,198,201,215] : List (Fin 224)), S₀.R i = [] := by
    intro i hi
    by_cases hr : i ∈ retired
    · simp [S₀,hr]
    · have hi' : i ∈ ([184,223,208,211,201,215] : List (Fin 224)) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
        simp only [retired,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
        tauto
      simpa [S₀,hr] using hclean i hi'
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generatedBoundaryUnfold_exec (body := body) w solution v₁ S₀
    hleft hm (by simpa [S₀,retired] using hcount) (by simpa [S₀,retired] using hsrc)
    (by simpa [S₀,retired] using hw) hc
  refine ⟨v₂,_,hu₂.trans hu₁,Nat.add_le_add_left hn₂ _,?_⟩
  simpa [preparedBoundaryUnfold,retired,S₀,Nat.add_assoc] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
