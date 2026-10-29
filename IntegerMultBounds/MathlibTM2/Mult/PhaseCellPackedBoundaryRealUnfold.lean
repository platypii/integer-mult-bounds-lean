module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMoveCountedLine

/-! Separate inverse-fold counters from the prepared factor page so recovery can reuse that page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- The factor placement with four inverse-fold temporaries moved to fresh ports.
Permutations make injectivity structural rather than a case enumeration. -/
def packedBoundaryUnfoldReg (i : Fin 224) : Fin 248 :=
  Equiv.swap 218 245 (Equiv.swap 212 244 (Equiv.swap 205 243 (Equiv.swap 203 242
    (Fin.castLE (by decide : 242 ≤ 248)
      (packedBoundaryFactorReg (Fin.castLE (by decide : 224 ≤ 226) i))))))

theorem packedBoundaryUnfoldReg_injective : Function.Injective packedBoundaryUnfoldReg := by
  intro i j h
  have h₁ := (Equiv.swap 218 245).injective h
  have h₂ := (Equiv.swap 212 244).injective h₁
  have h₃ := (Equiv.swap 205 243).injective h₂
  have h₄ := (Equiv.swap 203 242).injective h₃
  have h₅ : packedBoundaryFactorReg (Fin.castLE (by decide : 224 ≤ 226) i) =
      packedBoundaryFactorReg (Fin.castLE (by decide : 224 ≤ 226) j) :=
    Fin.ext (congrArg (fun k : Fin 248 => k.val) h₄)
  have h₆ := packedBoundaryFactorReg_injective h₅
  apply Fin.ext
  exact congrArg (fun k : Fin 226 => k.val) h₆

theorem packedBoundaryUnfoldReg_low (i : Fin 224) (hi : i.val < 64) :
    packedBoundaryUnfoldReg i = Fin.castLE (by decide : 224 ≤ 248) i := by
  have h140 : i.val ≠ 140 := by omega
  have h143 : i.val ≠ 143 := by omega
  have h206 : i.val ≠ 206 := by omega
  simp [packedBoundaryUnfoldReg,packedBoundaryFactorReg,Fin.ext_iff,
    Equiv.swap_apply_def,h140,h143,h206,show i.val < 154 by omega,
    show i.val ≠ 203 by omega,show i.val ≠ 242 by omega,
    show i.val ≠ 205 by omega,show i.val ≠ 243 by omega,
    show i.val ≠ 212 by omega,show i.val ≠ 244 by omega,
    show i.val ≠ 218 by omega,show i.val ≠ 245 by omega]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedBoundaryRealUnfold : Pr P 248 Q A U :=
  embProg packedBoundaryUnfoldReg Empty.elim (generatedBoundaryRealUnfold (P := Empty))

theorem packedBoundaryRealUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryUnfoldReg S).L i = [])
    (hmul : ∀ i : Fin 64, (embStk packedBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hsrc : S.R 231 = cstream A w solution)
    (hw : (S.R 174).length = w)
    (hclean : ∀ i ∈ ([242,243,198,237,245,222,225,244,215,229] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12 ∧
      Exec body packedBoundaryRealUnfold (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 231 []) 245
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  let T := embStk packedBoundaryUnfoldReg S
  have hcleanT : ∀ i ∈ ([189,191,184,223,204,208,211,198,201,215] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hclean _ (by decide)
  obtain ⟨v₁,n,hu₁,hn,he⟩ := generatedBoundaryRealUnfold_exec (body := fun p : Empty => nomatch p) hA w B solution hlen
    (embDn packedBoundaryUnfoldReg v) T hleft hmul hcount hsrc hw hcleanT
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedBoundaryUnfoldReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,?_,he₂.cast rfl ?_⟩
  · omega
  · apply congrArg (mk v₂)
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 217 []}
    change embOvr packedBoundaryUnfoldReg
      ({T₀ with R := (Function.update T₀.R 204
        (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))} : Stacks 224 A).get S = _
    rw [embOvr_updR packedBoundaryUnfoldReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR packedBoundaryUnfoldReg_injective,embOvr_stk]
    rfl

/-- Consume only the solver-owned prefix before inverse folding. -/
def packedBoundarySolutionUnfold : Pr P 248 Q A U :=
  .seq (ScalarPlacement.moveCountedLine 116 174 238 231 239 246 247 143)
    packedBoundaryRealUnfold

theorem packedBoundarySolutionUnfold_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A) (w : ℕ)
    (B : Finset (ZMod s)) (solution : List GaussianInt) (hlen : solution.length = B.card)
    (tail : List (Fin (A+4))) (v : HS 248 Q A U) (S : Stacks 248 A)
    (hleft : ∀ i : Fin 224, (embStk packedBoundaryUnfoldReg S).L i = [])
    (hmul : ∀ i : Fin 64, (embStk packedBoundaryUnfoldReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hsrc : S.R 238 = cstream A w solution ++ tail)
    (hw : (S.R 174).length = w)
    (hclean : ∀ i ∈ ([231,239,246,247,143,242,243,198,237,245,222,225,244,215,229] :
      List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ ScalarPlacement.moveCountedLineCost B.card w +
        (generatedBoundaryUnfoldCost B.card w+B.card*(12*w+9)+12) ∧
      Exec body packedBoundarySolutionUnfold (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          238 tail) 231 []) 245
          (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := ScalarPlacement.moveCountedLine_exec (body := body)
    116 174 238 231 239 246 247 143 (by decide) B.card w
    (cstream A w solution) tail (by simp only [length_cstream,hlen]) v S
    hcount hw hsrc (hclean 239 (by simp)) (hclean 246 (by simp))
    (hclean 247 (by simp)) (hclean 143 (by simp))
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update S.R
    238 tail) 231 (cstream A w solution))}
  have he₁' : Exec body (ScalarPlacement.moveCountedLine 116 174 238 231 239 246 247 143)
      (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hclean 231 (by simp),List.append_nil] using he₁
  have hmul₁ : ∀ i : Fin 64,
      (embStk packedBoundaryUnfoldReg S₁).R (boundaryFactorMulReg i) = [] := by
    intro i
    have hi : (boundaryFactorMulReg i).val < 64 := i.isLt
    have hr := packedBoundaryUnfoldReg_low (boundaryFactorMulReg i) hi
    have h := hmul i
    change S.R (packedBoundaryUnfoldReg (boundaryFactorMulReg i)) = [] at h
    change S₁.R (packedBoundaryUnfoldReg (boundaryFactorMulReg i)) = []
    rw [hr] at h ⊢
    simpa [S₁,Function.update_apply,Fin.ext_iff,boundaryFactorMulReg,
      show i.val ≠ 231 by omega,show i.val ≠ 238 by omega] using h
  have hclean₁ : ∀ i ∈ ([242,243,198,237,245,222,225,244,215,229] : List (Fin 248)),
      S₁.R i = [] := by
    intro i hi
    have hc := hclean i (List.mem_append_right [231,239,246,247,143] hi)
    have h231 : i ≠ 231 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h238 : i ≠ 238 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,Function.update_of_ne h231,Function.update_of_ne h238] using hc
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedBoundaryRealUnfold_exec (body := body) hA w B
    solution hlen v₁ S₁ hleft hmul₁ (by simpa [S₁] using hcount)
    (by simp [S₁]) (by simpa [S₁] using hw) hclean₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h231 : i = 231 <;> by_cases h245 : i = 245 <;>
    simp [S₁,h231,h245]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
