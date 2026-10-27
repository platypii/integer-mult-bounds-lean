module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinateData
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Borrow the retained folded coordinate page and prepare ascending scatter coordinates in separate registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

def sharedPageCoordinateReg (i : Fin 224) : Fin 240 :=
  ⟨if i.val = 189 then 234 else if i.val = 191 then 235 else if i.val = 198 then 236 else
    if i.val = 204 then 238 else if i.val = 217 then 239 else
    if i.val = 160 then 115 else if i.val = 115 then 160 else i.val, by split_ifs <;> omega⟩

theorem sharedPageCoordinateReg_injective : Function.Injective sharedPageCoordinateReg := by
  intro i j h
  have hh := congrArg (fun k : Fin 240 => k.val) h
  apply Fin.ext
  dsimp only [sharedPageCoordinateReg] at hh
  split_ifs at hh <;> omega

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 240 Q A U}

def sharedPageBoundaryCoordinates : Pr P 240 Q A U :=
  .seq (unaryProduct 116 115 231 232 233)
    (.seq (copyPrefix 231 109 239 232 233)
      (.seq (embProg sharedPageCoordinateReg Empty.elim (generatedBoundaryUnfold (P := Empty))) (uclear 231)))

def sharedPageBoundaryCoordinatesCost (N V : ℕ) : ℕ :=
  generatedBoundaryUnfoldCost N V+N*(16*V+9)+16

theorem sharedPageBoundaryCoordinates_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (V : ℕ)
    (v : HS 240 Q A U) (S : Stacks 240 A)
    (hleft : ∀ i, S.L i = [])
    (hmul : ∀ i : Fin 64, (embStk sharedPageCoordinateReg S).R (boundaryFactorMulReg i) = [])
    (hcount : (S.R 116).length = B.card) (hw : (S.R 115).length = V)
    (hsource : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))))
    (h239 : S.R 239 = []) (h231 : S.R 231 = []) (h232 : S.R 232 = []) (h233 : S.R 233 = [])
    (hclean : ∀ i ∈ ([234,235,184,223,238,208,211,236,201,215] : List (Fin 240)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPageBoundaryCoordinatesCost B.card V ∧
      Exec body sharedPageBoundaryCoordinates (mk v S) n
        (mk v' {S with R := (Function.update S.R 238 (cstream A V ((bOrder s B).map
          (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}) := by
  let coordinates := (bFoldOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))
  let raw := cstream A V coordinates
  let output := cstream A V (unfoldList coordinates)
  have hlen : coordinates.length = B.card := by simp [coordinates,bFoldOrder_length]
  have hraw : raw.length = B.card*V := by simp [raw,hlen]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 116) (b := 115) (dst := 231) (t₁ := 232) (t₂ := 233) (by decide) v S h232 h233
  let S₁ : Stacks 240 A := {S with R := Function.update S.R 231 (List.replicate (B.card*V) tick)}
  have he₁' : Exec body (unaryProduct 116 115 231 232 233) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hcount,hw,h231,List.append_nil] using he₁
  have hn₁' : n₁ ≤ B.card*(4*V+9)+4 := by simpa only [hcount,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body) (count := 231) (src := 109) (dst := 239)
    (saved := 232) (tmp := 233) (by decide) v₁ S₁ raw []
    (by simpa [S₁,raw,coordinates] using hsource) (by simp [S₁,hraw])
    (by simpa [S₁] using h232) (by simpa [S₁] using h233)
  let S₂ : Stacks 240 A := {S₁ with R := Function.update S₁.R 239 raw}
  have he₂' : Exec body (copyPrefix 231 109 239 232 233) (mk v₁ S₁) (10*raw.length+10) (mk v₂ S₂) := by
    simpa only [S₂,S₁,Function.update_of_ne (by decide : (239 : Fin 240) ≠ 231),h239,List.append_nil] using he₂
  let T := embStk sharedPageCoordinateReg S₂
  have hm : ∀ i : Fin 64, T.R (boundaryFactorMulReg i) = [] := by
    intro i
    have hr : sharedPageCoordinateReg (boundaryFactorMulReg i) = ⟨i.val,by omega⟩ := by
      apply Fin.ext
      have hi := i.isLt
      dsimp [sharedPageCoordinateReg,boundaryFactorMulReg]
      split_ifs <;> omega
    have hi239 : (⟨i.val,by omega⟩ : Fin 240) ≠ 239 := by apply Fin.ne_of_val_ne; have hi := i.isLt; dsimp; omega
    have hi231 : (⟨i.val,by omega⟩ : Fin 240) ≠ 231 := by apply Fin.ne_of_val_ne; have hi := i.isLt; dsimp; omega
    simpa only [T,embStk,Function.comp_def,hr,S₂,S₁,Function.update_of_ne hi239,Function.update_of_ne hi231] using hmul i
  have hc : ∀ i ∈ ([189,191,184,223,204,208,211,198,201,215] : List (Fin 224)), T.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [T,S₂,S₁,embStk,sharedPageCoordinateReg] using hclean _ (by simp)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := generatedBoundaryUnfold_exec (body := fun p : Empty => nomatch p)
    V coordinates (embDn sharedPageCoordinateReg v₂) T (fun i => hleft _) hm
    (by simpa [T,S₂,S₁,embStk,sharedPageCoordinateReg,hlen] using hcount)
    (by simp [T,S₂,embStk,sharedPageCoordinateReg,raw])
    (by simpa [T,S₂,S₁,embStk,sharedPageCoordinateReg] using hw) hc
  obtain ⟨v₃',hv₃',hu₃',he₃'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedPageCoordinateReg_injective (fun p => nomatch p) he₃ v₂ rfl S₂ rfl
  let S₃ : Stacks 240 A := {S₂ with R := Function.update (Function.update S₂.R 239 []) 238 output}
  have he₃'' : Exec body (embProg sharedPageCoordinateReg Empty.elim (generatedBoundaryUnfold (P := Empty)))
      (mk v₂ S₂) n₃ (mk v₃' S₃) := by
    convert he₃' using 1
    apply congrArg (mk v₃')
    symm
    let T₀ : Stacks 224 A := {T with R := Function.update T.R 217 []}
    change embOvr sharedPageCoordinateReg ({T₀ with R := Function.update T₀.R 204 output} : Stacks 224 A).get S₂ = S₃
    rw [embOvr_updR sharedPageCoordinateReg_injective]
    dsimp only [T₀]
    rw [embOvr_updR sharedPageCoordinateReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec body 231 v₃' S₃
  have hclock : (S₃.R 231).length = B.card*V := by simp [S₃,S₂,S₁]
  refine ⟨v₄,n₁+((10*raw.length+10)+(n₃+(2*(S₃.R 231).length+2))),
    hu₄.trans (hu₃'.trans (hu₃.trans (hu₂.trans hu₁))),?_,(Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃'' he₄))).cast rfl ?_⟩
  · rw [hraw,hclock,hlen] at *
    dsimp only [sharedPageBoundaryCoordinatesCost]
    nlinarith only [hn₁',hn₃]
  · apply congrArg (mk v₄)
    have hout : output = cstream A V ((bOrder s B).map (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) := by
      dsimp only [output,coordinates]
      rw [boundary_unfold_coordinates]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi239 : i = 239 <;> by_cases hi231 : i = 231 <;> by_cases hi238 : i = 238 <;>
      simp [S₃,S₂,S₁,hi239,hi231,hi238,h239,h231,hout]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
