module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocateZeroLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloBufferRelease

/-! Prepare the local solver's zero output from retained precision and core
headers, releasing every temporary header before entering the solver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 256 Q A U}

def prepareHaloBuffer : Pr P 256 Q A U :=
  .seq (generateWordWidth 119 254 104) (.seq prepareCoreHaloCount
    (.seq (allocateZeroLine 255 254 132 253 104 105) (clearWords [254,255])))

def prepareHaloBufferCost (q rows radius : ℕ) : ℕ :=
  (8*q+9)+(4*rows+8*radius+12)+allocateZeroLineCost (rows+2*radius) (2*q+8)+
    2*((2*q+8)+(rows+2*radius))+5

theorem prepareHaloBuffer_exec (q rows radius : ℕ) (v : HS 256 Q A U) (S : Stacks 256 A)
    (hq : (S.R 119).length = q) (hrows : (S.R 250).length = rows)
    (hradius : (S.R 249).length = radius)
    (hfresh : ∀ i ∈ ([104,105,253,254,255] : List (Fin 256)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloBufferCost q rows radius ∧
      Exec body prepareHaloBuffer (mk v S) n
        (mk v' {S with R := (Function.update S.R 132
          (cstream A (2*q+8) (List.replicate (rows+2*radius) 0)++S.R 132))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body) (precision := 119) (width := 254)
    (tmp := 104) (by decide) q v S hq (hfresh 254 (by decide)) (hfresh 104 (by decide))
  let S₁ : Stacks 256 A := {S with R := Function.update S.R 254 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := prepareCoreHaloCount_exec (body := body) rows radius v₁ S₁
    (by simpa [S₁] using hrows) (by simpa [S₁] using hradius)
    (by simpa [S₁] using hfresh 255 (by decide)) (by simpa [S₁] using hfresh 104 (by decide))
  let S₂ : Stacks 256 A := {S₁ with R := Function.update S₁.R 255 (List.replicate (rows+2*radius) tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := allocateZeroLine_exec (body := body)
    255 254 132 253 104 105 (by decide) (rows+2*radius) (2*q+8) v₂ S₂
    (by simp [S₂]) (by simp [S₂,S₁]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> simpa [S₂,S₁] using hfresh _ (by decide))
  let E := cstream A (2*q+8) (List.replicate (rows+2*radius) (0 : GaussianInt))
  let S₃ : Stacks 256 A := {S₂ with R := Function.update S₂.R 132 (E++S.R 132)}
  have he₃' : Exec body (allocateZeroLine 255 254 132 253 104 105) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,E] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [254,255] (by decide) v₃ S₃
  have hclear : 2*(([(254 : Fin 256),255].map fun i => (S₃.R i).length).sum)+2*[(254 : Fin 256),255].length+1 =
      2*((2*q+8)+(rows+2*radius))+5 := by simp [S₃,S₂,S₁]
  refine ⟨v₄,(8*q+9)+((4*rows+8*radius+12)+(n₃+(2*((2*q+8)+(rows+2*radius))+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))).cast (by rw [hclear]) ?_⟩
  · dsimp only [prepareHaloBufferCost]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h254 : i = 254 <;> by_cases h255 : i = 255 <;> by_cases h132 : i = 132 <;>
      simp [S₃,S₂,S₁,E,h254,h255,h132,hfresh 254 (by decide),hfresh 255 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
