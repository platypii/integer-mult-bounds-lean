module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire the final ambient residual and release the owned boundary workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryOwnedRegs : List (Fin 224) :=
  [115,116]++(List.finRange 224).filter (fun i => 154 ≤ i.val)

@[simp] theorem boundaryOwnedRegs_mem (i : Fin 224) :
    i ∈ boundaryOwnedRegs ↔ i = 115 ∨ i = 116 ∨ 154 ≤ i.val := by
  simp [boundaryOwnedRegs]

def releaseBoundaryWorkspace : Pr P 224 Q A U :=
  .seq (unaryProduct 121 160 131 134 135)
    (.seq (discardPrefix 131 110 134 135) (.seq (uclear 131) (clearWords boundaryOwnedRegs)))

def releaseBoundaryWorkspaceCost (s w : ℕ) (S : Stacks 224 A) : ℕ :=
  12*s*w+9*s+12+2*(boundaryOwnedRegs.map fun i => (S.R i).length).sum+
    2*boundaryOwnedRegs.length+1

theorem releaseBoundaryWorkspace_exec (s w : ℕ) (raw tail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 121).length = s) (hw : (S.R 160).length = w)
    (hsource : S.R 110 = raw++tail) (hlen : raw.length = s*w)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseBoundaryWorkspaceCost s w S ∧
      Exec body releaseBoundaryWorkspace (mk v S) m
        (mk v' {S with R := fun i => if i ∈ boundaryOwnedRegs then [] else (Function.update S.R 110 tail) i}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 160) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 160 131 134 135) (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hm₁' : m₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hm₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 131) (src := 110) (trash := 134) (tmp := 135) (by decide) raw tail v₁ S₁
    (by simpa [S₁] using hsource) (by simp [S₁,hlen])
    (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 110 tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 131 v₂ S₂
  let S₃ : Stacks 224 A := {S with R := Function.update S.R 110 tail}
  have he₃' : Exec body (uclear 131) (mk v₂ S₂) (2*(s*w)+2) (mk v₃ S₃) := by
    convert he₃ using 1
    · simp [S₂,S₁]
    · apply congrArg (mk v₃)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases h131' : i = 131 <;> by_cases h110 : i = 110 <;> simp [S₃,S₂,S₁,h131',h110,h131]
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) boundaryOwnedRegs (by decide) v₃ S₃
  have hsum : (boundaryOwnedRegs.map fun i => (S₃.R i).length).sum =
      (boundaryOwnedRegs.map fun i => (S.R i).length).sum := by
    have hmap : (boundaryOwnedRegs.map fun i => (S₃.R i).length) =
        (boundaryOwnedRegs.map fun i => (S.R i).length) := List.map_congr_left (fun i hi => by
      have hi110 : i ≠ 110 := by rw [boundaryOwnedRegs_mem] at hi; rcases hi with rfl | rfl | hi <;> simp_all [Fin.ext_iff] <;> omega
      simp [S₃,hi110])
    exact congrArg List.sum hmap
  refine ⟨v₄,m₁+((6*raw.length+6)+((2*(s*w)+2)+
    (2*(boundaryOwnedRegs.map fun i => (S.R i).length).sum+2*boundaryOwnedRegs.length+1))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast (by rw [hsum]) rfl⟩
  dsimp only [releaseBoundaryWorkspaceCost]
  rw [hlen]
  nlinarith only [hm₁']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
