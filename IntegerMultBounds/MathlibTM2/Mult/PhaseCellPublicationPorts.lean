module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMerge
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Separate the two owned lines and generate the selector's count from retained headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

def publicationSplit : Pr P₀ 144 Q A U :=
  .seq (unaryProduct 121 94 131 134 135)
    (.seq (transfer 131 132 136 134) (.seq (moveR 136 137 id) (uclear 131)))

def publicationSplitCost (s w : ℕ) : ℕ := 12*s*w+9*s+12

theorem publicationSplit_exec (s w : ℕ) (raw tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 132 = raw++tail) (hlen : raw.length = s*w)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h136 : S.R 136 = []) (h137 : S.R 137 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ publicationSplitCost s w ∧
      Exec body publicationSplit (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 132 tail) 137 raw)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 121) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S h134 h135
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 131 (List.replicate (s*w) tick)}
  have he₁' : Exec body (unaryProduct 121 94 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hs,hw,h131] using he₁
  have hn₁' : n₁ ≤ s*(4*w+9)+4 := by simpa [hs,hw] using hn₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := 131) (src := 132) (dst := 136) (tmp := 134)
    (by decide) v₁ S₁ raw tail (by simpa [S₁] using hsrc) (by simp [S₁,hlen]) (by simpa [S₁] using h134)
  let S₂ : Stacks 144 A := {S₁ with R := (Function.update (Function.update S₁.R 132 tail) 136 raw.reverse)}
  have he₂' : Exec body (transfer 131 132 136 134) (mk v₁ S₁) (4*raw.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,h136] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 136 137 (by decide) id v₂ S₂
  let S₃ : Stacks 144 A := {S₂ with R := movedR S₂.R 136 137 id (S₂.R 136)}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 131 v₃ S₃
  refine ⟨v₄,n₁+((4*raw.length+4)+((2*raw.length+2)+(2*(s*w)+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,(Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · rw [hlen]
    dsimp only [publicationSplitCost] at *
    nlinarith only [hn₁']
  · simp [S₃,S₂,S₁,movedR,hlen]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk131 : k = 131 <;> by_cases hk136 : k = 136 <;> by_cases hk137 : k = 137 <;>
      by_cases hk132 : k = 132 <;> simp [S₃,S₂,S₁,movedR,hk131,hk136,hk137,hk132,h131,h136,h137]

def publicationSelectFromHeaders : Pr P₀ 144 Q A U :=
  .seq (ucopy 121 143 134) publicationMerge

def publicationSelectFromHeadersCost (s w : ℕ) : ℕ := 4*s+4+publicationMergeCost s w

theorem publicationSelectFromHeaders_exec {s t band a b w : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hst : s < t) (hbs : b ≤ s) (D C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 121).length = s) (hw : (S.R 94).length = w)
    (hmask : S.R 109 = publicationMaskSymbols A s t band a b)
    (hD : S.R 137 = cstream A w (chirpLine s D)) (hC : S.R 132 = cstream A w (chirpLine s C)++tail)
    (h143 : S.R 143 = []) (h140 : S.R 140 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) :
    let G := fun i => realPartWord (publicationField t band a b D C i)
    ∃ v' n, v'.user = v.user ∧ n ≤ publicationSelectFromHeadersCost s w ∧
      Exec body publicationSelectFromHeaders (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 109 [])
          137 []) 132 (cstream A w (chirpLine s G)++tail))}) := by
  dsimp only
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 121) (b := 143) (t := 134)
    (by decide) (by decide) (by decide) v S h134
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 143 (List.replicate s tick)}
  have he₁' : Exec body (ucopy 121 143 134) (mk v S) (4*s+4) (mk v₁ S₁) := by
    simpa [S₁,hs,h143] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := publicationMerge_exec (body := body) hA hst hbs D C tail v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hw) (by simpa [S₁] using hmask)
    (by simpa [S₁] using hD) (by simpa [S₁] using hC)
    (by simpa [S₁] using h140) (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  refine ⟨v₂,(4*s+4)+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast rfl ?_⟩
  · dsimp only [publicationSelectFromHeadersCost]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk143 : k = 143 <;> by_cases hk132 : k = 132 <;> by_cases hk137 : k = 137 <;>
      by_cases hk109 : k = 109 <;> simp [S₁,hk143,hk132,hk137,hk109,h143]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
