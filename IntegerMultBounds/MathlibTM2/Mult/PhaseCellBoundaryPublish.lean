module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroWords

/-! Initialize and publish the ambient boundary field above retained tape contents. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryPublish : Pr P 224 Q A U :=
  .seq (zeroWords 121 160 132 184 217 223) (scatterBatch 220 223 201 160 204 132 208 211 215)

/-- The ambient prefix is generated from retained dimensions; only the gap stream
is supplied here. The packed boundary prefix is consumed and all borrowed tails restore. -/
theorem boundaryPublish_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (w : ℕ) (hw : 1 ≤ w)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 121).length = s) (hwidth : (S.R 160).length = w)
    (hc : S.R 220 = gatherControls A (boundaryScatterGaps s B w))
    (hsrc : S.R 204 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 54*s*w+16 ∧
      Exec body boundaryPublish (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 204 sourceTail) 132
          (cstream A w (chirpLine s G)++S.R 132))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := zeroWords_exec (body := body)
    (rows := 121) (width := 160) (dst := 132) (count := 184) (saved := 217) (tmp := 223)
    (by decide) s w v S hs hwidth
    (hclean 184 (by simp)) (hclean 217 (by simp)) (hclean 223 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 132 (cstream A w (List.replicate s 0)++S.R 132)}
  have hc₁ : S₁.R 220 = gatherControls A (boundaryScatterGaps s B w) := by simpa [S₁] using hc
  have hsrc₁ : S₁.R 204 = cstream A w ((bOrder s B).map G)++sourceTail := by simpa [S₁] using hsrc
  have hclean₁ : ∀ i ∈ ([223,201,208,211,215] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have hi132 : i ≠ 132 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,hi132] using hclean i (by simp_all)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryScatter_exec (body := body)
    (control := 220) (savedControl := 223) (gap := 201) (window := 160) (src := 204) (dst := 132)
    (acc := 208) (trash := 211) (tmp := 215) (by decide) s B w hw G hoff sourceTail (S.R 132)
    v₁ S₁ hc₁ rfl hsrc₁ (by simpa [S₁] using hwidth) hclean₁
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by nlinarith only [hn₁,hn₂,hsw],(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h204 : i = 204 <;> simp [S₁,h132,h204]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
