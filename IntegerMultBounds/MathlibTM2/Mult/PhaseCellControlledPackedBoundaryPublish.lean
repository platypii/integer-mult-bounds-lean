module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryPublish

/-! Generate scatter controls from origin advances and publish with complete local cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def controlledPackedBoundaryPublish : Pr P 224 Q A U :=
  .seq conditionalPackedBoundaryPublicationControls (.seq packedBoundaryPublish (uclear 220))

theorem controlledPackedBoundaryPublish_exec (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (a L w : ℕ) (hw : 1 ≤ w)
    (hfit : a+L ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+L)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ B, G i = 0)
    (sourceTail borrowed : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 222).length = L) (hwidth : (S.R 160).length = w)
    (hc : S.R 116 = List.replicate B.card tick)
    (hadv : S.R 206 = gatherControls A (originAdvances w 0 (packedBoundaryOrigins B a)++[0])++borrowed)
    (hsrc : S.R 204 = cstream A w ((bOrder s B).map G)++sourceTail)
    (hclean : ∀ i ∈ ([184,217,223,201,208,211,215,220] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 89*L*w+41 ∧
      Exec body controlledPackedBoundaryPublish (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 204 sourceTail) 132
          (cstream A w (packedInterval a L G)++S.R 132))}) := by
  let controls := gatherControls A (packedBoundaryGaps B a w)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 220 controls}
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := conditionalPackedBoundaryPublicationControls_exec (body := body)
    s B a L w hB hw borrowed v S hc hadv hwidth (fun i hi => hclean i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto))
  have he₁' : Exec body conditionalPackedBoundaryPublicationControls (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,controls,hclean 220 (by simp)] using he₁
  have hz : ∀ i ∈ ([184,217,223,201,208,211,215] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have hi220 : i ≠ 220 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,hi220] using hclean i (by simp_all)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedBoundaryPublish_exec (body := body) s B a L w hw hfit hB G hoff sourceTail v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using hwidth) rfl
    (by simpa [S₁] using hsrc) hz
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update S₁.R 204 sourceTail) 132
    (cstream A w (packedInterval a L G)++S.R 132))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 220 v₂ S₂
  have he₃' : Exec body (uclear 220) (mk v₂ S₂) (2*controls.length+2)
      (mk v₃ {S₂ with R := Function.update S₂.R 220 []}) := by simpa [S₂,S₁] using he₃
  have hlen : controls.length ≤ L*w := by
    have hv := scatterVolume_le w (List.replicate (L*w) ()) (packedBoundaryGaps B a w)
      (packedBoundaryGaps_fits B a L w hB _ (by simp))
    simp only [scatterVolume,packedBoundaryGaps_length,List.length_replicate] at hv
    have hn : B.card ≤ B.card*w := by simpa using Nat.mul_le_mul_left B.card hw
    simp only [controls,length_gatherControls,packedBoundaryGaps_length]
    omega
  refine ⟨v₃,n₁+(n₂+(2*controls.length+2)),hu₃.trans (hu₂.trans hu₁),
    by nlinarith only [hn₁,hn₂,hlen],(Exec.seq he₁' (Exec.seq he₂ he₃')).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h220 : i = 220 <;> by_cases h132 : i = 132 <;> by_cases h204 : i = 204 <;>
    simp [S₂,S₁,h220,h132,h204,hclean 220 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
