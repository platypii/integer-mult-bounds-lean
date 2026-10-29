module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Generate protected publication controls before the packed gather consumes its
advance stream. Native dimensions are read once; all temporary counters are
restored, including the accumulator disjoint from the live word width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

def packedCellPublicationFromDimensions : Pr P 168 Q A U :=
  .seq (unaryProduct 102 94 131 134 135)
    (.seq (publicationControls 116 88 91 89 90 131 92 95 140 104 106) (uclear 131))

theorem packedCellPublicationFromDimensions_exec (N L w : ℕ) (offsets : List ℕ)
    (hne : offsets ≠ []) (hdis : offsets.Pairwise (fun i j => i+L ≤ j))
    (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (borrowed : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hL : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hc : S.R 116 = List.replicate offsets.length tick)
    (hs : S.R 91 = gatherControls A (originAdvances w 0 offsets++[0])++borrowed)
    (hz : ∀ k ∈ [(88 : Fin 168),89,90,92,95,104,106,131,134,135], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12*N*w+21*offsets.length+6*L*w+9*L+27 ∧
      Exec body packedCellPublicationFromDimensions (mk v S) n
        (mk v' {S with R := (Function.update S.R 140
          (gatherControls A (packedCellGaps L w offsets)++S.R 140))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 102) (b := 94) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hz 134 (by simp)) (hz 135 (by simp))
  let S₁ : Stacks 168 A := { S with R := Function.update S.R 131 (List.replicate (L*w) tick) }
  have he₁' : Exec body (unaryProduct 102 94 131 134 135) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hL,hw,hz 131 (by simp)] using he₁
  have hn₁' : n₁ ≤ L*(4*w+9)+4 := by simpa [hL,hw] using hn₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedCellPublicationControls_exec (body := body)
    (count := 116) (savedCount := 88) (control := 91) (savedControl := 89) (counter := 90)
    (window := 131) (zero := 92) (acc := 95) (dst := 140) (trash := 104) (tmp := 106)
    (by decide) N L w offsets hne hdis hfit borrowed v₁ S₁
    (by simpa [S₁] using hc) (by simpa [S₁] using hs) (by simp [S₁]) (by
      intro k hk
      have hk131 : k ≠ (131 : Fin 168) := by
        intro he; subst k; norm_num at hk
      simp only [S₁,Function.update_of_ne hk131]
      apply hz k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₂ : Stacks 168 A := { S₁ with R := (Function.update S₁.R 140
    (gatherControls A (packedCellGaps L w offsets)++S₁.R 140)) }
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 131 v₂ S₂
  have hlen : (S₂.R 131).length = L*w := by simp [S₂,S₁]
  refine ⟨v₃,n₁+(n₂+(2*(L*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  · nlinarith only [hn₁',hn₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = 131
    · subst k; simp [hz 131 (by simp)]
    simp [S₂,S₁,Function.update_apply,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
