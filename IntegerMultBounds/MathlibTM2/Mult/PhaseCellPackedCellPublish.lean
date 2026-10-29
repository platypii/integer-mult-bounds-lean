module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellScatter
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Publish compact cell results into the retained local output buffer. Native
arithmetic headers may already be released: protected dimensions suffice. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def packedCellPublish : Pr P 168 Q A U :=
  .seq (unaryProduct 128 130 131 134 135)
    (.seq (scatterBatch 140 88 89 131 93 132 90 92 94) (clearWords [131,140]))

theorem packedCellPublish_exec (N L w : ℕ) (hL : 1 ≤ L) (hw : 1 ≤ w)
    (offsets : List ℕ) (hne : offsets ≠ [])
    (hdis : offsets.Pairwise (fun i j => i+L ≤ j)) (hfit : ∀ j ∈ offsets, j+L ≤ N)
    (E ys sourceTail outputTail : List (Fin (A+4)))
    (hE : E.length = N*w) (hys : ys.length = offsets.length*(L*w))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hrows : (S.R 128).length = L) (hwidth : (S.R 130).length = w)
    (hc : S.R 140 = gatherControls A (packedCellGaps L w offsets))
    (hdst : S.R 132 = E++outputTail) (hsrc : S.R 93 = ys++sourceTail)
    (hclean : ∀ k ∈ [(88 : Fin 168),89,90,92,94,131,134,135], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 54*N*w+15 ∧
      Exec body packedCellPublish (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 93 sourceTail)
          132 (scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail)) 140 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := 128) (b := 130) (dst := 131) (t₁ := 134) (t₂ := 135) (by decide) v S
    (hclean 134 (by simp)) (hclean 135 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 131 (List.replicate (L*w) tick)}
  have he₁' : Exec body (unaryProduct 128 130 131 134 135) (mk v S) m₁ (mk v₁ B) := by
    simpa [B,hrows,hwidth,hclean 131 (by simp)] using he₁
  have hm₁' : m₁ ≤ L*(4*w+9)+4 := by simpa [hrows,hwidth] using hm₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := packedCellScatter_exec (body := body)
    (control := 140) (savedControl := 88) (gap := 89) (window := 131) (src := 93) (dst := 132)
    (acc := 90) (trash := 92) (tmp := 94) (by decide) N L w hL hw offsets hdis hfit
    E ys sourceTail outputTail hE hys v₁ B
    (by simpa [B] using hc) (by simpa [B] using hdst) (by simpa [B] using hsrc) (by simp [B])
    (by intro k hk
        have hn : k ≠ 131 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [B,hn] using hclean k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp))
  let F : Stacks 168 A := {B with R := (Function.update (Function.update B.R 93 sourceTail)
    132 (scatterRows (L*w) E ys (packedCellGaps L w offsets)++outputTail))}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(131 : Fin 168),140] (by decide) v₂ F
  have hsum : ([(131 : Fin 168),140].map (fun k => (F.R k).length)).sum =
      L*w+(packedCellGaps L w offsets).sum+offsets.length := by
    simp [F,B,hc,length_gatherControls,packedCellGaps]
    omega
  have hfits : ScatterFits (L*w) E (packedCellGaps L w offsets) := by
    simpa [packedCellGaps] using windowGaps_fits (L*w) 0 (offsets.map (·*w)) E
      (fun _ _ => Nat.zero_le _) (packedCell_offsets_disjoint L w offsets hdis)
      (packedCell_offsets_fit N L w offsets E hE hfit)
  have hv := scatterVolume_le (L*w) E (packedCellGaps L w offsets) hfits
  simp only [scatterVolume,packedCellGaps,windowGaps_length,List.length_map,hE] at hv
  have hLN : L ≤ N := by
    cases ho : offsets with
    | nil => exact False.elim (hne ho)
    | cons j js => have hf := hfit j (by simp [ho]); omega
  have hLw : L*w ≤ N*w := Nat.mul_le_mul_right w hLN
  have hNw : N ≤ N*w := by simpa using Nat.mul_le_mul_left N hw
  have hK : offsets.length ≤ N*w := by
    have hpos : 1 ≤ L*w := by simpa using Nat.mul_le_mul hL hw
    have hk : offsets.length ≤ offsets.length*(L*w) := by simpa using Nat.mul_le_mul_left offsets.length hpos
    omega
  have hgap : (packedCellGaps L w offsets).sum ≤ N*w := by
    change (windowGaps (L*w) 0 (offsets.map (·*w))).sum ≤ N*w
    omega
  refine ⟨v₃,m₁+(m₂+(2*(L*w+(packedCellGaps L w offsets).sum+offsets.length)+5)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hsum]; simp) ?_⟩
  · nlinarith only [hm₁',hm₂,hgap,hLN,hLw,hNw,hK]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h131 : k = 131 <;> by_cases h140 : k = 140 <;> by_cases h93 : k = 93 <;>
      by_cases h132 : k = 132 <;> simp [F,B,h131,h140,h93,h132,hclean 131 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
