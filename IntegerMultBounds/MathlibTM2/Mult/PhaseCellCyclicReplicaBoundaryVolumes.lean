module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Derive both packed residual volumes from the retained cyclic endpoints.
The shared numerical word width is borrowed, and all product scratch restores. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

def cyclicReplicaBoundaryVolumes : Pr P 180 Q A U :=
  .seq (ucopy 145 176 177) (.seq (usub 144 176 177)
    (.seq (unaryProduct 176 130 168 174 175)
      (.seq (unaryProduct 146 130 171 174 175) (uclear 176))))

def cyclicReplicaBoundaryVolumesCost (a n w : ℕ) := 8*a+6*n+n*(4*w+9)+18

theorem cyclicReplicaBoundaryVolumes_exec (a left right w : ℕ)
    (v : HS 180 Q A U) (S : Stacks 180 A)
    (ha : (S.R 144).length = a) (hleft : (S.R 145).length = a+left)
    (hright : (S.R 146).length = right) (hw : (S.R 130).length = w)
    (hfresh : ∀ k ∈ [(168 : Fin 180),171,174,175,176,177], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicReplicaBoundaryVolumesCost a (left+right) w ∧
      Exec body cyclicReplicaBoundaryVolumes (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R
          168 (List.replicate (left*w) tick)) 171 (List.replicate (right*w) tick))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 145) (b := 176) (t := 177)
    (by decide) (by decide) (by decide) v S (hfresh _ (by simp))
  let J : Stacks 180 A := {S with R := Function.update S.R 176 (List.replicate (a+left) tick)}
  have he₁' : Exec body (ucopy 145 176 177) (mk v S) (4*(a+left)+4) (mk v₁ J) := by
    simpa only [J,hleft,hfresh 176 (by simp),List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec body (a := 144) (b := 176) (t := 177)
    (by decide) (by decide) (by decide) v₁ J (by simpa [J] using hfresh 177 (by simp))
  let K : Stacks 180 A := {S with R := Function.update S.R 176 (List.replicate left tick)}
  have he₂' : Exec body (usub 144 176 177) (mk v₁ J) (4*a+4) (mk v₂ K) := by
    simpa [J,K,ha,Function.update_idem] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := 176) (b := 130) (dst := 168) (t₁ := 174) (t₂ := 175) (by decide) v₂ K
    (by simpa [K] using hfresh 174 (by simp)) (by simpa [K] using hfresh 175 (by simp))
  let L : Stacks 180 A := {K with R := Function.update K.R 168 (List.replicate (left*w) tick)}
  have he₃' : Exec body (unaryProduct 176 130 168 174 175) (mk v₂ K) m₃ (mk v₃ L) := by
    simpa [K,L,hw,hfresh 168 (by simp)] using he₃
  have hm₃' : m₃ ≤ left*(4*w+9)+4 := by simpa [K,hw] using hm₃
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := unaryProduct_exec (body := body)
    (a := 146) (b := 130) (dst := 171) (t₁ := 174) (t₂ := 175) (by decide) v₃ L
    (by simpa [L,K] using hfresh 174 (by simp)) (by simpa [L,K] using hfresh 175 (by simp))
  let F : Stacks 180 A := {L with R := Function.update L.R 171 (List.replicate (right*w) tick)}
  have he₄' : Exec body (unaryProduct 146 130 171 174 175) (mk v₃ L) m₄ (mk v₄ F) := by
    simpa [L,K,F,hw,hright,hfresh 171 (by simp)] using he₄
  have hm₄' : m₄ ≤ right*(4*w+9)+4 := by simpa [L,K,hw,hright] using hm₄
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 176 v₄ F
  have hlen : (F.R 176).length = left := by simp [F,L,K]
  have hfinal : {F with R := Function.update F.R 176 []} =
      {S with R := (Function.update (Function.update S.R 168 (List.replicate (left*w) tick))
        171 (List.replicate (right*w) tick))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 176 <;> simp [F,L,K,hk,Function.update_apply,hfresh 176 (by simp)]
  refine ⟨v₅,_,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast rfl
      (congrArg (mk v₅) hfinal)⟩
  rw [hlen]
  unfold cyclicReplicaBoundaryVolumesCost
  nlinarith only [hm₃',hm₄',Nat.zero_le right]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
