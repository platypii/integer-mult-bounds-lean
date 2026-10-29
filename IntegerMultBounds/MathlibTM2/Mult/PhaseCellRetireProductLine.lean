module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine

/-! Retire a rectangular collection of fixed-width records using its retained
two dimensions. All generated counters and scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def retireProductLine (rows block width src blocks count trash tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct rows block blocks trash tmp)
    (.seq (retireCountedLine blocks width src count trash tmp) (uclear blocks))

def retireProductLineCost (K L w : ℕ) : ℕ :=
  K*(4*L+9)+retireCountedLineCost (K*L) w+2*(K*L)+6

theorem retireProductLine_exec (rows block width src blocks count trash tmp : Fin T)
    (hreg : [rows,block,width,src,blocks,count,trash,tmp].Nodup) (K L w : ℕ)
    (words tail : List (Fin (A+4))) (hlen : words.length = K*L*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hK : (S.R rows).length = K) (hL : (S.R block).length = L) (hw : (S.R width).length = w)
    (hsrc : S.R src = words++tail) (hblocks : S.R blocks = [])
    (hcount : S.R count = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retireProductLineCost K L w ∧
      Exec body (retireProductLine rows block width src blocks count trash tmp) (mk v S) m
        (mk v' {S with R := Function.update S.R src tail}) := by
  have hr := hreg
  regs_ne hr
  have h5 : [rows,block,blocks,trash,tmp].Nodup := by simp_all [ne_comm]
  have h6 : [blocks,width,src,count,trash,tmp].Nodup := by simp_all [ne_comm]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := rows) (b := block) (dst := blocks) (t₁ := trash) (t₂ := tmp) h5 v S htrash htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R blocks (List.replicate (K*L) tick)}
  have he₁' : Exec body (unaryProduct rows block blocks trash tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hK,hL,hblocks,List.append_nil] using he₁
  have hm₁' : m₁ ≤ K*(4*L+9)+4 := by simpa only [hK,hL] using hm₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retireCountedLine_exec (body := body) blocks width src count trash tmp
    h6 (K*L) w words tail hlen v₁ S₁ (by simp [S₁])
    (by simpa [S₁,‹width ≠ blocks›] using hw) (by simpa [S₁,‹src ≠ blocks›] using hsrc)
    (by simpa [S₁,‹blocks ≠ count›.symm] using hcount)
    (by simpa [S₁,‹blocks ≠ trash›.symm] using htrash)
    (by simpa [S₁,‹blocks ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src tail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body blocks v₂ S₂
  have hlenBlocks : (S₂.R blocks).length = K*L := by simp [S₂,S₁,‹src ≠ blocks›.symm]
  refine ⟨v₃,m₁+(m₂+(2*(K*L)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlenBlocks]) ?_⟩
  · dsimp only [retireProductLineCost]; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hs : k = src
    · subst k; simp [S₂,S₁,‹src ≠ blocks›]
    by_cases hb : k = blocks
    · subst k; simp [S₂,S₁,hs,hblocks]
    · simp [S₂,S₁,hs,hb]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
