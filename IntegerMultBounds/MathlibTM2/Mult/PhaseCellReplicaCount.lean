module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout

/-! Count replicas from actual packets independently of the output row width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def replicaCount (keys width row src count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct keys width row saved tmp)
    (.seq (countWords row src count saved tmp) (uclear row))

/-- Derive the real replica count before padding. The payload and both input
width headers restore, so this count remains valid when output rows shrink. -/
theorem replicaCount_exec {keys width row src count saved tmp : Fin T}
    (hreg : [keys,width,row,src,count,saved,tmp].Nodup)
    {N K W : ℕ} (hK : 0 < K) (hW : 0 < W)
    (f : Fin N → Fin K → Fin W → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A)
    (hkeys : (S.R keys).length = K) (hwidth : (S.R width).length = W)
    (hsrc : S.R src = replicaKeyWords f)
    (hrow : S.R row = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ K*(4*W+9)+N*(6*(K*W)+6)+2*(K*W)+10 ∧
      Exec body (replicaCount keys width row src count saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R count (List.replicate N tick)}) := by
  have hr := hreg
  regs_ne hr
  let words := List.ofFn fun r : Fin N =>
    (List.ofFn fun k : Fin K => List.ofFn fun b : Fin W => f r k b).flatten
  have hwords : words.flatten = replicaKeyWords f := by
    exact (keyReplicaWords_blocks (fun k r b => f r k b)).symm
  have hlen : ∀ xs ∈ words, xs.length = K*W := by
    intro xs hx
    obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hx
    simp [List.length_flatten,List.sum_ofFn]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [keys,width,row,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R row (List.replicate (K*W) tick)}
  have he₁' : Exec body (unaryProduct keys width row saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hkeys,hwidth,hrow] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := countWords_exec (body := body)
    (show [row,src,count,saved,tmp].Nodup by regs_nodup) (K*W) (Nat.mul_pos hK hW) words
    hlen v₁ S₁ (by simp [S₁])
    (by simpa [S₁,‹row ≠ src›.symm,hwords] using hsrc)
    (by simpa [S₁,‹row ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹row ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R count (List.replicate N tick)}
  have he₂' : Exec body (countWords row src count saved tmp) (mk v₁ S₁)
      (N*(6*(K*W)+6)+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,words,‹row ≠ count›.symm,hcount] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) row v₂ S₂
  refine ⟨v₃,n₁+(N*(6*(K*W)+6)+4)+(2*(K*W)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · rw [hkeys,hwidth] at hn₁
    omega
  · simp [S₂,S₁,‹row ≠ count›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = count
    · subst i; simp [S₂,S₁,‹row ≠ count›.symm]
    by_cases hirow : i = row
    · subst i; simp [S₂,S₁,‹row ≠ count›,hrow]
    · simp [S₂,S₁,hi,hirow]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
