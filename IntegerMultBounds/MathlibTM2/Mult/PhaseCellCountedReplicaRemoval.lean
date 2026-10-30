module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCountRemoval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout

/-! Derive output row dimensions before publishing real replica rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def countedReplicaRemoval (replicas keys width row src keep count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct keys width row saved tmp)
    (.seq (replicaCountRemoval replicas row src keep count saved tmp) (uclear row))

/-- Generate the current output row width and real-symbol count from ordinary
headers. Publish the actual real suffix and restore both generated counters. -/
theorem countedReplicaRemoval_exec {replicas keys width row src keep count saved tmp : Fin T}
    (hreg : [replicas,keys,width,row,src,keep,count,saved,tmp].Nodup)
    {C N K W : ℕ} (hN : N ≤ C) (f : Fin C → Fin K → Fin W → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hkeys : (S.R keys).length = K)
    (hwidth : (S.R width).length = W) (hsrc : S.R src = replicaKeyWords f)
    (hrow : S.R row = []) (hkeep : S.R keep = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ g : Fin N → Fin K → Fin W → Fin (A+4),
      replicaKeyWords g = (replicaKeyWords f).drop ((C-N)*(K*W)) ∧
      ∃ v' n, v'.user = v.user ∧
        n ≤ K*(4*W+9)+14*(C*(K*W))+9*N+2*(K*W)+26 ∧
        Exec body (countedReplicaRemoval replicas keys width row src keep count saved tmp)
          (mk v S) n (mk v' {S with R := Function.update S.R src (replicaKeyWords g)}) := by
  have hr := hreg
  regs_ne hr
  let cut := (C-N)*(K*W)
  let xs := replicaKeyWords f
  have hlen : xs.length = C*(K*W) := by simp [xs,replicaKeyWords]
  have hfit := Nat.mul_le_mul_right (K*W) hN
  have hcut : cut = C*(K*W)-N*(K*W) := Nat.sub_mul C N (K*W)
  have hreal : (xs.drop cut).length = N*(K*W) := by rw [List.length_drop,hlen,hcut]; omega
  obtain ⟨g,hg⟩ := replicaKeyWords_of_length (xs.drop cut) hreal
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [keys,width,row,saved,tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := {S with R := Function.update S.R row (List.replicate (K*W) tick)}
  have he₁' : Exec body (unaryProduct keys width row saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hkeys,hwidth,hrow] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := replicaCountRemoval_exec (body := body)
    (show [replicas,row,src,keep,count,saved,tmp].Nodup by regs_nodup)
    N (K*W) (xs.take cut) (xs.drop cut) hreal v₁ S₁
    (by simpa [S₁,‹replicas ≠ row›] using hreplicas) (by simp [S₁])
    (by rw [List.take_append_drop]; simpa [S₁,‹row ≠ src›.symm] using hsrc)
    (by simpa [S₁,‹row ≠ keep›.symm] using hkeep)
    (by simpa [S₁,‹row ≠ count›.symm] using hcount)
    (by simpa [S₁,‹row ≠ saved›.symm] using hsaved)
    (by simpa [S₁,‹row ≠ tmp›.symm] using htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (xs.drop cut)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) row v₂ S₂
  refine ⟨g,hg,v₃,n₁+n₂+(2*(K*W)+2),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · rw [hkeys,hwidth] at hn₁
    have hs : (xs.take cut).length+(xs.drop cut).length = C*(K*W) := by
      rw [←List.length_append,List.take_append_drop,hlen]
    omega
  · simp [S₂,S₁,‹row ≠ src›,Nat.add_assoc]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [S₂,S₁,‹row ≠ src›.symm,hg]
    by_cases hir : i = row
    · subst i; simp [S₂,S₁,‹row ≠ src›,hrow]
    · simp [S₂,S₁,his,hir]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
