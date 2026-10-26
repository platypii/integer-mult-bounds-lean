module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySize

/-! Accumulate binary sizes of retained unary headers. The structural header
list is fixed by the caller; every header and conversion scratch stack restores. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def addUnarySizes : List (Fin 117) → Pr P 117 Q A U
  | [] => .act .done
  | r::rs => .seq (unarySize r 115 0 1 2 3 4) (addUnarySizes rs)

theorem addUnarySizes_exec (rs : List (Fin 117))
    (hregs : ∀ r ∈ rs, [r,(115 : Fin 117),0,1,2,3,4].Nodup)
    (value : Fin 117 → ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsrc : ∀ r ∈ rs, (S.R r).length = value r)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (rs.map (fun r => 19*value r+8)).sum+1 ∧
      Exec body (addUnarySizes rs) (mk v S) n
        (mk v' {S with R := (Function.update S.R 115
          (List.replicate (rs.map (fun r => Nat.size (value r))).sum tick++S.R 115))}) := by
  induction rs generalizing v S with
  | nil =>
    refine ⟨v,1,rfl,by simp,?_⟩
    simpa [addUnarySizes,Action.run] using Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    have hr := hregs r (by simp)
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unarySize_exec (body := body) hr (value r) v S
      (hsrc r (by simp)) hfresh
    let S₁ : Stacks 117 A := {S with R := (Function.update S.R 115
      (List.replicate (Nat.size (value r)) tick++S.R 115))}
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih (fun r hr => hregs r (by simp [hr])) v₁ S₁
      (by intro k hk
          have hne : k ≠ 115 := by
            have hh := hregs k (by simp [hk])
            simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hh
            exact hh.1.1
          simpa [S₁,hne] using hsrc k (by simp [hk]))
      (by intro k hk
          have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
          simpa [S₁,hne] using hfresh k hk)
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
    · simp only [List.map_cons,List.sum_cons]; omega
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        by_cases hk : k = 115
        · subst k
          simp [S₁,List.replicate_append_replicate,← List.append_assoc,Nat.add_comm]
        · simp [S₁,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
