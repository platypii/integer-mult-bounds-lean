module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawReplicaGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedBatchInputBank

/-! A restoring replica gather reaches the same-origin solver's exact input
bank. The complete raw line batch and borrowed suffix remain beneath its RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem rawRepeatedBatchInput_exec (P N q l s t u band L lo B : ℕ)
    (hB : 0 < B) (hspan : lo+L ≤ s) (C : ℕ → ZMod s → GaussianInt)
    (v : HS 117 Q A U) (borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let raw := cstream A (2*q+8) (replicaAmbientWords B C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap (cellSourceRows L (fun _ => (lo : ZMod s)) C))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawReplicaGatherCost q s lo L (B-1) ∧
      Exec body rawReplicaGather
        (mk v (repeatedBatchInputBank P N q l s t u band L lo B raw borrowed outTail inp out)) n
        (mk v' (repeatedBatchInputBank P N q l s t u band L lo B rhs (raw++borrowed) outTail inp out)) := by
  dsimp only
  cases B with
  | zero => omega
  | succ B =>
    let raw := cstream A (2*q+8) (replicaAmbientWords (B+1) C)
    let S := repeatedBatchInputBank P N q l s t u band L lo (B+1) raw borrowed outTail inp out
    obtain ⟨v',n,hu,hn,he⟩ := rawReplicaGather_exec (body := body) q lo L B C hspan borrowed v S
      (by simp [S,repeatedBatchInputBank,batchInputBank])
      (by simp [S,repeatedBatchInputBank,batchInputBank])
      (by simp [S,repeatedBatchInputBank])
      (by simp [S,repeatedBatchInputBank,batchInputBank])
      (by simp [S,repeatedBatchInputBank,batchInputBank])
      (by simp [S,repeatedBatchInputBank,batchInputBank,raw]) (by
        intro k hk
        have hn (r : ℕ) (hr : 13 ≤ r) : k.val ≠ r := by omega
        simp [S,repeatedBatchInputBank,batchInputBank,Fin.ext_iff,
          hn 109 (by decide),hn 111 (by decide),hn 101 (by decide),hn 102 (by decide),hn 103 (by decide),
          hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),hn 100 (by decide),hn 112 (by decide),
          hn 114 (by decide),hn 116 (by decide),hn 110 (by decide),hn 93 (by decide)]) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        all_goals simp [S,repeatedBatchInputBank,batchInputBank])
    refine ⟨v',n,hu,by simpa using hn,he.cast rfl ?_⟩
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h110 : k = 110
    · subst k; simp [S,repeatedBatchInputBank,batchInputBank,raw]
    simp [S,repeatedBatchInputBank,batchInputBank,Function.update_apply,h110,
      show k.val ≠ 110 from fun he => h110 (Fin.ext he)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
