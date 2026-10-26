module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Endpoint stacks are borrowed during descriptor generation. Save their exact
contents outside the replica ABI, install its count, and restore them afterward. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def borrowReplicaEndpoints : Pr P 144 Q A U :=
  .seq (moveR 141 139 id) (.seq (moveR 142 140 id) (ucopy 143 142 133))

def borrowedReplicaEndpointR {A : ℕ} (R : Regs 144 A) (B : ℕ) : Regs 144 A :=
  Function.update (Function.update (Function.update (Function.update R
    139 (R 141).reverse) 140 (R 142).reverse) 141 []) 142 (List.replicate B tick)

theorem borrowReplicaEndpoints_exec (B a b : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hB : (S.R 143).length = B) (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h139 : S.R 139 = []) (h140 : S.R 140 = []) (h133 : S.R 133 = []) :
    ∃ v', v'.user = v.user ∧ Exec body borrowReplicaEndpoints (mk v S) (2*a+2*b+4*B+8)
      (mk v' {S with R := borrowedReplicaEndpointR S.R B}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body 141 139 (by decide) id v S
  let S₁ : Stacks 144 A := {S with R := movedR S.R 141 139 id (S.R 141)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 142 140 (by decide) id v₁ S₁
  let S₂ : Stacks 144 A := {S₁ with R := movedR S₁.R 142 140 id (S₁.R 142)}
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := 143) (b := 142) (t := 133)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂,S₁,movedR] using h133)
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁,movedR,ha,hb,hB]; ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h141 : k = 141 <;> by_cases h142 : k = 142 <;>
        by_cases h139' : k = 139 <;> by_cases h140' : k = 140 <;>
        simp [S₂,S₁,movedR,borrowedReplicaEndpointR,Function.update_apply,
          h141,h142,h139',h140',h139,h140,hB]

def releaseReplicaEndpoints : Pr P 144 Q A U :=
  .seq (uclear 142) (.seq (moveR 139 141 id) (moveR 140 142 id))

theorem releaseReplicaEndpoints_exec (B : ℕ) (a b : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hB : (S.R 142).length = B) (h139 : S.R 139 = a.reverse) (h140 : S.R 140 = b.reverse)
    (h141 : S.R 141 = []) :
    ∃ v', v'.user = v.user ∧ Exec body releaseReplicaEndpoints (mk v S)
      (2*B+2*a.length+2*b.length+6)
      (mk v' {S with R := (Function.update (Function.update (Function.update
        (Function.update S.R 139 []) 140 []) 141 a) 142 b)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec body 142 v S
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 142 []}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 139 141 (by decide) id v₁ S₁
  let S₂ : Stacks 144 A := {S₁ with R := movedR S₁.R 139 141 id (S₁.R 139)}
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 140 142 (by decide) id v₂ S₂
  refine ⟨v₃,hu₃.trans (hu₂.trans hu₁),(Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁,movedR,hB,h139,h140]; ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h141' : k = 141 <;> by_cases h142 : k = 142 <;>
        by_cases h139' : k = 139 <;> by_cases h140' : k = 140 <;>
        simp [S₂,S₁,movedR,Function.update_apply,h139,h140,h141,
          h141',h142,h139',h140']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
