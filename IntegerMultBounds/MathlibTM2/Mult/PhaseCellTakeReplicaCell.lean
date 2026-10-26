module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Consume one ambient-origin/length descriptor in the generated halo packet
format. The retained queue width and all conversion scratch stacks survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}

def takeReplicaCell : Pr P 144 Q A U :=
  .seq (takeUnaryKey 125 126 141 134 135 136 137) takeOuterLengthKey

def replicaCellR {A : ℕ} (R : Regs 144 A) (queue : List (Fin (A+4))) (lo L : ℕ) : Regs 144 A :=
  Function.update (Function.update (Function.update R 126 queue) 141 (List.replicate lo tick))
    128 (List.replicate L tick)

theorem takeReplicaCell_exec (V lo L : ℕ) (hlo : lo < 2^V) (hL : L < 2^V)
    (suffix : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hV : (S.R 125).length = V)
    (hqueue : S.R 126 = binSyms V lo++binSyms V L++suffix)
    (hfresh : ∀ k ∈ [(128 : Fin 144),141,134,135,136,137], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*lo+6*L+38*V+28 ∧
      Exec body takeReplicaCell (mk v S) n (mk v' {S with R := replicaCellR S.R suffix lo L}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeUnaryKey_exec (body := body)
    (width := 125) (src := 126) (dst := 141) (word := 134) (work := 135) (saved := 136) (tmp := 137)
    (by decide) V lo hlo (binSyms V L++suffix) v S hV (by simpa [List.append_assoc] using hqueue)
    (by intro k hk; apply hfresh k; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)
  let S₁ : Stacks 144 A := {S with R := (Function.update (Function.update S.R 126
    (binSyms V L++suffix)) 141 (List.replicate lo tick))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := takeOuterLengthKey_exec (body := body) V L hL suffix v₁ S₁
    (by simpa [S₁] using hV) (by simp [S₁]) (by
      intro k hk
      have h126 : k ≠ 126 := by intro he; subst k; norm_num at hk
      have h141 : k ≠ 141 := by intro he; subst k; norm_num at hk
      simpa [S₁,h126,h141] using hfresh k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h126 : k = 126
    · subst k; simp [S₁,replicaCellR]
    by_cases h128 : k = 128
    · subst k; simp [S₁,replicaCellR]
    by_cases h141 : k = 141
    · subst k; simp [S₁,replicaCellR]
    simp [S₁,replicaCellR,h126,h128,h141]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
