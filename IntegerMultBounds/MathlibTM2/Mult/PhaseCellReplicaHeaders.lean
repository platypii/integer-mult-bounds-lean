module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedBatchInputBank

/-! Copy the retained count and ambient origin into the private replica ABI.
The two sources are disjoint from the numerical bank and survive every call. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def replicaHeaderCopies : List (Fin 144 × Fin 144) := [(142,116),(141,111)]

def replicaHeaderValue (B lo : ℕ) (k : Fin 144) : ℕ := if k = 142 then B else lo

def copiedReplicaR {A : ℕ} (B lo : ℕ) (R : Regs 144 A) : Regs 144 A :=
  unaryCopiesR (replicaHeaderValue B lo) R replicaHeaderCopies

def installReplicaHeaders {Q A : ℕ} {U P : Type} : Pr P 144 Q A U :=
  copyUnaryHeaders 133 replicaHeaderCopies

theorem installReplicaHeaders_exec {Q A : ℕ} {U P : Type} {body : P → Pr P 144 Q A U}
    (B lo : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hB : (S.R 142).length = B) (hlo : (S.R 141).length = lo) (h133 : S.R 133 = []) :
    ∃ v', v'.user = v.user ∧ Exec body installReplicaHeaders (mk v S) (4*B+4*lo+9)
      (mk v' {S with R := copiedReplicaR B lo S.R}) := by
  obtain ⟨v',hu,he⟩ := copyUnaryHeaders_exec (body := body) 133 replicaHeaderCopies
    (by intro r hr; simp only [replicaHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> decide)
    (by intro r hr p hp
        simp only [replicaHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr hp
        rcases hr with rfl | rfl <;> rcases hp with rfl | rfl <;> decide)
    (replicaHeaderValue B lo) v S
    (by intro r hr; simp only [replicaHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · simpa [replicaHeaderValue] using hB
        · simpa [replicaHeaderValue] using hlo) h133
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp [copyUnaryHeadersCost,replicaHeaderCopies,replicaHeaderValue]
  ring

theorem copiedReplicaR_off {A : ℕ} (B lo : ℕ) (R : Regs 144 A) (k : Fin 144)
    (h116 : k ≠ 116) (h111 : k ≠ 111) : copiedReplicaR B lo R k = R k := by
  apply unaryCopiesR_off
  intro r hr
  simp only [replicaHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact h116.symm
  · exact h111.symm

theorem copiedReplica_project {A : ℕ} (P N q l s t u band L lo B : ℕ) (S : Stacks 144 A)
    (raw borrowed : List (Fin (A+4)))
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = raw++borrowed) :
    embStk groupReg {S with R := copiedReplicaR B lo (copiedGroupR P N q l s t u band L S.R)} =
      repeatedBatchInputBank P N q l s t u band L lo B raw borrowed (S.R 93) S.inp S.out := by
  have hg := copiedGroup_project P N q l s t u band L S raw borrowed hleft hblank hsrc
  have h111 : copiedGroupR P N q l s t u band L S.R 111 = [] := by
    have hh := congrArg (fun T : Stacks 117 A => T.R 111) hg
    simpa [embStk,groupReg,naturalGroupInputBank,batchInputBank] using hh
  have h116 : copiedGroupR P N q l s t u band L S.R 116 = [] := by
    have hh := congrArg (fun T : Stacks 117 A => T.R 116) hg
    simpa [embStk,groupReg,naturalGroupInputBank,batchInputBank] using hh
  ext1
  · rfl
  · rfl
  · funext i; exact hleft (groupReg i) i.isLt
  · funext i
    by_cases hi116 : i = 116
    · subst i
      simp [embStk,groupReg,copiedReplicaR,unaryCopiesR,replicaHeaderCopies,replicaHeaderValue,
        h116,repeatedBatchInputBank,batchInputBank]
    by_cases hi111 : i = 111
    · subst i
      simp [embStk,groupReg,copiedReplicaR,unaryCopiesR,replicaHeaderCopies,replicaHeaderValue,
        h111,repeatedBatchInputBank,batchInputBank]
    have hh := congrArg (fun T : Stacks 117 A => T.R i) hg
    change copiedReplicaR B lo _ (groupReg i) = _
    rw [copiedReplicaR_off B lo _ _ (by simpa [groupReg,Fin.ext_iff] using hi116)
      (by simpa [groupReg,Fin.ext_iff] using hi111)]
    by_cases hi109 : i = 109
    · subst i
      simpa [embStk,groupReg,naturalGroupInputBank,repeatedBatchInputBank,batchInputBank] using hh
    · have hv109 : i.val ≠ 109 := fun h => hi109 (Fin.ext h)
      have hv116 : i.val ≠ 116 := fun h => hi116 (Fin.ext h)
      simpa [embStk,naturalGroupInputBank,repeatedBatchInputBank,batchInputBank,hv109,hv116,
        hi111,hi116,hi109,Function.update_apply,Fin.ext_iff] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
