module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Install the grouped arithmetic headers after shared construction. The
retained word width survives; the batch count is doubled for the two branches. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def installBatchHeaders : Pr P₀ 117 Q A U :=
  .seq (uclear 101) (.seq (ucopy 112 100 104) (.seq (ucopy 109 101 104)
    (.seq (umul 2 96 108 104) (clearWords [96, 109, 112, 114]))))

def installBatchHeadersCost (P N q l B : ℕ) : ℕ := 2*N+2*P+6*q+6*l+6*B+23

def batchHeaderBank {A : ℕ} (S : Stacks 117 A) (q l B : ℕ) : Stacks 117 A :=
  { S with R := (fun k => if k = 100 then List.replicate q tick
    else if k = 101 then List.replicate l tick else if k = 108 then List.replicate (2*B) tick
    else if k ∈ [(96 : Fin 117), 109, 112, 114] then [] else S.R k) }

theorem installBatchHeaders_exec (P N q l B : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hN : (S.R 101).length = N)
    (hq : (S.R 112).length = q) (hl : (S.R 109).length = l) (hB : (S.R 96).length = B)
    (hfresh : ∀ k ∈ [(100 : Fin 117), 104, 108], S.R k = []) :
    ∃ v', v'.user = v.user ∧ Exec body installBatchHeaders (mk v S)
      (installBatchHeadersCost P N q l B) (mk v' (batchHeaderBank S q l B)) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body 101 v S
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 101 [] }
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) (a := 112) (b := 100) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 100 (List.replicate q tick) }
  have he₂' : Exec body (ucopy 112 100 104) (mk v₁ S₁) (4*q+4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, hfresh 100 (by simp)] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 109) (b := 101) (t := 104)
    (by decide) (by decide) (by decide) v₂ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 101 (List.replicate l tick) }
  have he₃' : Exec body (ucopy 109 101 104) (mk v₂ S₂) (4*l+4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hl] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := umul_exec (body := body) 2 (a := 96) (b := 108) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 108 (List.replicate (2*B) tick) }
  have he₄' : Exec body (umul 2 96 108 104) (mk v₃ S₃) (4*B+4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, S₁, hB, hfresh 108 (by simp)] using he₄
  obtain ⟨v₅, hu₅, he₅⟩ := clearWords_exec (body := body)
    [(96 : Fin 117), 109, 112, 114] (by decide) v₄ S₄
  refine ⟨v₅, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅)))).cast ?_ ?_⟩
  · simp [S₄, S₃, S₂, S₁, hP, hN, hq, hl, hB, installBatchHeadersCost]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk100 : k = 100
      · subst k; simp [batchHeaderBank, S₄, S₃, S₂, S₁]
      by_cases hk101 : k = 101
      · subst k; simp [batchHeaderBank, S₄, S₃, S₂, S₁]
      by_cases hk108 : k = 108
      · subst k; simp [batchHeaderBank, S₄, S₃, S₂, S₁]
      simp [batchHeaderBank, S₄, S₃, S₂, S₁, hk100, hk101, hk108]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
