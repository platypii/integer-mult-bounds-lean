module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchInput

/-! # Fixed-bank merge with every routing header generated and released -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def fixedBranchMerge : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (mergeFromWords 1 94 2 93 3 4 5 7 8) (uclear 1))

def fixedMergeCost (w M L : ℕ) : ℕ := (M * L) * (25 * w + 21) + 17 * M + 34

/-- Merge the adjacent branch blocks using only the retained 2M, L and w headers.
Every generated header and every work stack is empty on return. -/
theorem fixedBranchMerge_with_x_tail_exec (hA : 96 ≤ A) {q l w M L : ℕ} (hw : 1 ≤ w)
    (rawX rawV : ℕ → List GaussianInt) (X Y : Fin (M * L) → GaussianInt)
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fixedMergeCost w M L ∧
      Exec body fixedBranchMerge
        (mk v (Fixed.startWithTails q l w (M + M) L L rawX rawV
          (cstream A w (List.ofFn X) ++ (cstream A w (List.ofFn Y) ++ tail)) tailX [] inp out)) m
        (mk v' (Fixed.startWithTails q l w (M + M) L L rawX rawV
          (cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail) tailX [] inp out)) := by
  let result := cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail
  let S := Fixed.startWithTails q l w (M + M) L L rawX rawV
    (cstream A w (List.ofFn X) ++ (cstream A w (List.ofFn Y) ++ tail)) tailX [] inp out
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S
    (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]; omega)
    (by simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := mergeFromWords_exec (body := body)
    (words := 1) (width := 94) (count := 2) (src := 93) (a := 3) (b := 4) (acc := 5) (buf := 7) (tmp := 8)
    (by decide) hA hw X Y v₁ S₁ tail
    (by simp [S₁]) (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 1 v₂ S₂
  have hwords : (S₂.R 1).length = M * L := by simp [S₂, S₁]
  refine ⟨v₃, m₁ + (m₂ + (2 * (M * L) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · unfold fixedMergeCost
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hwords]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (1 : Fin 117)
    · subst k
      simp [S₂, S₁, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    · by_cases ho : k.val = 93
      · have h93 : k = (93 : Fin 117) := Fin.ext ho
        subst k
        simp [S₂, S₁, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, result]
      · have h93 : k ≠ (93 : Fin 117) := fun h => ho (congrArg Fin.val h)
        simp [S₂, S₁, S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, hk, ho, h93]


theorem fixedBranchMerge_exec (hA : 96 ≤ A) {q l w M L : ℕ} (hw : 1 ≤ w)
    (rawX rawV : ℕ → List GaussianInt) (X Y : Fin (M * L) → GaussianInt)
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fixedMergeCost w M L ∧
      Exec body fixedBranchMerge
        (mk v (Fixed.start q l w (M + M) L L rawX rawV
          (cstream A w (List.ofFn X) ++ (cstream A w (List.ofFn Y) ++ tail)) inp out)) m
        (mk v' (Fixed.start q l w (M + M) L L rawX rawV
          (cstream A w (List.ofFn (fun i => X i - Y i)) ++ tail) inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    fixedBranchMerge_with_x_tail_exec (q := q) (l := l) (w := w) (M := M) (L := L)
      hA hw rawX rawV X Y v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
