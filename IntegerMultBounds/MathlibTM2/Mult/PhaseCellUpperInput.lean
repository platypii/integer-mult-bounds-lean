module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLowerBatch

/-! # Upper-stage operand preparation inside the existing 117-tape bank

The ten private host registers used here are empty again before S1 starts.
No larger bank and no supplied reversed operand or row-symbol count are needed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

/-- Reuse private host slots 1..10 between S1 calls; its retained dimensions supply all counts. -/
def reverseInput : Pr P 117 Q A U :=
  reverseRowsFromDimensions 108 2 103 3 94 4 111 5 6 7 8 9 10 1

theorem inputBank_update_y (q l w M a b : ℕ) (X V Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) :
    Function.update (Fixed.inputBank q l w M a b X V tail) (Fixed.batchReg .srcY)
      (cstream A w ((List.range M).flatMap Y)) = Fixed.inputBank q l w M a b X Y tail := by
  funext k
  by_cases hk : k.val = 111
  · have he : k = Fixed.batchReg .srcY := Fin.ext hk
    subst k
    simp [Fixed.inputBank, Fixed.batchReg]
  · have he : k ≠ Fixed.batchReg .srcY := by intro he; exact hk (congrArg Fin.val he)
    simp [Fixed.inputBank, Function.update_of_ne he, hk]

theorem start_update_y (q l w M a b : ℕ) (X V Y : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    { Fixed.start q l w M a b X V tail inp out with R :=
      (Function.update (Fixed.inputBank q l w M a b X V tail) (Fixed.batchReg .srcY)
        (cstream A w ((List.range M).flatMap Y))) } =
      Fixed.start q l w M a b X Y tail inp out := by
  rw [inputBank_update_y]
  rfl

/-- Publishing a result changes only the existing S1 output suffix parameter. -/
theorem start_update_output (q l w M a b : ℕ) (X V : ℕ → List GaussianInt)
    (tail result : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    { Fixed.start q l w M a b X V tail inp out with R :=
      (Function.update (Fixed.inputBank q l w M a b X V tail) (Fixed.ringReg .out) result) } =
      Fixed.start q l w M a b X V result inp out := by
  have hR : Function.update (Fixed.inputBank q l w M a b X V tail) (Fixed.ringReg .out) result =
      Fixed.inputBank q l w M a b X V result := by
    funext k
    by_cases hk : k.val = 93
    · have he : k = Fixed.ringReg .out := Fin.ext hk
      subst k
      simp [Fixed.inputBank, Fixed.ringReg]
    · have he : k ≠ Fixed.ringReg .out := by intro he; exact hk (congrArg Fin.val he)
      simp [Fixed.inputBank, Function.update_of_ne he, hk]
  rw [hR]
  rfl

/-- A generator-side suffix is independent of changes to the right operand. -/
theorem inputBankWithTails_update_y (q l w M a b : ℕ) (X V Y : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A + 4))) :
    Function.update (Fixed.inputBankWithTails q l w M a b X V tail tailX []) (Fixed.batchReg .srcY)
      (cstream A w ((List.range M).flatMap Y)) =
      Fixed.inputBankWithTails q l w M a b X Y tail tailX [] := by
  funext k
  by_cases hk : k.val = 111
  · have he : k = Fixed.batchReg .srcY := Fin.ext hk
    subst k
    simp [Fixed.inputBankWithTails, Fixed.inputBank, Fixed.batchReg]
  · have he : k ≠ Fixed.batchReg .srcY := fun h => hk (congrArg Fin.val h)
    simp [Fixed.inputBankWithTails, Fixed.inputBank, Function.update_of_ne he, hk]

theorem startWithTails_update_y (q l w M a b : ℕ) (X V Y : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    { Fixed.startWithTails q l w M a b X V tail tailX [] inp out with R :=
      (Function.update (Fixed.inputBankWithTails q l w M a b X V tail tailX []) (Fixed.batchReg .srcY)
        (cstream A w ((List.range M).flatMap Y))) } =
      Fixed.startWithTails q l w M a b X Y tail tailX [] inp out := by
  rw [inputBankWithTails_update_y]
  rfl

/-- Publishing a result preserves both raw-operand suffixes. -/
theorem startWithTails_update_output (q l w M a b : ℕ) (X V : ℕ → List GaussianInt)
    (tail result tailX tailY : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    { Fixed.startWithTails q l w M a b X V tail tailX tailY inp out with R :=
      (Function.update (Fixed.inputBankWithTails q l w M a b X V tail tailX tailY)
        (Fixed.ringReg .out) result) } =
      Fixed.startWithTails q l w M a b X V result tailX tailY inp out := by
  have hR : Function.update (Fixed.inputBankWithTails q l w M a b X V tail tailX tailY)
      (Fixed.ringReg .out) result = Fixed.inputBankWithTails q l w M a b X V result tailX tailY := by
    funext k
    by_cases hk : k.val = 93
    · have he : k = Fixed.ringReg .out := Fin.ext hk
      subst k
      simp [Fixed.inputBankWithTails, Fixed.inputBank, Fixed.ringReg]
    · have he : k ≠ Fixed.ringReg .out := fun h => hk (congrArg Fin.val h)
      simp [Fixed.inputBankWithTails, Fixed.inputBank, Function.update_of_ne he, hk]
  rw [hR]
  rfl

/-- The exact canonical S1 bank after executed preparation, with every private word erased. -/
theorem reverseInput_with_x_tail_exec (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (hlen : ∀ n < M, (V n).length = L)
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20 ∧
      Exec body reverseInput (mk v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)) n
        (mk v' (Fixed.startWithTails q l w M L L X (fun j => (V j).reverse) tail tailX [] inp out)) := by
  let blocks := (List.range M).map V
  obtain ⟨v', n, hu, hn, he⟩ := reverseRowsFromDimensions_exec (body := body)
    (dst := 1) (batch := 108) (batchSaved := 2) (rowCount := 103) (recordSaved := 3)
    (wordR := 94) (recordSymbols := 4) (src := 111) (acc := 5) (current := 6)
    (savedSource := 7) (saved := 8) (buf := 9) (tmp := 10)
    (by decide +kernel) w L blocks (by
      intro xs hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      exact hlen j (List.mem_range.mp hj)) v (Fixed.startWithTails q l w M L L X V tail tailX [] inp out)
    (by simp [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, blocks])
    (by simp [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, blocks, List.flatMap_def])
    (by simp [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  refine ⟨v', n, hu, by simpa [blocks] using hn, ?_⟩
  have he' := he
  simp only [blocks, List.flatMap_map] at he'
  exact he'.cast rfl (congrArg (mk v')
    (startWithTails_update_y q l w M L L X V (fun j => (V j).reverse) tail tailX inp out))


theorem reverseInput_exec (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (hlen : ∀ n < M, (V n).length = L)
    (v : HS 117 Q A U) (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (32 * L * w + 19 * L + 17) + 6 * L * w + 9 * L + 20 ∧
      Exec body reverseInput (mk v (Fixed.start q l w M L L X V tail inp out)) n
        (mk v' (Fixed.start q l w M L L X (fun j => (V j).reverse) tail inp out)) := by
  simpa only [Fixed.startWithTails_nil] using
    reverseInput_with_x_tail_exec q l w M L X V hlen v tail [] inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
