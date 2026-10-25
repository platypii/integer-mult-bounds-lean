module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchCanonical

/-! # Install normalized input in the interior bank

The output prefix of the input-weight pass becomes S1's raw right operand.
Its owned table copy and normalization descriptor are released, while borrowed
generator-side data and the persistent output suffix are unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def installInput : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (takeFromWords 1 94 2 93 111 7 8)
      (.seq (uclear 1) (.seq (uclear 96) (uclear 116))))

def installInputCost (M L w b : ℕ) : ℕ :=
  14 * (M * L * w) + 15 * (M * L) + 17 * M + 2 * b + 28

/-- Derive the transfer count, install the raw words and release owned staging.
Every native stack and all other registers retain their exact original values. -/
theorem installInput_exec (M L w b : ℕ) (xs : List GaussianInt) (hlen : xs.length = M * L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w) (htable : (S.R 96).length = M * L * w)
    (hscale : (S.R 116).length = b) (hsrc : S.R 93 = cstream A w xs ++ tail) (hdst : S.R 111 = [])
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ installInputCost M L w b ∧
      Exec body installInput (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update
          S.R 93 tail) 111 (cstream A w xs)) 96 []) 116 []) }) := by
  have hxs : (cstream A w xs).length = M * L * w := by simp [hlen]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S (by omega) hrows (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := takeFromWords_exec (body := body)
    (words := 1) (width := 94) (count := 2) (src := 93) (dst := 111) (buf := 7) (tmp := 8)
    (by decide) (M * L) w v₁ S₁ (cstream A w xs) tail
    (by simp [S₁]) (by simpa [S₁] using hwidth) hxs (by simpa [S₁] using hsrc)
    (by simp [S₁, hclean 2 (by simp)]) (by simp [S₁, hclean 7 (by simp)])
    (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 93 tail) 111 (cstream A w xs)) }
  have he₂' : Exec body (takeFromWords 1 94 2 93 111 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₂, S₁, Function.update_of_ne (show (111 : Fin 117) ≠ 1 by decide), hdst, List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 1 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 1 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 96 v₃ S₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 96 [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 116 v₄ S₄
  have hcount : (S₂.R 1).length = M * L := by simp [S₂, S₁]
  have ht : (S₃.R 96).length = M * L * w := by simpa [S₃, S₂, S₁] using htable
  have hb : (S₄.R 116).length = b := by simpa [S₄, S₃, S₂, S₁] using hscale
  refine ⟨v₅, m₁ + (m₂ + ((2 * (M * L) + 2) + ((2 * (M * L * w) + 2) + (2 * b + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_⟩
  · unfold installInputCost
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast
      (by rw [hcount, ht, hb]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (1 : Fin 117)
    · subst k
      simp [S₄, S₃, S₂, S₁, hclean 1 (by simp)]
    · simp [S₄, S₃, S₂, S₁, Function.update_apply, hk]

/-- The staging bank has the exact interior layout outside the owned transfer
and the two temporary input-weight controls. -/
def inputInstallBank {A : ℕ} (q l w M L b : ℕ) (X Z V : ℕ → List GaussianInt)
    (factors : List GaussianInt) (tail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := singleBranchInputWithXTail q l w M L X Z V tail tailX inp out
  { S with R := (Function.update (Function.update (Function.update (Function.update S.R
      111 []) 93 (cstream A w ((List.range M).flatMap V) ++ tail)) 96 (cstream A w factors))
      116 (List.replicate b tick)) }

/-- The transfer's endpoint is exactly the existing single-input interior bank. -/
theorem inputInstallBank_frame {A : ℕ} (q l w M L b : ℕ) (X Z V : ℕ → List GaussianInt)
    (factors : List GaussianInt) (tail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := inputInstallBank q l w M L b X Z V factors tail tailX inp out
    { S with R := (Function.update (Function.update (Function.update (Function.update S.R 93 tail)
      111 (cstream A w ((List.range M).flatMap V))) 96 []) 116 []) } =
      singleBranchInputWithXTail q l w M L X Z V tail tailX inp out := by
  dsimp only
  let I := singleBranchInputWithXTail q l w M L X Z V tail tailX inp out
  have h93 : I.R 93 = tail := by
    simp [I, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  have h96 : I.R 96 = [] := by
    simp [I, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  have h116 : I.R 116 = [] := by
    simp [I, singleBranchInputWithXTail, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
  have h111 : I.R 111 = cstream A w ((List.range M).flatMap V) := by simp [I, singleBranchInputWithXTail]
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk93 : k = (93 : Fin 117)
  · subst k; simpa [inputInstallBank] using h93.symm
  · by_cases hk96 : k = (96 : Fin 117)
    · subst k; simpa [inputInstallBank] using h96.symm
    · by_cases hk116 : k = (116 : Fin 117)
      · subst k; simpa [inputInstallBank] using h116.symm
      · by_cases hk111 : k = (111 : Fin 117)
        · subst k; simpa [inputInstallBank] using h111.symm
        · simp [inputInstallBank, Function.update_apply, hk93, hk96, hk116, hk111]

/-- Install from the staging bank into the exact pre-existing interior ABI. -/
theorem inputInstallBank_exec (q l w M L b : ℕ) (X Z V : ℕ → List GaussianInt)
    (hlenV : ∀ n < M, (V n).length = L) (factors : List GaussianInt) (hfactors : factors.length = M * L)
    (v : HS 117 Q A U) (tail tailX : List (Fin (A + 4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' m, v'.user = v.user ∧ m ≤ installInputCost M L w b ∧
      Exec body installInput (mk v (inputInstallBank q l w M L b X Z V factors tail tailX inp out)) m
        (mk v' (singleBranchInputWithXTail q l w M L X Z V tail tailX inp out)) := by
  let S := inputInstallBank q l w M L b X Z V factors tail tailX inp out
  have hflat : ((List.range M).flatMap V).length = M * L := by
    have h := length_flatten_const ((List.range M).map V) (by
      intro xs hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact hlenV n (List.mem_range.mp hn))
    simpa only [List.flatMap_def, List.length_map, List.length_range] using h
  obtain ⟨v', m, hu, hm, he⟩ := installInput_exec (body := body) M L w b _ hflat v S tail
    (by simp [S, inputInstallBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputInstallBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputInstallBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputInstallBank, hfactors]) (by simp [S, inputInstallBank])
    (by simp [S, inputInstallBank]) (by simp [S, inputInstallBank])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simp [S, inputInstallBank, singleBranchInputWithXTail, Fixed.startWithTails,
          Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  congr 1
  exact inputInstallBank_frame q l w M L b X Z V factors tail tailX inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
