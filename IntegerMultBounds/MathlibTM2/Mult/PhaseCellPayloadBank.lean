module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagePayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputStage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchCanonical

/-! # Copy a borrowed per-call payload into the actual input ABI -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- After releasing the normalized raw operand, every non-output field is
exactly the empty-work input bank, independently of the computed rows. -/
theorem emptyInputBank_output_frame {A : ℕ} (q l w M L : ℕ) (X Z V : ℕ → List GaussianInt)
    (tail tailX result : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    { S with R := (Function.update (Function.update S.R 111 []) 93 result) } =
      let S₀ := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
      { S₀ with R := Function.update S₀.R 93 result } := by
  dsimp only
  have hempty : (List.range M).flatMap (fun _ : ℕ => ([] : List GaussianInt)) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intros
    rfl
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h93 : k = (93 : Fin 117)
  · subst k; simp
  · by_cases h111 : k = (111 : Fin 117)
    · subst k; simp [inputSourceBank, singleBranchInputWithXTail, hempty]
    · have hn93 : k.val ≠ 93 := fun h => h93 (Fin.ext h)
      have hn111 : k.val ≠ 111 := fun h => h111 (Fin.ext h)
      by_cases h116 : k = (116 : Fin 117)
      · subst k
        simp [inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
          Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
      · by_cases h96 : k = (96 : Fin 117)
        · subst k
          simp [inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
            Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
        · simp [inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
            Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank,
            h93, h111, hn93, hn111, h116, h96]

/-- Input buffers are empty initially. The RHS is a borrowed per-call payload
beneath the reusable setup, not part of the setup reuse key. -/
theorem stagePayloadBank_exec (q l w M L : ℕ) (X Z : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (a : GaussianInt) (weights source factors : List GaussianInt)
    (hweights : weights.length = M * L) (hsource : source.length = M * L) (hfactors : factors.length = M * L)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let tailX := csyms A w a ++ (cstream A w weights ++
      (cstream A w source ++ (cstream A w factors ++ borrowed)))
    ∃ v' m, v'.user = v.user ∧ m ≤ stagePayloadCost M L w ∧
      Exec body stagePayload
        (mk v (inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out)) m
        (mk v' (inputSourceBank q l w M L 0 X Z source factors tail tailX inp out)) := by
  dsimp only
  let tailX := csyms A w a ++ (cstream A w weights ++
    (cstream A w source ++ (cstream A w factors ++ borrowed)))
  let S := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
  let pre := cstream A w ((List.range (M + M)).flatMap (rowBank M X Z)) ++
    (csyms A w a ++ cstream A w weights)
  have hpre : pre.length = 3 * (M * L * w) + w := by
    have hh := rawRows_length (A := A) w (M + M) L (rowBank M X Z) (rowBank_length X Z hlenX hlenZ)
    simp [pre, hh, hweights, csyms]
    ring
  obtain ⟨v', m, hu, hm, he⟩ := stagePayload_exec (body := body) M L w pre
    (cstream A w source) (cstream A w factors) borrowed v S
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]; omega)
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    hpre (by simp [hsource]) (by simp [hfactors])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, pre, tailX, List.append_assoc])
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
          Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h93 : k = (93 : Fin 117)
  · subst k; simp [S, inputSourceBank]
  · by_cases h96 : k = (96 : Fin 117)
    · subst k; simp [S, inputSourceBank]
    · simp [S, inputSourceBank, Function.update_apply, h93, h96]; rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
