module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyInputViews

/-! Construct the packed caller's ordinary queue and headers around a native
factory bank, with all three placement views proved structurally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {A : ℕ}

/-- The publication workspace is blank except for the binary radius word. -/
def packedKeyPublicationInput (S : Stacks 242 A) (V radius : ℕ) : Stacks 263 A :=
  let B := extendStacks (by decide : 242 ≤ 263) S
  {B with R := Function.update B.R 252 (binSyms V radius)}

/-- Ordinary unary headers and the complex input queue, outside the numerical
bank. Registers above the packet-width header are fresh workspace. -/
def packedKeyDescriptorInput (B : Stacks 263 A) (p W N packet : ℕ)
    (source : List (Fin (A+4))) : Stacks 276 A :=
  {extendStacks (by decide : 263 ≤ 276) B with
    R := fun k => if hk : k.val < 263 then B.R ⟨k.val,hk⟩ else
      match k.val with
      | 263 => source
      | 264 => List.replicate N tick
      | 265 => List.replicate W tick
      | 266 => List.replicate p tick
      | 267 => List.replicate packet tick
      | _ => []}

theorem packedKeyDescriptorInput_view (B : Stacks 263 A) (p W N packet : ℕ)
    (source : List (Fin (A+4))) :
    embStk packedKeySolverReg (packedKeyDescriptorInput B p W N packet source) = B := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk, packedKeyDescriptorInput, packedKeySolverReg, extendStacks, i.isLt]
  · funext i
    simp [embStk, packedKeyDescriptorInput, packedKeySolverReg, i.isLt]

theorem packedKeyPublicationInput_view (S : Stacks 242 A) (V radius : ℕ) :
    embStk packedHaloPublishedReg (packedKeyPublicationInput S V radius) =
      extendStacks (by decide : 242 ≤ 249) S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk, packedKeyPublicationInput, packedHaloPublishedReg, extendStacks]
  · funext i
    have hne : packedHaloPublishedReg i ≠ (252 : Fin 263) := by
      intro h
      have hv := congrArg Fin.val h
      have := i.isLt
      change i.val = 252 at hv
      omega
    dsimp only [embStk, packedKeyPublicationInput, Function.comp_apply]
    rw [Function.update_of_ne hne]
    simp [packedHaloPublishedReg, extendStacks]

theorem packedKeyPublicationInput_native (S : Stacks 242 A) (V radius : ℕ) (i : Fin 242) :
    (packedKeyPublicationInput S V radius).R (Fin.castLE (by decide : 242 ≤ 263) i) = S.R i := by
  have hne : Fin.castLE (by decide : 242 ≤ 263) i ≠ (252 : Fin 263) := by
    intro h
    have hv := congrArg Fin.val h
    have := i.isLt
    change i.val = 252 at hv
    omega
  simp [packedKeyPublicationInput, hne, extendStacks, i.isLt]

theorem packedKeyPublicationInput_radius (S : Stacks 242 A) (V radius : ℕ) :
    (packedKeyPublicationInput S V radius).R 252 = binSyms V radius := by
  simp [packedKeyPublicationInput]

theorem packedKeyPublicationInput_fresh (S : Stacks 242 A) (V radius : ℕ)
    (i : Fin 263) (hi : 242 ≤ i.val) (hne : i ≠ 252) :
    (packedKeyPublicationInput S V radius).R i = [] := by
  simp [packedKeyPublicationInput, hne, extendStacks, show ¬ i.val < 242 by omega]

theorem packedKeyDescriptorInput_left (S : Stacks 242 A) (V radius p W N packet : ℕ)
    (source : List (Fin (A+4))) (hleft : ∀ i, S.L i = []) (i : Fin 276) :
    (packedKeyDescriptorInput (packedKeyPublicationInput S V radius) p W N packet source).L i = [] := by
  simp [packedKeyDescriptorInput, packedKeyPublicationInput, extendStacks, hleft]

/-- Every enclosing bank view is derived from one native factory bank. -/
theorem packedKeyDescriptorInput_views (S : Stacks 242 A) (V radius p W N packet : ℕ)
    (source : List (Fin (A+4))) :
    PackedKeyBankViews
      (packedKeyDescriptorInput (packedKeyPublicationInput S V radius) p W N packet source)
      (packedKeyPublicationInput S V radius) (extendStacks (by decide : 242 ≤ 249) S) S := by
  refine ⟨packedKeyDescriptorInput_view _ _ _ _ _ _, packedKeyPublicationInput_view _ _ _, ?_⟩
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp [embStk, packedHaloBatchReg, extendStacks]
  · funext i
    simp [embStk, packedHaloBatchReg, extendStacks]

theorem packedKeyDescriptorInput_native (B : Stacks 263 A) (p W N packet : ℕ)
    (source : List (Fin (A+4))) (i : Fin 263) :
    (packedKeyDescriptorInput B p W N packet source).R (packedKeySolverReg i) = B.R i := by
  exact congrArg (fun S : Stacks 263 A => S.R i) (packedKeyDescriptorInput_view B p W N packet source)

theorem packedKeyDescriptorInput_headers (B : Stacks 263 A) (p W N packet : ℕ)
    (source : List (Fin (A+4))) :
    let M := packedKeyDescriptorInput B p W N packet source
    M.R 263 = source ∧ M.R 264 = List.replicate N tick ∧
      M.R 265 = List.replicate W tick ∧ M.R 266 = List.replicate p tick ∧
      M.R 267 = List.replicate packet tick := by
  simp [packedKeyDescriptorInput]

theorem packedKeyDescriptorInput_fresh (B : Stacks 263 A) (p W N packet : ℕ)
    (source : List (Fin (A+4))) (i : Fin 276) (hi : 268 ≤ i.val) :
    (packedKeyDescriptorInput B p W N packet source).R i = [] := by
  simp only [packedKeyDescriptorInput, show ¬ i.val < 263 by omega, dite_false]
  split <;> first | rfl | omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
