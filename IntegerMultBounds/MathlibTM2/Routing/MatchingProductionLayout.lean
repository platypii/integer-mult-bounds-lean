module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionSetup

/-! Thirty-six fixed production tapes outside the generated core. Prefix output
shares the gather input; all remaining workspaces are disjoint. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

def matchingCoreEmbed (N : ℕ) (j : Fin N) : Fin (N + 36) := Fin.castAdd 36 j

def matchingGatherSlot (N : ℕ) (j : Fin 18) : Fin (N + 36) :=
  ⟨N + 7 + j.val, by have := j.isLt; omega⟩

def matchingGenerateSlot (N : ℕ) (j : Fin 11) : Fin (N + 36) :=
  ⟨N + 25 + j.val, by have := j.isLt; omega⟩

def matchingExtractSlot (N : ℕ) (j : Fin 8) : Fin (N + 36) :=
  ⟨N + (if j.val = 6 then 21 else if j.val < 6 then j.val else j.val - 1), by
    have := j.isLt
    split_ifs <;> omega⟩

theorem matchingCoreEmbed_injective (N : ℕ) : Function.Injective (matchingCoreEmbed N) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (N + 36) => x.val) h)

theorem matchingGatherSlot_injective (N : ℕ) : Function.Injective (matchingGatherSlot N) := by
  intro i j h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  apply Fin.ext
  dsimp only [matchingGatherSlot] at hv
  omega

theorem matchingGenerateSlot_injective (N : ℕ) : Function.Injective (matchingGenerateSlot N) := by
  intro i j h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  apply Fin.ext
  dsimp only [matchingGenerateSlot] at hv
  omega

theorem matchingExtractSlot_injective (N : ℕ) : Function.Injective (matchingExtractSlot N) := by
  intro i j h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  dsimp only [matchingExtractSlot] at hv
  split_ifs at hv <;> omega

theorem matchingExtractSlot_join (N : ℕ) : matchingExtractSlot N 6 = matchingGatherSlot N 14 := by
  apply Fin.ext
  simp [matchingExtractSlot, matchingGatherSlot, Nat.add_assoc]

theorem matchingGenerateSlot_gather (N : ℕ) (i : Fin 11) (j : Fin 18) :
    matchingGenerateSlot N i ≠ matchingGatherSlot N j := by
  intro h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  have hj := j.isLt
  dsimp only [matchingGenerateSlot, matchingGatherSlot] at hv
  omega

theorem matchingCoreEmbed_gather (N : ℕ) (i : Fin N) (j : Fin 18) :
    matchingCoreEmbed N i ≠ matchingGatherSlot N j := by
  intro h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  have hi := i.isLt
  change i.val = N + 7 + j.val at hv
  omega

theorem matchingCoreEmbed_generate (N : ℕ) (i : Fin N) (j : Fin 11) :
    matchingCoreEmbed N i ≠ matchingGenerateSlot N j := by
  intro h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  have hi := i.isLt
  change i.val = N + 25 + j.val at hv
  omega

theorem matchingCoreEmbed_extract (N : ℕ) (i : Fin N) (j : Fin 8) :
    matchingCoreEmbed N i ≠ matchingExtractSlot N j := by
  intro h
  have hv := congrArg (fun x : Fin (N + 36) => x.val) h
  have hi := i.isLt
  change i.val = N + (if j.val = 6 then 21 else if j.val < 6 then j.val else j.val - 1) at hv
  split_ifs at hv <;> omega

end IntegerMultBounds.MathlibTM2.Routing
