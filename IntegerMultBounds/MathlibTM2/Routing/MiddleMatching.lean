module

public import IntegerMultBounds.MathlibTM2.Routing.MatchingShears

/-! Restrict a physical matching to a middle field when every surrounding
coordinate is fixed. The restriction is explicit subtraction, not an oracle. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {N : ℕ} (B W : ℕ) (hfit : B + W ≤ N)

def middleCoordinate (q : Fin W) : Fin N := ⟨B + q.val, by have := q.isLt; omega⟩

theorem middleCoordinate_injective : Function.Injective (middleCoordinate B W hfit) := by
  intro q r h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change B + q.val = B + r.val at hv
  omega

variable (mate : Fin N → Fin N) (hinv : Function.Involutive mate)
    (hfix : ∀ q : Fin N, q.val < B ∨ B + W ≤ q.val → mate q = q)

include hinv hfix in
theorem middleMatching_interval (q : Fin W) :
    B ≤ (mate (middleCoordinate B W hfit q)).val ∧
      (mate (middleCoordinate B W hfit q)).val < B + W := by
  by_contra h
  have hout : (mate (middleCoordinate B W hfit q)).val < B ∨
      B + W ≤ (mate (middleCoordinate B W hfit q)).val := by omega
  have heq : mate (middleCoordinate B W hfit q) = middleCoordinate B W hfit q :=
    (hfix _ hout).symm.trans (hinv _)
  have hv := congrArg Fin.val heq
  change (mate (middleCoordinate B W hfit q)).val = B + q.val at hv
  have := q.isLt
  omega

def middleMatching (q : Fin W) : Fin W :=
  ⟨(mate (middleCoordinate B W hfit q)).val - B, by
    have h := middleMatching_interval B W hfit mate hinv hfix q
    omega⟩

theorem middleMatching_coordinate (q : Fin W) :
    middleCoordinate B W hfit (middleMatching B W hfit mate hinv hfix q) =
      mate (middleCoordinate B W hfit q) := by
  apply Fin.ext
  change B + ((mate (middleCoordinate B W hfit q)).val - B) = _
  have h := middleMatching_interval B W hfit mate hinv hfix q
  omega

theorem middleMatching_involutive : Function.Involutive (middleMatching B W hfit mate hinv hfix) := by
  intro q
  apply middleCoordinate_injective B W hfit
  rw [middleMatching_coordinate, middleMatching_coordinate, hinv]

end IntegerMultBounds.MathlibTM2.Routing
