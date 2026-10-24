module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueStep
public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountBank

/-! The closed counted bank projects back to the fixed compiler bank each round.
Only unused count/output slots and the live residue change inside its core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {A : ℕ}

def canonicalResidueCoreBank (R : Fin 126 → List (Fin (A + 4))) (L i : ℕ)
    (count output : List (Fin (A + 4))) : Fin 126 → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R 107 count) 116 (binSyms L i)) 98 output

theorem canonicalResidueCoreBank_keep (R : Fin 126 → List (Fin (A + 4))) (L i : ℕ)
    (count output : List (Fin (A + 4))) (j : Fin 126) (h107 : j ≠ 107) (h116 : j ≠ 116) (h98 : j ≠ 98) :
    canonicalResidueCoreBank R L i count output j = R j := by
  simp [canonicalResidueCoreBank, h107, h116, h98]

theorem canonicalResidueBank_projection (R : Fin 163 → List (Fin (A + 4)))
    (core : Fin 126 → List (Fin (A + 4)))
    (hR : (fun j => R (canonicalResidueCoreSlot j)) = matchingProductionBank core [] [] [] [])
    (L i : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4))) :
    (fun j => indexedCountBank R 107 162 116 98 L cs profile i (canonicalResidueCoreSlot j)) =
      matchingProductionBank
        (canonicalResidueCoreBank core L i (cs.drop i) (indexedCountOutput profile i ++ R 98)) [] [] [] [] := by
  simp only [canonicalResidueCoreBank, matchingProductionBank_updateCore]
  funext j
  have base := congrFun hR j
  have hsaved : canonicalResidueCoreSlot j ≠ 162 := by
    intro h
    have hv := congrArg (fun x : Fin 163 => x.val) h
    change j.val = 162 at hv
    have := j.isLt
    omega
  have h107 : (107 : Fin 163) = canonicalResidueCoreSlot 107 := rfl
  have h116 : (116 : Fin 163) = canonicalResidueCoreSlot 116 := rfl
  have h98 : (98 : Fin 163) = canonicalResidueCoreSlot 98 := rfl
  simp only [indexedCountBank, Function.update_apply, hsaved, ite_false, h107, h116, h98,
    canonicalResidueCoreSlot_injective.eq_iff, matchingCoreEmbed]
  change (if j = 98 then _ else if j = 116 then _ else if j = 107 then _ else R (canonicalResidueCoreSlot j)) = _
  by_cases hd : j = 98
  · subst j; simp
  by_cases hi : j = 116
  · subst j; simp
  by_cases hc : j = 107
  · subst j; simp
  · simpa [hd, hi, hc] using base

theorem canonicalResidueCoreBank_blank (R : Fin 126 → List (Fin (A + 4)))
    (hblank : ∀ j : Fin 126, j.val < 98 → j ≠ 57 → j ≠ 70 → j ≠ 84 → j ≠ 85 → R j = [])
    (L i : ℕ) (count output : List (Fin (A + 4)))
    (j : Fin 126) (hj : j.val < 98) (h57 : j ≠ 57) (h70 : j ≠ 70) (h84 : j ≠ 84) (h85 : j ≠ 85) :
    canonicalResidueCoreBank R L i count output j = [] := by
  rw [canonicalResidueCoreBank_keep R L i count output j
    (by intro h; subst j; simp at hj) (by intro h; subst j; simp at hj) (by intro h; subst j; simp at hj)]
  exact hblank j hj h57 h70 h84 h85

theorem canonicalResidueCoreBank_geometry (R : Fin 126 → List (Fin (A + 4)))
    (hblank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → R (canonicalPermutationGeometrySlot j) = [])
    (L i : ℕ) (count output : List (Fin (A + 4)))
    (j : Fin 28) (h0 : j ≠ 0) (h9 : j ≠ 9) (h18 : j ≠ 18) :
    canonicalResidueCoreBank R L i count output (canonicalPermutationGeometrySlot j) = [] := by
  have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hj9 : j.val ≠ 9 := fun h => h9 (Fin.ext h)
  have hj18 : j.val ≠ 18 := fun h => h18 (Fin.ext h)
  rw [canonicalResidueCoreBank_keep R L i count output (canonicalPermutationGeometrySlot j)
    (by simp [canonicalPermutationGeometrySlot, hj0, hj9, Fin.ext_iff]; omega)
    (by simp [canonicalPermutationGeometrySlot, hj0, hj9, Fin.ext_iff]; omega)
    (by simp [canonicalPermutationGeometrySlot, hj0, hj9, Fin.ext_iff])]
  exact hblank j h0 h9 h18

end IntegerMultBounds.MathlibTM2.Routing
