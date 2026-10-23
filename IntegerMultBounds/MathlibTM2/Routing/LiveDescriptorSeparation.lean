module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorLayout

/-! The concrete shared workspace satisfies the live compiler's alias and
separation conditions. Core output writes preserve every auxiliary tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

noncomputable section

variable {N J A : ℕ}

theorem liveBankProfile_input (j : Fin J) :
    liveBankProfile (N := N) j (.coordinate .dst) = liveBankCoordinate .src := rfl

theorem liveBankRun_input : liveBankRuns (N := N) (J := J) .src = liveBankCoordinate .dst := rfl

theorem liveBankZero_block : liveBankZero (N := N) (J := J) .dst = liveBankRuns .block := rfl

theorem liveBankProfile_saved (j : Fin J) (r : GroupedProfileReg) :
    liveDescriptorAux (N := N) .profileSaved ≠ liveBankProfile j r := by
  change liveDescriptorAux (N := N) .profileSaved ≠ liveDescriptorAux (liveProfileRole j r)
  apply liveDescriptorAux_injective.ne
  cases r <;> try simp [liveProfileRole]
  rename_i c
  cases c <;> try simp
  rename_i a
  cases a <;> simp

theorem liveBankCoordinate_saved (r : SparseCoordinateReg) :
    liveDescriptorAux (N := N) (J := J) .coordinateSaved ≠ liveBankCoordinate r := by
  cases r <;> simp [liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankZero_coordinate (r : BinaryZeroReg) :
    liveBankZero (N := N) (J := J) r ≠ liveBankCoordinate .dst := by
  cases r <;> simp [liveBankZero, liveZeroRole, liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankRun_coordinate (r : SelectorRunReg) (hr : r ≠ .src) :
    liveBankRuns (N := N) (J := J) r ≠ liveBankCoordinate .dst := by
  cases r <;> simp_all [liveBankRuns, liveRunRole, liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankZero_input (r : BinaryZeroReg) :
    liveBankZero (N := N) (J := J) r ≠ liveBankCoordinate .src := by
  cases r <;> simp [liveBankZero, liveZeroRole, liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankRun_coordinateInput (r : SelectorRunReg) :
    liveBankRuns (N := N) (J := J) r ≠ liveBankCoordinate .src := by
  cases r <;> simp [liveBankRuns, liveRunRole, liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankMask_input (j : Fin J) (r : BinaryMaskReg) :
    liveBankMask (N := N) j r ≠ liveBankCoordinate .src := by
  cases r <;> simp [liveBankMask, liveMaskRole, liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankDense_archive :
    liveBankRuns (N := N) (J := J) .dst ≠ liveDescriptorAux .archive := by
  simp [liveBankRuns, liveRunRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankDense_mask (j : Fin J) (r : BinaryMaskReg) :
    liveBankRuns (N := N) .dst ≠ liveBankMask j r := by
  cases r <;> simp [liveBankRuns, liveRunRole, liveBankMask, liveMaskRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankArchive_mask (j : Fin J) (r : BinaryMaskReg) :
    liveDescriptorAux (N := N) .archive ≠ liveBankMask j r := by
  cases r <;> simp [liveBankMask, liveMaskRole, liveDescriptorAux_injective.eq_iff]

theorem liveBankArchive_coordinateInput :
    liveDescriptorAux (N := N) (J := J) .archive ≠ liveBankCoordinate .src := by
  simp [liveBankCoordinate, liveCoordinateRole, liveDescriptorAux_injective.eq_iff]

theorem liveDescriptorAux_update_core (R : Fin (liveDescriptorT N J) → List (Fin (A + 4)))
    (i : Fin N) (word : List (Fin (A + 4))) (r : LiveDescriptorRole J) :
    Function.update R (liveDescriptorCore i) word (liveDescriptorAux r) = R (liveDescriptorAux r) :=
  Function.update_of_ne (liveDescriptorCore_aux i r).symm _ _

end
end IntegerMultBounds.MathlibTM2.Routing
