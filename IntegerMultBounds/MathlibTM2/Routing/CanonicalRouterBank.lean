module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBulk
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalCore

/-! A common core bank for bulk and terminal routing. Exactly the record stream
is shared; every nonstream terminal register lies beyond the complete bulk bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
noncomputable section

abbrev canonicalRouterBulkT := originalMatchingScheduleT 6
abbrev canonicalRouterCommonT := canonicalRouterBulkT + canonicalTerminalT

def canonicalRouterBulkEmbed (j : Fin canonicalRouterBulkT) : Fin canonicalRouterCommonT :=
  Fin.castAdd canonicalTerminalT j

def canonicalRouterTerminalEmbed (j : Fin canonicalTerminalT) : Fin canonicalRouterCommonT :=
  if j = canonicalTerminalRouter .str then canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)
  else Fin.natAdd canonicalRouterBulkT j

@[simp] theorem canonicalRouterTerminalEmbed_stream :
    canonicalRouterTerminalEmbed (canonicalTerminalRouter .str) =
      canonicalRouterBulkEmbed (originalMatchingScheduleStream 6) := by
  simp only [canonicalRouterTerminalEmbed, ite_true]

theorem canonicalRouterBulkEmbed_injective : Function.Injective canonicalRouterBulkEmbed :=
  Fin.castAdd_injective canonicalRouterBulkT canonicalTerminalT

theorem canonicalRouterTerminalEmbed_separate (j : Fin canonicalTerminalT)
    (hj : j ≠ canonicalTerminalRouter .str) (i : Fin canonicalRouterBulkT) :
    canonicalRouterTerminalEmbed j ≠ canonicalRouterBulkEmbed i := by
  intro he
  have hv := congrArg (fun x : Fin canonicalRouterCommonT => x.val) he
  simp only [canonicalRouterTerminalEmbed, ite_eq_right hj, canonicalRouterBulkEmbed,
    Fin.val_natAdd, Fin.val_castAdd] at hv
  have := i.isLt
  omega

theorem canonicalRouterTerminalEmbed_injective : Function.Injective canonicalRouterTerminalEmbed := by
  intro i j he
  by_cases hi : i = canonicalTerminalRouter .str
  · subst i
    by_cases hj : j = canonicalTerminalRouter .str
    · exact hj.symm
    · exact (canonicalRouterTerminalEmbed_separate j hj _
        (he.symm.trans canonicalRouterTerminalEmbed_stream)).elim
  · by_cases hj : j = canonicalTerminalRouter .str
    · subst j
      exact (canonicalRouterTerminalEmbed_separate i hi _
        (he.trans canonicalRouterTerminalEmbed_stream)).elim
    · have hv := congrArg (fun x : Fin canonicalRouterCommonT => x.val) he
      simp only [canonicalRouterTerminalEmbed, ite_eq_right hi, ite_eq_right hj, Fin.val_natAdd] at hv
      apply Fin.ext
      omega

def canonicalRouterTerminalLift (extra : ℕ) (j : Fin canonicalTerminalT) : Fin (canonicalRouterCommonT + extra) :=
  Fin.castAdd extra (canonicalRouterTerminalEmbed j)

theorem canonicalRouterTerminalLift_injective (extra : ℕ) :
    Function.Injective (canonicalRouterTerminalLift extra) :=
  (Fin.castAdd_injective canonicalRouterCommonT extra).comp canonicalRouterTerminalEmbed_injective

@[simp] theorem canonicalRouterTerminalLift_stream (extra : ℕ) :
    canonicalRouterTerminalLift extra (canonicalTerminalRouter .str) =
      Fin.castAdd extra (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) := by
  unfold canonicalRouterTerminalLift
  rw [canonicalRouterTerminalEmbed_stream]

def canonicalRouterCommonBank {A : ℕ}
    (bulk : Fin canonicalRouterBulkT → List (Fin (A + 4)))
    (terminal : Fin canonicalTerminalT → List (Fin (A + 4))) :
    Fin canonicalRouterCommonT → List (Fin (A + 4)) :=
  Function.extend canonicalRouterBulkEmbed bulk
    (Function.extend canonicalRouterTerminalEmbed terminal (fun _ => []))

theorem canonicalRouterCommonBank_bulk {A : ℕ}
    (bulk : Fin canonicalRouterBulkT → List (Fin (A + 4)))
    (terminal : Fin canonicalTerminalT → List (Fin (A + 4))) (i : Fin canonicalRouterBulkT) :
    canonicalRouterCommonBank bulk terminal (canonicalRouterBulkEmbed i) = bulk i :=
  canonicalRouterBulkEmbed_injective.extend_apply _ _ i

theorem canonicalRouterCommonBank_terminal {A : ℕ}
    (bulk : Fin canonicalRouterBulkT → List (Fin (A + 4)))
    (terminal : Fin canonicalTerminalT → List (Fin (A + 4)))
    (hstream : bulk (originalMatchingScheduleStream 6) = terminal (canonicalTerminalRouter .str))
    (j : Fin canonicalTerminalT) :
    canonicalRouterCommonBank bulk terminal (canonicalRouterTerminalEmbed j) = terminal j := by
  by_cases hj : j = canonicalTerminalRouter .str
  · subst j
    rw [canonicalRouterTerminalEmbed_stream, canonicalRouterCommonBank_bulk]
    exact hstream
  · unfold canonicalRouterCommonBank
    rw [Function.extend_apply']
    · exact canonicalRouterTerminalEmbed_injective.extend_apply _ _ j
    · rintro ⟨i, hi⟩
      exact canonicalRouterTerminalEmbed_separate j hj i hi.symm

/-- Sharing the stream does not add its payload to either metadata budget. -/
theorem canonicalRouterCommonBank_length_le {A : ℕ}
    (bulk : Fin canonicalRouterBulkT → List (Fin (A + 4)))
    (terminal : Fin canonicalTerminalT → List (Fin (A + 4))) (C D : ℕ)
    (hbulk : ∀ j, j ≠ originalMatchingScheduleStream 6 → (bulk j).length ≤ C)
    (hterminal : ∀ j, j ≠ canonicalTerminalRouter .str → (terminal j).length ≤ D)
    (j : Fin canonicalRouterCommonT)
    (hj : j ≠ canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) :
    (canonicalRouterCommonBank bulk terminal j).length ≤ C + D := by
  by_cases hb : ∃ i, canonicalRouterBulkEmbed i = j
  · obtain ⟨i, rfl⟩ := hb
    rw [canonicalRouterCommonBank_bulk]
    have hi := hbulk i (fun he => hj (congrArg canonicalRouterBulkEmbed he))
    omega
  · unfold canonicalRouterCommonBank
    rw [Function.extend_apply' _ _ _ hb]
    by_cases ht : ∃ i, canonicalRouterTerminalEmbed i = j
    · obtain ⟨i, rfl⟩ := ht
      rw [canonicalRouterTerminalEmbed_injective.extend_apply]
      have hi : i ≠ canonicalTerminalRouter .str := by
        intro he
        subst i
        exact hj canonicalRouterTerminalEmbed_stream
      exact (hterminal i hi).trans (Nat.le_add_left _ _)
    · rw [Function.extend_apply' _ _ _ ht]
      exact Nat.zero_le _


/-- A completed phase changes only the shared stream seen by either projection. -/
theorem canonicalRouterCommonBank_updateStream {A : ℕ}
    (bulk : Fin canonicalRouterBulkT → List (Fin (A + 4)))
    (terminal : Fin canonicalTerminalT → List (Fin (A + 4))) (replacement : List (Fin (A + 4))) :
    canonicalRouterCommonBank
      (Function.update bulk (originalMatchingScheduleStream 6) replacement)
      (Function.update terminal (canonicalTerminalRouter .str) replacement) =
    Function.update (canonicalRouterCommonBank bulk terminal)
      (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6)) replacement := by
  funext j
  by_cases hb : ∃ i, canonicalRouterBulkEmbed i = j
  · obtain ⟨i, rfl⟩ := hb
    rw [canonicalRouterCommonBank_bulk]
    by_cases hi : i = originalMatchingScheduleStream 6
    · subst i
      simp only [Function.update_self]
    · rw [Function.update_of_ne hi,
        Function.update_of_ne (canonicalRouterBulkEmbed_injective.ne hi), canonicalRouterCommonBank_bulk]
  · have hj : j ≠ canonicalRouterBulkEmbed (originalMatchingScheduleStream 6) := by
      intro he
      exact hb ⟨_, he.symm⟩
    rw [Function.update_of_ne hj]
    unfold canonicalRouterCommonBank
    rw [Function.extend_apply' _ _ _ hb, Function.extend_apply' _ _ _ hb]
    by_cases ht : ∃ i, canonicalRouterTerminalEmbed i = j
    · obtain ⟨i, rfl⟩ := ht
      rw [canonicalRouterTerminalEmbed_injective.extend_apply, canonicalRouterTerminalEmbed_injective.extend_apply]
      apply Function.update_of_ne
      intro hi
      subst i
      exact hj canonicalRouterTerminalEmbed_stream
    · rw [Function.extend_apply' _ _ _ ht, Function.extend_apply' _ _ _ ht]

end
end IntegerMultBounds.MathlibTM2.Routing
