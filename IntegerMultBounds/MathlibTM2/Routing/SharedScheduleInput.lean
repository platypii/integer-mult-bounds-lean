module

public import IntegerMultBounds.MathlibTM2.Routing.SharedScheduleLayout

/-! Compatible initial data for a core program and its placement schedule.
The overlay preserves every core word and installs schedule inputs off that bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

noncomputable def sharedScheduleInputBank {N t₀ n A : ℕ} (src : Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (spec : Fin 3 → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) : Fin (sharedScheduleT N t₀) → List (Fin (A + 4)) :=
  Function.extend sharedCoreEmbed coreWords
    (binaryScheduleInputBank (sharedScheduleSlot src) spec bankWords Lc L B rowBits stream)

theorem sharedScheduleInputBank_core {N t₀ n A : ℕ} (src : Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (spec : Fin 3 → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (i : Fin N) :
    sharedScheduleInputBank src coreWords spec bankWords Lc L B rowBits stream (sharedCoreEmbed i) = coreWords i :=
  (sharedCoreEmbed_injective (N := N) (t₀ := t₀)).extend_apply _ _ i

theorem sharedScheduleInputBank_schedule {N t₀ n A : ℕ} (src : Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (spec : Fin 3 → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream : List (Fin (A + 4))) (hstream : coreWords src = stream)
    (r : BinaryScheduleReg t₀ 3) :
    sharedScheduleInputBank src coreWords spec bankWords Lc L B rowBits stream (sharedScheduleSlot src r) =
      binaryScheduleInputWords spec bankWords Lc L B rowBits stream r := by
  by_cases hr : r = .str
  · subst r
    rw [sharedScheduleSlot_str, sharedScheduleInputBank_core]
    exact hstream
  · have hoff : ¬∃ i, sharedCoreEmbed i = sharedScheduleSlot src r := by
      rintro ⟨i, hi⟩
      exact sharedScheduleSlot_separate src r hr i hi.symm
    change Function.extend sharedCoreEmbed coreWords _ (sharedScheduleSlot src r) = _
    rw [Function.extend_apply' _ _ _ hoff]
    exact binaryScheduleInputBank_at (sharedScheduleSlot src) (sharedScheduleSlot_injective src)
      spec bankWords Lc L B rowBits stream r

/-- Replacing the record stream leaves every placement input unchanged. -/
theorem sharedScheduleInputBank_updateStream {N t₀ n A : ℕ} (src : Fin N)
    (coreWords : Fin N → List (Fin (A + 4))) (spec : Fin 3 → BlockExchangeSpec n)
    (bankWords : Fin (swapT t₀) → List (Fin (A + 4))) (Lc L B : ℕ)
    (rowBits : List Bool) (stream replacement : List (Fin (A + 4))) :
    sharedScheduleInputBank src (Function.update coreWords src replacement)
        spec bankWords Lc L B rowBits replacement =
      Function.update (sharedScheduleInputBank src coreWords spec bankWords Lc L B rowBits stream)
        (sharedCoreEmbed src) replacement := by
  funext j
  by_cases hcore : ∃ i, sharedCoreEmbed i = j
  · obtain ⟨i, rfl⟩ := hcore
    rw [sharedScheduleInputBank_core]
    by_cases hi : i = src
    · subst i
      simp
    · rw [Function.update_of_ne hi,
        Function.update_of_ne (sharedCoreEmbed_injective.ne hi), sharedScheduleInputBank_core]
  · have hj : j ≠ sharedCoreEmbed src := by
      intro h
      exact hcore ⟨src, h.symm⟩
    rw [Function.update_of_ne hj]
    unfold sharedScheduleInputBank
    rw [Function.extend_apply' _ _ _ hcore, Function.extend_apply' _ _ _ hcore]
    by_cases hslot : ∃ r, sharedScheduleSlot src r = j
    · obtain ⟨r, rfl⟩ := hslot
      rw [binaryScheduleInputBank_at _ (sharedScheduleSlot_injective src),
        binaryScheduleInputBank_at _ (sharedScheduleSlot_injective src)]
      have hr : r ≠ .str := by
        intro h
        subst r
        exact hj (sharedScheduleSlot_str src)
      cases r <;> first | rfl | contradiction
    · unfold binaryScheduleInputBank
      rw [Function.extend_apply' _ _ _ hslot, Function.extend_apply' _ _ _ hslot]

end IntegerMultBounds.MathlibTM2.Routing
