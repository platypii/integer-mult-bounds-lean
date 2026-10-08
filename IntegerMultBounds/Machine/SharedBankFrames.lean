import IntegerMultBounds.Machine.SharedBank

/-! Projection and clearing laws for permanent shared banks. All complementary
complete tapes and heads are retained in their original physical slots. -/
namespace IntegerMultBounds.Machine.SharedBankFrames
open SharedBank
variable {k t u a : ℕ}
noncomputable section

theorem payload_identity (v : Tapes k a) : payload v id = v := by
  cases v
  rfl

theorem strip_identity (v : Tapes k a) : strip v id = empty k a := by
  unfold strip empty
  congr 1 <;> funext i <;> simp

theorem payload_append_left (v : Tapes t a) (w : Tapes u a) (slots : Fin k → Fin t) :
    payload (v.append w) (fun i => Fin.castAdd u (slots i)) = payload v slots := by
  unfold payload Tapes.append
  simp only [Fin.addCases_left]

theorem strip_append_left (v : Tapes t a) (w : Tapes u a) (slots : Fin k → Fin t) :
    strip (v.append w) (fun i => Fin.castAdd u (slots i)) = (strip v slots).append w := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [strip,Tapes.append,Fin.ext_iff]
  | right i =>
    have hn : ¬∃ j, Fin.castAdd u (slots j) = Fin.natAdd t i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      have hh := (slots j).isLt
      omega
    simp [strip,Tapes.append,hn]

/-- The permanent slots precede both private banks. -/
def commonSlots (k t u : ℕ) (j : Fin k) : Fin ((k+t)+u) :=
  Fin.castAdd u (Fin.castAdd t j)

theorem commonSlots_injective (k t u : ℕ) : Function.Injective (commonSlots k t u) :=
  (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)

theorem payload_common (common : Tapes k a) (left : Tapes t a) (right : Tapes u a) :
    payload ((common.append left).append right) (commonSlots k t u) = common := by
  change payload ((common.append left).append right) (fun j => Fin.castAdd u (Fin.castAdd t j)) = _
  rw [payload_append_left]
  change payload (common.append left) (fun j => Fin.castAdd t (id j)) = _
  rw [payload_append_left,payload_identity]

theorem strip_common (common : Tapes k a) (left : Tapes t a) (right : Tapes u a) :
    strip ((common.append left).append right) (commonSlots k t u) =
      ((empty k a).append left).append right := by
  change strip ((common.append left).append right) (fun j => Fin.castAdd u (Fin.castAdd t j)) = _
  rw [strip_append_left]
  change (strip (common.append left) (fun j => Fin.castAdd t (id j))).append right = _
  rw [strip_append_left,strip_identity]

/-- Appending wholly blank banks produces one wholly blank bank. -/
theorem empty_append (t u a : ℕ) :
    (empty t a).append (empty u a) = empty (t+u) a := by
  unfold empty Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]

theorem strip_empty (slots : Fin k → Fin t) : strip (empty t a) slots = empty t a := by
  unfold strip empty
  congr 1 <;> funext i <;> simp

/-- A stage with blank private input has literally no nonblank input outside
its permanent common bank. -/
theorem strip_common_blank (common : Tapes k a) (t u : ℕ) :
    strip ((common.append (empty t a)).append (empty u a)) (commonSlots k t u) =
      empty ((k+t)+u) a := by
  rw [strip_common,empty_append,empty_append]

theorem strip_common_single_blank (common : Tapes k a) (t : ℕ) :
    strip (common.append (empty t a)) (fun i => Fin.castAdd t i) = empty (k+t) a := by
  change strip (common.append (empty t a)) (fun i => Fin.castAdd t (id i)) = _
  rw [strip_append_left,strip_identity,empty_append]

/-- Once selected cells have been cleared, a second clearing changes nothing. -/
theorem strip_idempotent (v : Tapes t a) (slots : Fin k → Fin t) :
    strip (strip v slots) slots = strip v slots := by
  unfold strip
  congr 1 <;> funext i <;> by_cases h : ∃ j, slots j = i <;> simp [h]

/-- Clearing never changes an unselected tape or its head. -/
theorem strip_frame (v : Tapes t a) (slots : Fin k → Fin t) (i : Fin t)
    (hi : ∀ j, slots j ≠ i) :
    (strip v slots).head i = v.head i ∧ (strip v slots).tape i = v.tape i := by
  have hn : ¬∃ j, slots j = i := by rintro ⟨j,hj⟩; exact hi j hj
  simp [strip,hn]

end
end IntegerMultBounds.Machine.SharedBankFrames
