module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Lift
public import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy

/-!
# Banks that pad a caller with blank tapes

`Padded F ℓ`: the bank `F c` keeps the caller `c` at the slots `ℓ` (`Lift`) and is blank, with its
head at `0`, everywhere else. Appending a blank bank pads (`append`), pads compose (`comp`), and a
pad carries a sparse header bank to the sparse header bank at the lifted slots (`headerBank`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine
open IntegerMultBounds.Machine
open FixedHeaderSparseBankCopy (headerBank headerBank_target headerBank_blank)
variable {a t u w : ℕ}

/-- The bank `F c` keeps the caller `c` at the slots `ℓ` and is blank elsewhere. -/
structure Padded (F : Tapes t a → Tapes u a) (ℓ : Fin t → Fin u) : Prop extends Lift F ℓ where
  outside : ∀ c j, (∀ i, ℓ i ≠ j) → (F c).head j = 0 ∧ (F c).tape j = fun _ => blank

namespace Padded

theorem append {n : ℕ} (Y : Tapes n a) (hY : ∀ j, Y.head j = 0 ∧ Y.tape j = fun _ => blank) :
    Padded (t := t) (fun c => c.append Y) (Fin.castAdd n) where
  toLift := Lift.append Y
  outside c j hj := by
    induction j using Fin.addCases with
    | left j => exact (hj j rfl).elim
    | right j => simpa only [Tapes.append, Fin.addCases_right] using hY j

theorem comp {F : Tapes t a → Tapes u a} {G : Tapes u a → Tapes w a} {ℓ : Fin t → Fin u} {ℓ' : Fin u → Fin w}
    (h : Padded F ℓ) (h' : Padded G ℓ') : Padded (fun c => G (F c)) (fun j => ℓ' (ℓ j)) where
  toLift := h.toLift.comp h'.toLift
  outside c j hj := by
    by_cases hk : ∃ k, ℓ' k = j
    · obtain ⟨k, rfl⟩ := hk
      rw [h'.head, h'.tape]
      exact h.outside c k (fun i hi => hj i (congrArg ℓ' hi))
    · exact h'.outside (F c) j (fun k hk' => hk ⟨k, hk'⟩)

/-- Padding preserves caller head equality without comparing concrete banks. -/
theorem head_congr {F : Tapes t a → Tapes u a} {ℓ : Fin t → Fin u}
    (h : Padded F ℓ) {v w : Tapes t a} (hh : v.head = w.head) :
    (F v).head = (F w).head := by
  funext j
  by_cases hj : ∃ i, ℓ i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [h.head,h.head,hh]
  · rw [(h.outside v j (fun i hi => hj ⟨i,hi⟩)).1,
      (h.outside w j (fun i hi => hj ⟨i,hi⟩)).1]

/-- A pad carries the sparse header bank at `d` to the sparse header bank at the lifted slots. -/
theorem headerBank_eq {F : Tapes t a → Tapes u a} {ℓ : Fin t → Fin u} (h : Padded F ℓ) {n : ℕ}
    (d : Fin n → Fin t) (hd : Function.Injective d) (bs : Fin n → List Bool) :
    F (headerBank d bs) = headerBank (fun i => ℓ (d i)) bs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq (fun i => ℓ (d i)) (h.inj.comp hd)
  · intro i
    rw [h.head, h.tape]
    exact headerBank_target d hd bs i
  · intro j hj
    by_cases hk : ∃ k, ℓ k = j
    · obtain ⟨k, rfl⟩ := hk
      rw [h.head, h.tape]
      exact headerBank_blank d bs k (fun i hi => hj i (congrArg ℓ hi))
    · exact h.outside _ j (fun k hk' => hk ⟨k, hk'⟩)

end Padded
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine
