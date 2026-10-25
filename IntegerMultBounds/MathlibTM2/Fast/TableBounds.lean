module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Table instructions preserve bounded variable values. This lets a table bank
survive a host emission and be reused by another independently verified row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {n A W w : ℕ}

theorem TblIns.run_bounded (i : TblIns n) (st : TblSt n A)
    (h : ∀ j, st.val j < 2^W) : ∀ j, (i.run A W w st).val j < 2^W := by
  have upd (k : Fin n) (v : ℕ) (hv : v < 2^W) : ∀ j, Function.update st.val k v j < 2^W := by
    intro j
    by_cases hj : j = k
    · simpa [hj] using hv
    · simpa [hj] using h j
  cases i with
  | add a b c => exact upd c _ (Nat.mod_lt _ (Nat.two_pow_pos W))
  | sub a b c => exact upd c _ (Nat.mod_lt _ (Nat.two_pow_pos W))
  | mul a b c => exact upd c _ (Nat.mod_lt _ (Nat.two_pow_pos W))
  | div a b c => exact upd c _ ((Nat.div_le_self _ _).trans_lt (h a))
  | mod a b c => exact upd c _ ((Nat.mod_le _ _).trans_lt (h a))
  | copy a c => exact upd c _ (h a)
  | zero c => exact upd c 0 (Nat.two_pow_pos W)
  | inc c => exact upd c _ (Nat.mod_lt _ (Nat.two_pow_pos W))
  | emit a b => exact h

theorem TblBig.bounded {c : TblCode n} {st st' : TblSt n A} {k : ℕ}
    (h : TblBig A W w c st st' k) (hst : ∀ j, st.val j < 2^W) : ∀ j, st'.val j < 2^W := by
  induction h with
  | ins i st => exact i.run_bounded st hst
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hst)
  | iteT _ _ ih => exact ih hst
  | iteF _ _ ih => exact ih hst
  | loopF _ => exact hst
  | loopT _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hst)

theorem TblDo.bounded {c : TblCode n} {st : TblSt n A} {Post : TblSt n A → Prop} {K : ℕ}
    (h : TblDo A W w c st Post K) (hst : ∀ j, st.val j < 2^W) :
    TblDo A W w c st (fun st' => Post st' ∧ ∀ j, st'.val j < 2^W) K := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  exact ⟨st', k, hb, ⟨hp, hb.bounded hst⟩, hk⟩

end IntegerMultBounds.MathlibTM2.Fast.TableVM
