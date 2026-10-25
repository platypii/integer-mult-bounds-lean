module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! # Shared finite encoding of table-bank roles -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def code {n : ℕ} : TblR n → Fin (n + 15)
  | .v i => ⟨i.val, by omega⟩
  | .wr => ⟨n, by omega⟩
  | .wn => ⟨n + 1, by omega⟩
  | .acc => ⟨n + 2, by omega⟩
  | .z i => ⟨n + 3 + i.val, by omega⟩

theorem code_injective {n : ℕ} : Function.Injective (@code n) := by
  intro r s h
  have hv := congrArg Fin.val h
  cases r <;> cases s <;> simp only [code] at hv
  all_goals first
    | rfl
    | (congr 1; apply Fin.ext; omega)
    | omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.ForwardBankPlacement
