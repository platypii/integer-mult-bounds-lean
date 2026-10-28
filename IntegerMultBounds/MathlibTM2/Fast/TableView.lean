module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! A smaller scalar machine shares a selected variable view of an existing bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def TblR.rename {m n : ℕ} (f : Fin m → Fin n) : TblR m → TblR n
  | .v i => .v (f i)
  | .wr => .wr
  | .wn => .wn
  | .acc => .acc
  | .z i => .z i

theorem TblR.rename_injective {m n : ℕ} {f : Fin m → Fin n} (hf : Function.Injective f) :
    Function.Injective (TblR.rename f) := by
  intro r t he
  cases r <;> cases t <;> simp_all [TblR.rename,hf.eq_iff]

theorem tblRho_restrict {m n A : ℕ} (f : Fin m → Fin n) (W : ℕ)
    (wl nl : List (Fin (A+4))) (st : TblSt n A) (r : TblR m) :
    tblRho W wl nl (st.restrict f) r = tblRho W wl nl st (r.rename f) := by
  cases r <;> rfl

theorem tblHolds_restrict {m n T A : ℕ} (f : Fin m → Fin n) (rg : TblR n → Fin T)
    (W : ℕ) (wl nl : List (Fin (A+4))) (st : TblSt n A) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    tblHolds (rg ∘ TblR.rename f) S (tblRho W wl nl (st.restrict f)) := by
  intro r
  rw [tblRho_restrict]
  exact hS (r.rename f)

end IntegerMultBounds.MathlibTM2.Fast.TableVM
