module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth

/-! Fixed-width table registers retain their volume; only emitted output grows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main

/-- Canonical table boundaries differ in stock by exactly the accumulator growth.
Variable values may change freely without changing their encoded widths. -/
theorem tblHolds.stock_balance {n T Q A W : ℕ} {U : Type}
    {rg : TblR n → Fin T}
    {wl nl : List (Fin (A+4))} {st st' : TblSt n A}
    {S F : Stacks T A} (v v' : HS T Q A U)
    (hS : tblHolds rg S (tblRho W wl nl st))
    (hF : tblHolds rg F (tblRho W wl nl st')) (hfr : tblFr rg S F) :
    mnSize (mk v' F)+st.acc.length = mnSize (mk v S)+st'.acc.length := by
  classical
  have hoff : ∀ k, k ≠ rg .acc → (F.R k).length = (S.R k).length := by
    intro k hk
    by_cases h : ∃ r, rg r = k
    · obtain ⟨r,rfl⟩ := h
      rw [hF, hS]
      cases r <;> simp_all [tblRho, length_binSyms]
    · rw [hfr.2.2.2 k (by simpa only [not_exists] using h)]
  have hs := sum_replace_embedding (fun _ : Fin 1 => rg .acc)
    (by intro i j _; exact Subsingleton.elim i j)
    (fun k => (F.R k).length) (fun k => (S.R k).length)
    (fun _ => st'.acc.length) (by intro i; rw [hF]; rfl)
    (by intro k hk; exact hoff k (by intro he; exact hk ⟨0,he.symm⟩))
  simp only [Fin.sum_univ_one] at hs
  have ha : (S.R (rg .acc)).length = st.acc.length := congrArg List.length (hS .acc)
  rw [mnSize_mk_registerBankStock, mnSize_mk_registerBankStock, hfr.1, hfr.2.1]
  simp only [registerBankStock, Finset.sum_add_distrib, hfr.2.2.1]
  omega

/-- Table instructions only prepend emitted symbols to the accumulator. -/
theorem TblIns.acc_length_le {n A W w : ℕ} (i : TblIns n) (st : TblSt n A) :
    st.acc.length ≤ (i.run A W w st).acc.length := by
  cases i <;> simp [TblIns.run]

/-- Every canonical boundary in a table execution has at most the final output volume. -/
theorem TblBig.acc_length_le {n A W w : ℕ} {c : TblCode n}
    {st st' : TblSt n A} {k : ℕ} (h : TblBig A W w c st st' k) :
    st.acc.length ≤ st'.acc.length := by
  induction h with
  | ins i st => exact i.acc_length_le st
  | seq _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopF _ => exact le_rfl
  | loopT _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Spectators and fixed-width variables are paid once, independently of atom count. -/
theorem tblHolds.stock_le {n T Q A W : ℕ} {U : Type}
    {rg : TblR n → Fin T} {wl nl : List (Fin (A+4))}
    {st st' : TblSt n A} {S F : Stacks T A} (v v' : HS T Q A U)
    (hS : tblHolds rg S (tblRho W wl nl st))
    (hF : tblHolds rg F (tblRho W wl nl st')) (hfr : tblFr rg S F)
    (hacc : st.acc.length ≤ st'.acc.length) :
    mnSize (mk v' F) ≤ mnSize (mk v S)+(st'.acc.length-st.acc.length) := by
  have h := hS.stock_balance v v' hF hfr
  omega

end IntegerMultBounds.MathlibTM2.Fast.TableVM
