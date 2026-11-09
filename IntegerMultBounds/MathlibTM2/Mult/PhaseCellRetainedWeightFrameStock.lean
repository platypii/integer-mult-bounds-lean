module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHostStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! A retained table bank has fixed volume; only the two batch archives grow. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- Shrinking packets and clock pay no additional stock; each archive gains at most `volume`. -/
theorem retainedWeight_stock_le {Q A V w : ℕ} {U : Type}
    {st st' : TblSt 48 A} {S F : Stacks 117 A} (v v' : HS 117 Q A U)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st))
    (hF : tblHolds coefficientReg F (tblRho V (List.replicate V tick) (List.replicate w tick) st'))
    (ha : st.acc = []) (ha' : st'.acc = [])
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hl : F.L = S.L)
    (hf : ∀ k, 63 ≤ k.val → k ≠ 109 → k ≠ 95 → k ≠ 113 → k ≠ 107 → F.R k = S.R k)
    (volume : ℕ)
    (h95 : (F.R 95).length ≤ (S.R 95).length+volume)
    (h113 : (F.R 113).length ≤ (S.R 113).length+volume)
    (h109 : (F.R 109).length ≤ (S.R 109).length)
    (h107 : (F.R 107).length ≤ (S.R 107).length) :
    mnSize (mk v' F) ≤ mnSize (mk v S)+2*volume := by
  have hpoint : ∀ k : Fin 117, (F.R k).length ≤ (S.R k).length+
      (if k = 95 then volume else 0)+(if k = 113 then volume else 0) := by
    intro k
    by_cases hk95 : k = 95
    · subst k; simpa using h95
    by_cases hk113 : k = 113
    · subst k; simpa using h113
    simp only [ite_eq_right hk95, ite_eq_right hk113, Nat.add_zero]
    by_cases hk109 : k = 109
    · subst k; exact h109
    by_cases hk107 : k = 107
    · subst k; exact h107
    by_cases hk : k.val < 63
    · obtain ⟨r,rfl⟩ := coefficientReg_covers k hk
      rw [hS r, hF r]
      cases r <;> simp [tblRho, length_binSyms, ha, ha']
    · rw [hf k (by omega) hk109 hk95 hk113 hk107]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpoint k)
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock,hin,hout]
  simp only [registerBankStock,Finset.sum_add_distrib,hl]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
