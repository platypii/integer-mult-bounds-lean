module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRetainedRound

/-! Recover p from the retained kernel length with fifteen binary divisions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblRecoverRoundPrecision : TblCode 25 :=
  tblBlock 25 ([.zero 9,.inc 9,.inc 9]++List.replicate 14 (.div 0 9 0)) (.div 0 9 0)

theorem tblRecoverRoundPrecision_do {A W e p : ℕ} (st : TblSt 25 A)
    (hP : st.val 0 = 2^15*p) (hroom : 2 < 2^W) (hfit : ∀ i, st.val i < 2^W) :
    TblDo A W e tblRecoverRoundPrecision st (fun z =>
      z.val 0 = p ∧ z.val 18 = st.val 18 ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W) 18 := by
  have hW : W ≠ 0 := by intro he; subst W; norm_num at hroom
  have hr : TblDo A W e tblRecoverRoundPrecision st
      (fun z => z.val = Function.update (Function.update st.val 9 2) 0 p ∧ z.acc = st.acc) 18 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits,TblIns.exact,List.replicate_succ,hW,hroom]
    · constructor
      · simp [tblExactList,TblIns.exact,List.replicate_succ,
          hP,Nat.div_div_eq_div_mul]
      · simp [tblExactList,TblIns.exact,List.replicate_succ]
  exact (tblDo_with_fits hr hfit).mono
    (fun _ ⟨⟨hv,ha⟩,hf⟩ => ⟨by simp [hv],by simp [hv],ha,hf⟩) (le_refl _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
