module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseArguments
public import IntegerMultBounds.NLogN.PhaseCellHaloMask

/-! Compute the original phases at both guard-band endpoints using naturals. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloMaskPhaseCode : TblCode 16 :=
  tblBlock 16 [.sub 3 2 9, .add 3 2 10, .sub 1 0 6, .add 0 0 7, .add 6 6 8,
    .mul 8 9 11, .add 11 0 11, .div 11 7 11, .mul 8 10 12, .add 12 0 12] (.div 12 7 12)

theorem haloMaskPhaseCode_do {A V w s t band k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hb : st.val 2 = band) (hk : st.val 3 = k)
    (hst : s ≤ t) (hband : band ≤ k)
    (hsV : 2*s < 2^V) (hgapV : 2*(t-s) < 2^V) (hksum : k+band < 2^V)
    (hleft : 2*(t-s)*(k-band)+s < 2^V) (hright : 2*(t-s)*(k+band)+s < 2^V) :
    TblDo A V w haloMaskPhaseCode st (fun st' =>
      st'.val 11 = naturalPhase s t (k-band) ∧ st'.val 12 = naturalPhase s t (k+band) ∧
      st'.acc = st.acc ∧ ∀ r, r ∉ [(6 : Fin 16),7,8,9,10,11,12] → st'.val r = st.val r) 11 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,ht,hb,hk,hst,hband,
      ← two_mul,← Nat.mul_assoc]
    omega
  · simp only [List.cons_append,List.nil_append,tblExactList,TblIns.exact]
    simp [hs,ht,hb,hk,naturalPhase,← two_mul,← Nat.mul_assoc]
    intro r hr6 hr7 hr8 hr9 hr10 hr11 hr12
    simp [hr6,hr7,hr8,hr9,hr10,hr11,hr12]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
