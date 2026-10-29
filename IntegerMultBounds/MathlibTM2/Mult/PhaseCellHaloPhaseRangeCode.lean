module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalHaloGroupCode

/-! Compute the local loop bounds in binary from retained halo endpoints. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloPhaseRangeCode : TblCode 16 := tblBlock 16 [
  .mul 6 13 4,.add 4 0 4,.add 0 0 8,.div 4 8 4,
  .mul 6 14 15,.add 15 0 15,.div 15 8 15] (.inc 15)

theorem haloPhaseRangeCode_do {A V w s t a b band : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hden : st.val 6 = 2*(t-s)) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w haloPhaseRangeCode st (fun st' =>
      st'.val 4 = haloPhaseStart s t a ∧ st'.val 15 = naturalPhase s t b+1 ∧ st'.acc = st.acc ∧
      ∀ k : Fin 16, k ≠ 4 → k ≠ 8 → k ≠ 15 → st'.val k = st.val k) 8 := by
  have hpa : (t-s)*a ≤ t*t := Nat.mul_le_mul (Nat.sub_le _ _) (haS.trans hst.le)
  have hpb : (t-s)*b ≤ t*t := Nat.mul_le_mul (Nat.sub_le _ _) (hbS.trans hst.le)
  have hna : 2*(t-s)*a+s < 2^V := by nlinarith only [hwide,hpa,haS,hst]
  have hnb : 2*(t-s)*b+s < 2^V := by nlinarith only [hwide,hpb,hbS,hst]
  have hss : s+s < 2^V := by nlinarith only [hwide,hst]
  have hn : naturalPhase s t b+1 < 2^V := by
    have hh := naturalPhase_le_gap (t := t) hs0 hbS
    have hg := Nat.sub_le t s
    nlinarith only [hwide,hh,hg]
  have hsum : s+s = 2*s := by omega
  apply TblDo.block
  · simp [haloPhaseRangeCode,tblFitsList,TblIns.fits,TblIns.exact,hs,hden,ha,hb,hsum,
      hna,hnb,hss,show (2*(t-s)*b+s)/(2*s)+1 < 2^V from hn]
    all_goals omega
  · refine ⟨?_,?_,rfl,?_⟩
    · simp [haloPhaseRangeCode,tblExactList,TblIns.exact,hs,hden,ha,hb,haloPhaseStart,naturalPhase,hsum]
    · simp [haloPhaseRangeCode,tblExactList,TblIns.exact,hs,hden,ha,hb,naturalPhase,hsum]
    · intro k hk4 hk8 hk15
      simp [haloPhaseRangeCode,tblExactList,TblIns.exact,hk4,hk8,hk15]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
