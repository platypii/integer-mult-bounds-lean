module

public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorEnumeration

/-! Fixed table code generates local nearest-row offsets from s,t,a,origin,n.
The shared descriptor loop proves order once; no origin list is an input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def localRowCode : TblCode 16 :=
  tblBlock 16 [.add 2 4 8,.mul 1 8 8,.add 8 8 8,.add 8 0 8,
    .add 0 0 9,.div 8 9 9,.sub 9 3 9] (.emit 9 12)

theorem localRowCode_do {A W w s t a origin j : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (ha : st.val 2 = a)
    (ho : st.val 3 = origin) (hj : st.val 4 = j) (hz : st.val 12 = 0)
    (hspos : 0 < s) (hleft : origin ≤ nearestNatural s t (a+j))
    (hwide : a+j+2*t*(a+j)+3*s < 2^W) :
    TblDo A W w localRowCode st (fun F =>
      F.acc = (tblPairs A w (nearestNatural s t (a+j)-origin) 0).reverse++st.acc ∧
      ∀ i, i ∉ [(8 : Fin 16),9,10,11] → F.val i = st.val i) 8 := by
  have hnum : 2*t*(a+j)+s < 2^W := by omega
  have hden : 2*s < 2^W := by omega
  have hmul : t*(a+j) < 2^W := by nlinarith
  have hdouble : t*(a+j)+t*(a+j) < 2^W := by nlinarith
  have hnear : nearestNatural s t (a+j) < 2^W :=
    (Nat.div_le_self _ _).trans_lt hnum
  unfold localRowCode
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits,TblIns.exact,hs,ht,ha,ho,hj,←two_mul,←Nat.mul_assoc]
    dsimp only [nearestNatural] at hleft hnear
    omega
  · constructor
    · simp [tblExactList,TblIns.exact,hs,ht,ha,ho,hj,hz,nearestNatural,←two_mul,←Nat.mul_assoc]
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
      simp [tblExactList,TblIns.exact,Function.update_of_ne hi.1,Function.update_of_ne hi.2.1]

def localRowOriginsCode : TblCode 16 := tblFor 4 15 localRowCode

theorem localRowOriginsCode_do {A W w s t a origin n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (ha : st.val 2 = a)
    (ho : st.val 3 = origin) (hz : st.val 12 = 0) (hn : st.val 15 = n)
    (hspos : 0 < s) (hcount : n < 2^W)
    (hleft : ∀ j < n, origin ≤ nearestNatural s t (a+j))
    (hwide : a+n+2*t*(a+n)+3*s < 2^W) :
    TblDo A W w localRowOriginsCode st (fun F =>
      F.acc = ((List.range n).flatMap (fun j =>
        tblPairs A w (nearestNatural s t (a+j)-origin) 0)).reverse++st.acc) (11*n+3) := by
  have hh := descriptorEnumeration_do localRowCode
    (fun j => tblPairs A w (nearestNatural s t (a+j)-origin) 0) st hn hcount (K := 8)
    (by
      intro j hj st₁ hf hindex
      have hmul := Nat.mul_le_mul_left (2*t) (show a+j ≤ a+n by omega)
      exact localRowCode_do st₁ ((hf 0 (by simp)).trans hs) ((hf 1 (by simp)).trans ht)
        ((hf 2 (by simp)).trans ha) ((hf 3 (by simp)).trans ho) hindex
        ((hf 12 (by simp)).trans hz) hspos (hleft j hj) (by omega))
  simpa only [localRowOriginsCode,Nat.mul_comm] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
