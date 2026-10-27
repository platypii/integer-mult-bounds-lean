module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode


/-! Generate the interior selection mask in ambient coordinate order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def publicationMaskRow : TblCode 16 :=
  couplingSourceMaskRow false

theorem publicationMaskRow_do {A V w s t band a b k : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w publicationMaskRow st (fun st' =>
      st'.acc = (tblPairs A w (if haloInteriorAt s t band a b k then 1 else 0)
        (if haloInteriorAt s t band a b k then 1 else 0)).reverse ++ st.acc ∧
      ∀ r : Fin 16, r.val < 6 → st'.val r = st.val r) 26 := by
  simpa [publicationMaskRow,haloMaskAt] using
    couplingSourceMaskRow_do false st hs ht hband hk ha hb hs0 hst haS hbS hwide

def publicationMaskCode : TblCode 16 :=
  couplingSourceMaskCode false

theorem publicationMaskCode_do {A V w s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) :
    TblDo A V w publicationMaskCode st (fun st' =>
      st'.acc = ((List.range s).flatMap (fun k =>
        tblPairs A w (if haloInteriorAt s t band a b k then 1 else 0)
          (if haloInteriorAt s t band a b k then 1 else 0))).reverse ++ st.acc)
      (29*s+3) := by
  simpa [publicationMaskCode,haloMaskAt] using
    couplingSourceMaskCode_do false st hs ht hband ha hb hs0 hst haS hbS hwide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
