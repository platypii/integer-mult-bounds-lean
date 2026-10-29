module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingIndexCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupCode

/-! A coupling offset is wrapped, tested in ambient geometry, then translated
to a packed address without serializing or reloading the intermediate query. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def packedCouplingLookupCode (negative boundary : Bool) : TblCode 16 :=
  packedCouplingIndexCode negative ;; packedLookupCode boundary

theorem packedCouplingLookupCode_do {A V s t band a b i d : ℕ}
    (negative boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hd : d ≤ band)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hsV : s < 2^V)
    (hfit : i+band*s+d < 2^V) :
    TblDo A V V (packedCouplingLookupCode negative boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b (couplingIndex negative s band i d) then 1 else 0) ∧
      st'.val 3 = couplingIndex negative s band i d-a ∧ st'.acc = st.acc) 31 := by
  have hc := packedCouplingIndexCode_do (A := A) (V := V) negative st hs hband hi hd' hs0 hd hfit
  apply hc.seq (K₂ := 27)
  intro st₁ ⟨hk,hacc,hframe⟩
  have hf (r : Fin 16) (h3 : r ≠ 3) (h10 : r ≠ 10) := hframe r h3 h10
  have hm := packedLookupCode_do (A := A) (V := V) (w := V) boundary st₁
    ((hf 0 (by decide) (by decide)).trans hs) ((hf 1 (by decide) (by decide)).trans ht)
    ((hf 2 (by decide) (by decide)).trans hband) hk
    ((hf 4 (by decide) (by decide)).trans ha) ((hf 5 (by decide) (by decide)).trans hb)
    hs0 hst haS hbS hwide ((couplingIndex_lt negative hs0).trans hsV)
  exact hm.mono (fun _ h => ⟨h.1,h.2.1,h.2.2.trans hacc⟩) le_rfl

def guardedPackedCouplingLookupCode (negative boundary : Bool) : TblCode 16 :=
  packedCouplingIndexCode negative ;; guardedPackedLookupCode boundary

theorem guardedPackedCouplingLookupCode_do {A V s t band a b i d : ℕ}
    (negative boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hd : d ≤ band)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hsV : s < 2^V)
    (hfit : i+band*s+d < 2^V) :
    TblDo A V V (guardedPackedCouplingLookupCode negative boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b (couplingIndex negative s band i d) then 1 else 0) ∧
      st'.val 3 = (if haloMaskAt boundary s t band a b (couplingIndex negative s band i d) then couplingIndex negative s band i d-a else 0) ∧ st'.acc = st.acc) 33 := by
  have hc := packedCouplingIndexCode_do (A := A) (V := V) negative st hs hband hi hd' hs0 hd hfit
  apply hc.seq (K₂ := 29)
  intro st₁ ⟨hk,hacc,hframe⟩
  have hf (r : Fin 16) (h3 : r ≠ 3) (h10 : r ≠ 10) := hframe r h3 h10
  have hm := guardedPackedLookupCode_do (A := A) (V := V) (w := V) boundary st₁
    ((hf 0 (by decide) (by decide)).trans hs) ((hf 1 (by decide) (by decide)).trans ht)
    ((hf 2 (by decide) (by decide)).trans hband) hk
    ((hf 4 (by decide) (by decide)).trans ha) ((hf 5 (by decide) (by decide)).trans hb)
    hs0 hst haS hbS hwide ((couplingIndex_lt negative hs0).trans hsV)
  exact hm.mono (fun _ h => ⟨h.1,h.2.1,h.2.2.trans hacc⟩) le_rfl

/-- Advance a binary offset before selecting the next masked operand. -/
def nextPackedCouplingLookupCode (negative boundary : Bool) : TblCode 16 :=
  .ins (.inc 8) ;; guardedPackedCouplingLookupCode negative boundary

theorem nextPackedCouplingLookupCode_do {A V s t band a b i d : ℕ}
    (negative boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hd : d+1 ≤ band)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hsV : s < 2^V)
    (hfit : i+band*s+(d+1) < 2^V) :
    TblDo A V V (nextPackedCouplingLookupCode negative boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b (couplingIndex negative s band i (d+1)) then 1 else 0) ∧
      st'.val 3 = (if haloMaskAt boundary s t band a b (couplingIndex negative s band i (d+1)) then couplingIndex negative s band i (d+1)-a else 0) ∧ st'.acc = st.acc) 34 := by
  have hnext : d+1 < 2^V := by omega
  have hc : TblDo A V V (.ins (.inc 8)) st
      (fun st' => st' = ⟨Function.update st.val 8 (d+1),st.acc⟩) 1 :=
    TblDo.ins (.inc 8) (by simp [TblIns.run,hd',Nat.mod_eq_of_lt hnext])
  apply hc.seq (K₂ := 33)
  intro st' he
  subst st'
  exact guardedPackedCouplingLookupCode_do negative boundary _
    (by simpa using hs) (by simpa using ht) (by simpa using hband)
    (by simpa using ha) (by simpa using hb) (by simpa using hi) (by simp)
    hs0 hst haS hbS hd hwide hsV hfit

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
