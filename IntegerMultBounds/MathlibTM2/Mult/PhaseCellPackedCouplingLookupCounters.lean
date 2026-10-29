module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCouplingLookupCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLookupCounters

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedCouplingLookupCounters_exec {P U : Type} {Q A V s t band a b i d : ℕ}
    {body : P → Pr P 117 Q A U} (negative boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hsV : s < 2^V) (hd : d ≤ band) (hfit : i+band*s+d < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 31*tblC V V+6*(couplingIndex negative s band i d-a+1)+84*V+76 ∧
      Exec body (packedLookupCountersFor (packedCouplingLookupCode negative boundary)) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      S'.R 108 = List.replicate (couplingIndex negative s band i d-a) tick++S.R 108 ∧
      S'.R 109 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b (couplingIndex negative s band i d)
        then [tick] else [])++S.R 109 ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → S'.R r = S.R r := by
  let k := couplingIndex negative s band i d
  have hc := packedCouplingLookupCode_do (A := A) (V := V) negative boundary st
    hs ht hband ha hb hi hd' hs0 hst haS hbS hd hwide hsV hfit
  have hc' : TblDo A V V (packedCouplingLookupCode negative boundary) st
      (fun st' => st'.acc = [] ∧ st'.val 3 = k-a ∧ st'.val 15 =
        (if haloMaskAt boundary s t band a b k then 1 else 0)) 31 :=
    hc.mono (fun st' h => ⟨h.2.2.trans hacc,h.2.1,h.1⟩) le_rfl
  obtain ⟨v',S',n,hu,hn,he,hio,hout,hl,hzero,hindex,hmask,hframe⟩ :=
    packedLookupCounters_of_code (body := body) (packedCouplingLookupCode negative boundary) st (k-a) _
      (by split <;> omega) hbound hc' v S hS
  refine ⟨v',S',n,hu,hn,he,hio,hout,hl,hzero,hindex,?_,hframe⟩
  split <;> simp_all [k]

theorem guardedPackedCouplingLookupCounters_exec {P U : Type} {Q A V s t band a b i d : ℕ}
    {body : P → Pr P 117 Q A U} (negative boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hi : st.val 7 = i) (hd' : st.val 8 = d)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hsV : s < 2^V) (hd : d ≤ band) (hfit : i+band*s+d < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 117 Q A U) (S : Stacks 117 A)
    [NeZero s]
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ 33*tblC V V+6*(b-a+1)+84*V+76 ∧
      Exec body (packedLookupCountersFor (guardedPackedCouplingLookupCode negative boundary)) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ r : Fin 117, r.val < 31 → S'.R r = []) ∧
      S'.R 108 = List.replicate (if haloMaskAt boundary s t band a b (couplingIndex negative s band i d) then couplingIndex negative s band i d-a else 0) tick++S.R 108 ∧
      S'.R 109 = (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b (couplingIndex negative s band i d)
        then [tick] else [])++S.R 109 ∧
      ∀ r : Fin 117, 31 ≤ r.val → r ≠ 108 → r ≠ 109 → S'.R r = S.R r := by
  let k := couplingIndex negative s band i d
  have hc := guardedPackedCouplingLookupCode_do (A := A) (V := V) negative boundary st
    hs ht hband ha hb hi hd' hs0 hst haS hbS hd hwide hsV hfit
  have hc' : TblDo A V V (guardedPackedCouplingLookupCode negative boundary) st
      (fun st' => st'.acc = [] ∧ st'.val 3 = (if haloMaskAt boundary s t band a b k then k-a else 0) ∧ st'.val 15 =
        (if haloMaskAt boundary s t band a b k then 1 else 0)) 33 :=
    hc.mono (fun st' h => ⟨h.2.2.trans hacc,h.2.1,h.1⟩) le_rfl
  obtain ⟨v',S',n,hu,hn,he,hio,hout,hl,hzero,hindex,hmask,hframe⟩ :=
    packedLookupCounters_of_code (body := body) (guardedPackedCouplingLookupCode negative boundary) st (if haloMaskAt boundary s t band a b k then k-a else 0) _
      (by split <;> omega) hbound hc' v S hS
  have hindexBound := guardedPackedLookupIndex_le boundary hst band a b k hbS (couplingIndex_lt negative hs0)
  refine ⟨v',S',n,hu,by omega,he,hio,hout,hl,hzero,hindex,?_,hframe⟩
  split <;> simp_all [k]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
