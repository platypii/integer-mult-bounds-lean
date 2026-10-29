module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalIntervalCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloMembershipMask
public import IntegerMultBounds.NLogN.PhaseCellHaloMask

/-! Translate the query coordinate after the ambient membership test. The
checked saturating subtraction handles unselected coordinates below the halo.
All geometry and the membership flag (register 15) are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloMaskAt_packed_bounds {s t : ℕ} [NeZero s] (boundary : Bool)
    (hst : s < t) (band a b k : ℕ) (hb : b ≤ s) (hk : k < s)
    (hmask : haloMaskAt boundary s t band a b k = true) : a ≤ k ∧ k < b := by
  have hm := (haloMaskAt_spec boundary hst band a b k hb hk).mp hmask
  have hhalo : (k : ZMod s) ∈ haloVertices s a b := by
    cases boundary
    · exact haloInterior_subset s t band a b hm
    · exact (Finset.mem_sdiff.mp hm).1
  simpa only [ZMod.val_cast_of_lt hk] using (mem_haloVertices a b (k : ZMod s)).mp hhalo

def packedLookupOffsetCode : TblCode 16 := tblNatSub 3 4 3

theorem packedLookupOffsetCode_do {A V w k a : ℕ} (st : TblSt 16 A)
    (hk : st.val 3 = k) (ha : st.val 4 = a) (hwide : k < 2^V) :
    TblDo A V w packedLookupOffsetCode st
      (fun st' => st' = ⟨Function.update st.val 3 (k-a),st.acc⟩) 2 := by
  simpa only [packedLookupOffsetCode,hk,ha] using
    tblNatSub_do (A := A) (W := V) (w := w) 3 4 3 st (by simpa only [hk] using hwide)

def packedLookupCode (boundary : Bool) : TblCode 16 :=
  haloMembershipMaskCode boundary ;; packedLookupOffsetCode

/-- Unselected queries must not emit a large unary ambient offset. -/
def guardedPackedLookupOffsetCode : TblCode 16 :=
  .ins (.zero 6) ;; .ite 6 15 packedLookupOffsetCode (.ins (.zero 3))

theorem guardedPackedLookupOffsetCode_do {A V w k a : ℕ} (st : TblSt 16 A)
    (hk : st.val 3 = k) (ha : st.val 4 = a) (hwide : k < 2^V) :
    TblDo A V w guardedPackedLookupOffsetCode st (fun st' =>
      st'.val 3 = (if 0 < st.val 15 then k-a else 0) ∧
      st'.val 15 = st.val 15 ∧ st'.acc = st.acc) 4 := by
  have hz : TblDo A V w (.ins (.zero 6)) st
      (fun st' => st' = ⟨Function.update st.val 6 0,st.acc⟩) 1 :=
    TblDo.insX (.zero 6) (by trivial) (by simp [TblIns.exact])
  apply hz.seq (K₂ := 3)
  intro st₁ he
  subst st₁
  by_cases hf : 0 < st.val 15
  · apply TblDo.iteT (by simpa using hf)
    exact (packedLookupOffsetCode_do (A := A) (V := V) (w := w) _
      (by simpa using hk) (by simpa using ha) hwide).mono
      (fun st' he => by subst st'; simp [hf]) le_rfl
  · apply TblDo.iteF (by simpa using hf)
    have hz3 : TblDo A V w (.ins (.zero 3)) ⟨Function.update st.val 6 0,st.acc⟩
        (fun st' => st' = ⟨Function.update (Function.update st.val 6 0) 3 0,st.acc⟩) 1 :=
      TblDo.insX (.zero 3) (by trivial) (by simp [TblIns.exact])
    exact hz3.mono (fun st' he => by subst st'; simp [hf]) (by decide)

theorem packedLookupCode_do {A V w s t band a b k : ℕ} (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V) :
    TblDo A V w (packedLookupCode boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b k then 1 else 0) ∧
      st'.val 3 = k-a ∧ st'.acc = st.acc) 27 := by
  have hm := haloMembershipMaskCode_do (A := A) (V := V) (w := w) boundary st
    hs ht hband hk ha hb hs0 hst haS hbS hwide
  apply hm.seq (K₂ := 2)
  intro st₁ ⟨hflag,hacc,hframe⟩
  have hc := packedLookupOffsetCode_do (A := A) (V := V) (w := w) st₁
    ((hframe 3 (by decide)).trans hk) ((hframe 4 (by decide)).trans ha) hkW
  apply hc.mono _ le_rfl
  intro st₂ he
  subst st₂
  simp [hflag,hacc]

def guardedPackedLookupCode (boundary : Bool) : TblCode 16 :=
  haloMembershipMaskCode boundary ;; guardedPackedLookupOffsetCode

theorem guardedPackedLookupCode_do {A V w s t band a b k : ℕ}
    (boundary : Bool) (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hkW : k < 2^V) :
    TblDo A V w (guardedPackedLookupCode boundary) st (fun st' =>
      st'.val 15 = (if haloMaskAt boundary s t band a b k then 1 else 0) ∧
      st'.val 3 = (if haloMaskAt boundary s t band a b k then k-a else 0) ∧
      st'.acc = st.acc) 29 := by
  have hm := haloMembershipMaskCode_do (A := A) (V := V) (w := w) boundary st
    hs ht hband hk ha hb hs0 hst haS hbS hwide
  apply hm.seq (K₂ := 4)
  intro st₁ ⟨hflag,hacc,hframe⟩
  have hc := guardedPackedLookupOffsetCode_do (A := A) (V := V) (w := w) st₁
    ((hframe 3 (by decide)).trans hk) ((hframe 4 (by decide)).trans ha) hkW
  apply hc.mono _ le_rfl
  intro st₂ ⟨hindex,hflag₂,hacc₂⟩
  refine ⟨hflag₂.trans hflag,?_,hacc₂.trans hacc⟩
  rw [hindex,hflag]
  split <;> simp_all

theorem guardedPackedLookupIndex_le {s t : ℕ} [NeZero s] (boundary : Bool)
    (hst : s < t) (band a b k : ℕ) (hb : b ≤ s) (hk : k < s) :
    (if haloMaskAt boundary s t band a b k then k-a else 0) ≤ b-a := by
  split_ifs with hm
  · have hh := haloMaskAt_packed_bounds boundary hst band a b k hb hk hm
    omega
  · omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
