module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderData

/-! Count the actual halo boundary directly from scalar geometry, before arithmetic precision is selected. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryCountMaskMap (i : Fin 16) : Fin 17 := ⟨i.val,by omega⟩

theorem boundaryCountMaskMap_injective : Function.Injective boundaryCountMaskMap := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 17 => k.val) h)

def boundaryCountRow : TblCode 17 :=
  .seq ((haloMembershipMaskCode true).rename boundaryCountMaskMap)
    (.seq (.ins (.zero 6)) (.ite 6 15 (.ins (.inc 16)) (.ins (.zero 6))))

theorem boundaryCountRow_do {A V w s t band a b k m : ℕ} (st : TblSt 17 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band) (hk : st.val 3 = k)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hm : st.val 16 = m)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hmV : m+1 < 2^V) :
    TblDo A V w boundaryCountRow st (fun z =>
      z.val 16 = m+(if haloMaskAt true s t band a b k then 1 else 0) ∧
      z.acc = st.acc ∧ ∀ r : Fin 17, r.val < 6 → z.val r = st.val r) 28 := by
  have hmask := (haloMembershipMaskCode_do (A := A) (V := V) (w := w) true
    (st.restrict boundaryCountMaskMap) hs ht hband hk ha hb hs0 hst haS hbS hwide).rename boundaryCountMaskMap_injective
  unfold boundaryCountRow
  apply hmask.seq (K₂ := 3)
  intro z ⟨⟨hflag,hacc,hframe⟩,hoff⟩
  have hflag' : z.val 15 = (if haloMaskAt true s t band a b k then 1 else 0) := hflag
  have hm' : z.val 16 = m := (hoff 16 (by intro i; simp [boundaryCountMaskMap,Fin.ext_iff]; omega)).trans hm
  have hlow (r : Fin 17) (hr : r.val < 6) : z.val r = st.val r := by
    exact hframe ⟨r.val,by omega⟩ hr
  have hzero : TblDo A V w (.ins (.zero 6)) z (fun z' => z'.val 6 = 0 ∧
      z'.val 15 = z.val 15 ∧ z'.val 16 = m ∧ z'.acc = st.acc ∧
      ∀ r : Fin 17, r.val < 6 → z'.val r = st.val r) 1 := by
    apply TblDo.ins
    refine ⟨by simp [TblIns.run],by simp [TblIns.run],by simpa [TblIns.run] using hm',hacc,?_⟩
    intro r hr
    have h6 : r ≠ 6 := by intro he; subst r; norm_num at hr
    simpa [TblIns.run,h6] using hlow r hr
  apply hzero.seq (K₂ := 2)
  intro z' ⟨hz,h15,h16,ha',hf⟩
  by_cases hB : haloMaskAt true s t band a b k = true
  · apply TblDo.iteT (by simpa [hz,h15,hflag',hB])
    apply TblDo.insX (.inc 16) (by simpa [TblIns.fits,h16] using hmV)
    refine ⟨by simp [TblIns.exact,h16,hB],ha',?_⟩
    intro r hr
    have hne : r ≠ 16 := by intro he; subst r; norm_num at hr
    simpa [TblIns.exact,hne] using hf r hr
  · apply TblDo.iteF (by simpa [hz,h15,hflag',hB])
    apply TblDo.ins
    refine ⟨by simp [TblIns.run,h16,hB],ha',?_⟩
    intro r hr
    have hne : r ≠ 6 := by intro he; subst r; norm_num at hr
    simpa [TblIns.run,hne] using hf r hr

def boundaryCountCode : TblCode 17 := .seq (.ins (.zero 16)) (tblFor 3 0 boundaryCountRow)

theorem boundaryCountCode_do {A V w s t band a b : ℕ} [NeZero s] (st : TblSt 17 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hfit : ∀ i, st.val i < 2^V) :
    TblDo A V w boundaryCountCode st (fun z =>
      z.val 16 = (haloBoundary s t band a b).card ∧ z.acc = st.acc ∧
      (∀ r : Fin 17, r.val < 6 → r ≠ 3 → z.val r = st.val r) ∧
      ∀ i, z.val i < 2^V) (31*s+4) := by
  let st₁ : TblSt 17 A := ⟨Function.update st.val 16 0,st.acc⟩
  have hzero : TblDo A V w (.ins (.zero 16)) st (fun z => z = st₁) 1 := by
    apply TblDo.ins
    rfl
  let count := fun j => ((List.range j).filter (haloMaskAt true s t band a b)).length
  let Inv := fun j (z : TblSt 17 A) =>
    (∀ r : Fin 17, r.val < 6 → r ≠ 3 → z.val r = st₁.val r) ∧ z.val 16 = count j ∧ z.acc = st.acc
  have hsV : s < 2^V := by nlinarith [Nat.zero_le (t*t)]
  have hfor : TblDo A V w (tblFor 3 0 boundaryCountRow) st₁ (fun z =>
      z.val 16 = count s ∧ z.acc = st.acc ∧
      ∀ r : Fin 17, r.val < 6 → r ≠ 3 → z.val r = st.val r) (1+(s*(28+1+2)+2)) := by
    apply TblDo.for s 28 (by simpa [st₁] using hs) hsV (by decide) Inv
    · refine ⟨?_,?_,rfl⟩
      · intro r hr h3; simp [h3]
      · simp [st₁,count]
    · intro k hk z ⟨hf,hcount,hacc⟩ hindex htotal
      have hlow (r : Fin 17) (hr : r.val < 6) (h3 : r ≠ 3) : z.val r = st.val r := by
        have h16 : r ≠ 16 := by intro he; subst r; norm_num at hr
        simpa [st₁,h16] using hf r hr h3
      have hcountLe : count k ≤ k := by
        exact (List.length_filter_le _ _).trans (by simp)
      have hrow := boundaryCountRow_do (A := A) (V := V) (w := w) z
        ((hlow 0 (by decide) (by decide)).trans hs) ((hlow 1 (by decide) (by decide)).trans ht)
        ((hlow 2 (by decide) (by decide)).trans hband) hindex
        ((hlow 4 (by decide) (by decide)).trans ha) ((hlow 5 (by decide) (by decide)).trans hb) hcount
        (NeZero.pos s) hst haS hbS hbandS hwide (by omega)
      exact hrow.mono (fun z' ⟨hc,ha',hfr⟩ =>
        ⟨(hfr 3 (by decide)).trans hindex,(hfr 0 (by decide)).trans htotal,by
          refine ⟨?_,?_,ha'.trans hacc⟩
          · intro r hr h3
            have hne : r ≠ 3 := h3
            simpa [hne] using (hfr r hr).trans (hf r hr h3)
          · change z'.val 16 = count (k+1)
            rw [hc]
            simp [count,List.range_succ,List.filter_append,List.length_append]
            split <;> simp_all⟩) (le_refl _)
    · intro z ⟨hf,hc,ha'⟩ _ _
      refine ⟨hc,ha',?_⟩
      intro r hr h3
      have h16 : r ≠ 16 := by intro he; subst r; norm_num at hr
      simpa [st₁,h16] using hf r hr h3
  have hr := hzero.seq (fun z hz => by cases hz; exact hfor)
  obtain ⟨z,k,hbig,⟨hc,ha',hf⟩,hcost⟩ := hr
  refine ⟨z,k,hbig,⟨?_,ha',hf,hbig.lt hfit⟩,?_⟩
  · exact hc.trans (boundaryIndices_length hst band a b hbS)
  · omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
