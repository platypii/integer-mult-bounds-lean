module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode

/-! Scan the original bounded phase range and emit origin/length pairs only
for positive clipped cells. Empty halos produce an empty descriptor stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloDescriptorEmit : TblCode 16 :=
  .ite 12 11 (tblBlock 16 [.emit 9 12] (.emit 11 12)) (.ins (.copy 12 12))

theorem haloDescriptorEmit_do {A W w origin len : ℕ} (st : TblSt 16 A)
    (ho : st.val 9 = origin) (hl : st.val 11 = len) (hz : st.val 12 = 0) :
    TblDo A W w haloDescriptorEmit st (fun st' => st'.val = st.val ∧
      st'.acc = (if 0 < len then tblPairs A w origin 0++tblPairs A w len 0 else []).reverse++st.acc) 3 := by
  by_cases hpos : 0 < len
  · apply TblDo.iteT (by omega : st.val 12 < st.val 11)
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · simp [tblExactList,TblIns.exact,ho,hl,hz,hpos,List.reverse_append,List.append_assoc]
  · apply TblDo.iteF (by omega : ¬ st.val 12 < st.val 11)
    exact (TblDo.ins (.copy 12 12) (P := fun st' => st' = st) (by simp [TblIns.run])).mono
      (fun st' he => he ▸ by simp [hpos]) (by omega)

def haloDescriptorRowCode : TblCode 16 := haloIntervalCode ;; haloDescriptorEmit

theorem haloDescriptorRowCode_do {A W w s t band a b phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hphase : st.val 4 = phase)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloDescriptorRowCode st (fun st' =>
      st'.acc = (if 0 < haloLength s t band a b phase then
        tblPairs A w (haloStart s t band a phase) 0++tblPairs A w (haloLength s t band a b phase) 0
        else []).reverse++st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16),9,10,11] → st'.val k = st.val k) 33 := by
  have hi := haloIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone ha hb has hbs hs hst hphaseMax hwide
  exact hi.seq (K₂ := 3) (fun st₁ ⟨hstart,_,hlen,hacc,hframe⟩ =>
    (haloDescriptorEmit_do (A := A) (W := W) (w := w) st₁ hstart hlen ((hframe 12 (by simp)).trans hz)).mono
      (fun st₂ ⟨hv,ha₂⟩ => ⟨by rw [ha₂,hacc],fun k hk => by rw [hv]; exact hframe k hk⟩) le_rfl)

def haloDescriptorCode : TblCode 16 := tblFor 4 15 haloDescriptorRowCode

theorem haloDescriptorCode_do {A W w s t band a b : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hden : st.val 6 = 2*(t-s))
    (hone : st.val 7 = 1) (hz : st.val 12 = 0) (hcount : st.val 15 = t-s+1)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloDescriptorCode st (fun st' =>
      st'.acc = ((haloCellPhases s t band a b).flatMap (fun phase =>
        tblPairs A w (haloStart s t band a phase) 0++tblPairs A w (haloLength s t band a b phase) 0)).reverse++st.acc)
      (36*(t-s+1)+3) := by
  let F := fun phase => if 0 < haloLength s t band a b phase then
    tblPairs A w (haloStart s t band a phase) 0++tblPairs A w (haloLength s t band a b phase) 0 else []
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ k, k ∉ [(4 : Fin 16),8,9,10,11] → st'.val k = st.val k) ∧
    st'.acc = ((List.range j).flatMap F).reverse++st.acc
  have hN : t-s+1 < 2^W := by have hd := Nat.sub_le t s; nlinarith only [hwide,hd]
  have hc : TblDo A W w haloDescriptorCode st (fun st' =>
      st'.acc = ((List.range (t-s+1)).flatMap F).reverse++st.acc) (1+((t-s+1)*(33+1+2)+2)) := by
    apply TblDo.for (t-s+1) 33 hcount hN (by decide) Inv
    · constructor
      · intro k hk
        have hn : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
        simp [hn]
      · simp
    · intro j hj st₁ ⟨hf,hacc⟩ hindex hn
      have hr := haloDescriptorRowCode_do (A := A) (W := W) (w := w) st₁
        ((hf 0 (by simp)).trans hs') ((hf 2 (by simp)).trans hband) hindex
        ((hf 6 (by simp)).trans hden) ((hf 7 (by simp)).trans hone) ((hf 12 (by simp)).trans hz)
        ((hf 13 (by simp)).trans ha) ((hf 14 (by simp)).trans hb) has hbs hs hst (by omega) hwide
      exact hr.mono (fun st₂ ⟨hout,hframe⟩ => ⟨(hframe 4 (by simp)).trans hindex,
        (hframe 15 (by simp)).trans hn,(by
          constructor
          · intro k hk
            have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
            have hrest : k ∉ [(8 : Fin 16),9,10,11] := fun hm => hk (List.mem_cons_of_mem _ hm)
            simpa [h4] using (hframe k hrest).trans (hf k hk)
          · change st₂.acc = _
            rw [hout,hacc,List.range_succ]
            simp [F,List.reverse_append,List.append_assoc])⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  have hfilter (xs : List ℕ) : xs.flatMap F =
      (xs.filter (fun phase => decide (0 < haloLength s t band a b phase))).flatMap (fun phase =>
        tblPairs A w (haloStart s t band a phase) 0++tblPairs A w (haloLength s t band a b phase) 0) := by
    induction xs with
    | nil => rfl
    | cons phase xs ih =>
      by_cases hh : 0 < haloLength s t band a b phase <;> simp [F,hh,ih]
  exact hc.mono (fun st' hh => by simpa [hfilter,haloCellPhases] using hh) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
