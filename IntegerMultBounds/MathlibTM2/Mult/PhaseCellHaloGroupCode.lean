module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupCode
public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! Emit exactly the clipped origins of one positive halo length class in
original ambient phase order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloGroupRowCode : TblCode 16 := haloIntervalCode ;; naturalOriginEmit

theorem haloGroupRowCode_do {A W w s t band a b L phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hphase : st.val 4 = phase) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloGroupRowCode st (fun st' =>
      st'.acc = (if haloLength s t band a b phase = L then tblPairs A w (haloStart s t band a phase) 0
        else []).reverse ++ st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16), 9, 10, 11] → st'.val k = st.val k) 33 := by
  have hi := haloIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone ha hb has hbs hs hst hphaseMax hwide
  exact hi.seq (fun st' ⟨ha, hb, hl, hacc, hf⟩ =>
    (naturalOriginEmit_do (A := A) (W := W) (w := w) st'
      ((hf 3 (by simp)).trans hL') hl ha ((hf 12 (by simp)).trans hz)).mono
      (fun st'' ⟨hv, hout⟩ => ⟨by rw [hout, hacc], fun k hk => by rw [hv]; exact hf k hk⟩) le_rfl)

/-- Selection and emission commute for any phase list; no scan bound is built in. -/
theorem haloGroupRows_filter (A w s t band a b L : ℕ) (hL : 0 < L) (xs : List ℕ) :
    xs.flatMap (fun phase => if haloLength s t band a b phase = L then
      tblPairs A w (haloStart s t band a phase) 0 else []) =
      (xs.filter (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L))).flatMap
        (fun phase => tblPairs A w (haloStart s t band a phase) 0) := by
  induction xs with
  | nil => rfl
  | cons phase xs ih =>
    by_cases hh : haloLength s t band a b phase = L <;> simp [hh,hL,ih]

def haloGroupCode : TblCode 16 := tblFor 4 15 haloGroupRowCode

theorem haloGroupCode_do {A W w s t band a b L : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloGroupCode st (fun st' =>
      st'.acc = ((haloLengthGroup s t band a b L).flatMap
        (fun phase => tblPairs A w (haloStart s t band a phase) 0)).reverse ++ st.acc)
      (36*(t-s+1)+3) := by
  let F := fun phase => if haloLength s t band a b phase = L then tblPairs A w (haloStart s t band a phase) 0 else []
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ k, k ∉ [(4 : Fin 16), 8, 9, 10, 11] → st'.val k = st.val k) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hN : t-s+1 < 2^W := by
    have hd : t-s ≤ t := Nat.sub_le _ _
    nlinarith only [hwide, hd]
  have hc : TblDo A W w haloGroupCode st (fun st' =>
      st'.acc = ((List.range (t-s+1)).flatMap F).reverse ++ st.acc)
      (1+((t-s+1)*(33+1+2)+2)) := by
    apply TblDo.for (t-s+1) 33 hcount hN (by decide) Inv
    · constructor
      · intro k hk
        have hn : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
        simp [hn]
      · simp
    · intro j hj st₁ ⟨hf, hacc⟩ hindex hn
      have hr := haloGroupRowCode_do (A := A) (W := W) (w := w) st₁
        ((hf 0 (by simp)).trans hs') ((hf 2 (by simp)).trans hband) ((hf 3 (by simp)).trans hL') hindex
        ((hf 6 (by simp)).trans hden) ((hf 7 (by simp)).trans hone) ((hf 12 (by simp)).trans hz)
        ((hf 13 (by simp)).trans ha) ((hf 14 (by simp)).trans hb) has hbs hs hst (by omega) hwide
      exact hr.mono (fun st₂ ⟨hout, hframe⟩ => ⟨(hframe 4 (by simp)).trans hindex,
        (hframe 15 (by simp)).trans hn, (by
          constructor
          · intro k hk
            have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
            have hrest : k ∉ [(8 : Fin 16), 9, 10, 11] := fun hm => hk (List.mem_cons_of_mem _ hm)
            simpa [h4] using (hframe k hrest).trans (hf k hk)
          · change st₂.acc = _
            rw [hout, hacc, List.range_succ]
            simp [F, List.reverse_append, List.append_assoc])⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  have hfilter (xs : List ℕ) : xs.flatMap F =
      (xs.filter (fun phase => decide (0 < L ∧ haloLength s t band a b phase = L))).flatMap
        (fun phase => tblPairs A w (haloStart s t band a phase) 0) := by
    simpa only [F] using haloGroupRows_filter A w s t band a b L hL xs
  exact hc.mono (fun st' hh => by simpa [hfilter, haloLengthGroup] using hh) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
