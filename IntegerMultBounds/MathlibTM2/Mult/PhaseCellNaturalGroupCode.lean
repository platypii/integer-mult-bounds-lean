module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalIntervalCode
public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups

/-! Scan each possible natural phase once and emit exactly the origins of the
requested nonempty length group. All comparisons use original ambient cells. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalOriginEmit : TblCode 16 :=
  .ite 11 3 (.ins (.copy 12 12)) (.ite 3 11 (.ins (.copy 12 12)) (.ins (.emit 9 12)))

theorem naturalOriginEmit_do {A W w L len origin : ℕ} (st : TblSt 16 A)
    (hL : st.val 3 = L) (hlen : st.val 11 = len) (ho : st.val 9 = origin) (hz : st.val 12 = 0) :
    TblDo A W w naturalOriginEmit st (fun st' => st'.val = st.val ∧
      st'.acc = (if len = L then tblPairs A w origin 0 else []).reverse ++ st.acc) 3 := by
  by_cases hlt : len < L
  · have hh : st.val 11 < st.val 3 := by omega
    apply (TblDo.iteT hh (TblDo.ins (.copy 12 12) (P := fun st' => st' = st) (by simp [TblIns.run]))).mono
    · intro st' he; subst he
      simp [show len ≠ L by omega]
    · omega
  · apply TblDo.iteF (by omega : ¬ st.val 11 < st.val 3)
    by_cases hgt : L < len
    · apply TblDo.iteT (by omega : st.val 3 < st.val 11)
      exact TblDo.ins (.copy 12 12) (by simp [TblIns.run, show len ≠ L by omega])
    · apply TblDo.iteF (by omega : ¬ st.val 3 < st.val 11)
      exact TblDo.ins (.emit 9 12) (by simp [TblIns.run, ho, hz, show len = L by omega])

def naturalGroupRowCode : TblCode 16 := naturalIntervalCode ;; naturalOriginEmit

theorem naturalGroupRowCode_do {A W w s t band L phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hphase : st.val 4 = phase) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w naturalGroupRowCode st (fun st' =>
      st'.acc = (if naturalLength s t band phase = L then tblPairs A w (naturalStart s t band phase) 0
        else []).reverse ++ st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16), 9, 10, 11] → st'.val k = st.val k) 24 := by
  have hi := naturalIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone hs hst hphaseMax hwide
  exact hi.seq (fun st' ⟨ha, hb, hl, hacc, hf⟩ =>
    (naturalOriginEmit_do (A := A) (W := W) (w := w) st'
      ((hf 3 (by simp)).trans hL') hl ha ((hf 12 (by simp)).trans hz)).mono
      (fun st'' ⟨hv, hout⟩ => ⟨by rw [hout, hacc], fun k hk => by rw [hv]; exact hf k hk⟩) le_rfl)

def naturalGroupCode : TblCode 16 := tblFor 4 15 naturalGroupRowCode

theorem naturalGroupCode_do {A W w s t band L : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (hs : 0 < s) (hst : s < t) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w naturalGroupCode st (fun st' =>
      st'.acc = ((naturalLengthGroup s t band L).flatMap
        (fun phase => tblPairs A w (naturalStart s t band phase) 0)).reverse ++ st.acc)
      (27*(t-s+1)+3) := by
  let F := fun phase => if naturalLength s t band phase = L then tblPairs A w (naturalStart s t band phase) 0 else []
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ k, k ∉ [(4 : Fin 16), 8, 9, 10, 11] → st'.val k = st.val k) ∧
    st'.acc = ((List.range j).flatMap F).reverse ++ st.acc
  have hN : t-s+1 < 2^W := by
    have hd : t-s ≤ t := Nat.sub_le _ _
    nlinarith only [hwide, hd]
  have hc : TblDo A W w naturalGroupCode st (fun st' =>
      st'.acc = ((List.range (t-s+1)).flatMap F).reverse ++ st.acc)
      (1+((t-s+1)*(24+1+2)+2)) := by
    apply TblDo.for (t-s+1) 24 hcount hN (by decide) Inv
    · constructor
      · intro k hk
        have hn : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
        simp [hn]
      · simp
    · intro j hj st₁ ⟨hf, ha⟩ hindex hn
      have hr := naturalGroupRowCode_do (A := A) (W := W) (w := w) st₁
        ((hf 0 (by simp)).trans hs') ((hf 2 (by simp)).trans hband) ((hf 3 (by simp)).trans hL') hindex
        ((hf 6 (by simp)).trans hden) ((hf 7 (by simp)).trans hone) ((hf 12 (by simp)).trans hz)
        hs hst (by omega) hwide
      exact hr.mono (fun st₂ ⟨hout, hframe⟩ => ⟨(hframe 4 (by simp)).trans hindex,
        (hframe 15 (by simp)).trans hn, (by
          constructor
          · intro k hk
            have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
            have hrest : k ∉ [(8 : Fin 16), 9, 10, 11] := fun hm => hk (List.mem_cons_of_mem _ hm)
            simpa [h4] using (hframe k hrest).trans (hf k hk)
          · change st₂.acc = _
            rw [hout, ha, List.range_succ]
            simp [F, List.reverse_append, List.append_assoc])⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  have hfilter (xs : List ℕ) : xs.flatMap F =
      (xs.filter (fun phase => decide (0 < L ∧ naturalLength s t band phase = L))).flatMap
        (fun phase => tblPairs A w (naturalStart s t band phase) 0) := by
    induction xs with
    | nil => rfl
    | cons phase xs ih =>
      by_cases hh : naturalLength s t band phase = L <;> simp [F, hh, hL, ih]
  exact hc.mono (fun st' hh => by simpa [hfilter, naturalLengthGroup] using hh) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
