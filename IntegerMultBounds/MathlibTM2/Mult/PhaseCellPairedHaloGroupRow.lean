module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClipCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupCode
public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! Emit ambient origins and local offsets together, using the two coordinates
of a table packet. No later coordinate translation is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def pairedOriginEmit : TblCode 16 :=
  .ite 11 3 (.ins (.copy 12 12)) (.ite 3 11 (.ins (.copy 12 12)) (.ins (.emit 9 10)))

theorem pairedOriginEmit_do {A W w L len origin offset : ℕ} (st : TblSt 16 A)
    (hL : st.val 3 = L) (hlen : st.val 11 = len) (ho : st.val 9 = origin) (hlocal : st.val 10 = offset) :
    TblDo A W w pairedOriginEmit st (fun st' => st'.val = st.val ∧
      st'.acc = (if len = L then tblPairs A w origin offset else []).reverse ++ st.acc) 3 := by
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
      exact TblDo.ins (.emit 9 10) (by simp [TblIns.run, ho, hlocal, show len = L by omega])

def pairedHaloGroupRowCode : TblCode 16 :=
  haloIntervalCode ;; .ins (.sub 9 13 10) ;; pairedOriginEmit

theorem pairedHaloGroupRowCode_do {A W w s t band a b L phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hphase : st.val 4 = phase) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w pairedHaloGroupRowCode st (fun st' =>
      st'.acc = (if haloLength s t band a b phase = L then tblPairs A w (haloStart s t band a phase) (haloStart s t band a phase-a)
        else []).reverse ++ st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16), 9, 10, 11] → st'.val k = st.val k) 34 := by
  have hi := haloIntervalCode_do (A := A) (W := W) (w := w) st hs' hband hphase hden hone ha hb has hbs hs hst hphaseMax hwide
  exact hi.seq (K₂ := 4) (fun st' ⟨ha', hb', hl, hacc, hf⟩ => by
    have hbase : st'.val 13 = a := (hf 13 (by simp)).trans ha
    have hsub : TblDo A W w (.ins (.sub 9 13 10)) st'
        (fun st'' => st'' = ⟨Function.update st'.val 10 (haloStart s t band a phase-a),st'.acc⟩) 1 := by
      apply TblDo.ins
      have hlower : phaseLower s (t-s) phase ≤ s := by
        apply (phaseLower_le (by omega : 0 < t-s)).mpr
        nlinarith
      have hstart : haloStart s t band a phase ≤ s+band := by
        dsimp [haloStart,naturalStart]
        omega
      have hbasele : a ≤ haloStart s t band a phase := by
        dsimp [haloStart]
        omega
      have hfit : haloStart s t band a phase-a < 2^W := by
        nlinarith only [hwide,hstart,has,hst,Nat.sub_le (haloStart s t band a phase) a]
      have hmod : (haloStart s t band a phase+2^W-a)%2^W = haloStart s t band a phase-a := by
        rw [show haloStart s t band a phase+2^W-a = (haloStart s t band a phase-a)+2^W by omega]
        simp [Nat.mod_eq_of_lt hfit]
      simp [TblIns.run,ha',hbase,hmod]
    exact hsub.seq (K₂ := 3) (fun st'' he => by
      subst st''
      apply (pairedOriginEmit_do (A := A) (W := W) (w := w) (offset := haloStart s t band a phase-a) _
        (by simpa using (hf 3 (by simp)).trans hL')
        (by simpa using hl) (by simpa using ha') (by simp)).mono
      · intro st''' ⟨hv,hout⟩
        refine ⟨?_,?_⟩
        · simpa only [hacc] using hout
        · intro k hk
          rw [hv]
          have hk10 : k ≠ (10 : Fin 16) := by
            intro he; subst k; simp at hk
          simpa [hk10] using hf k hk
      · omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
