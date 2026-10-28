module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunRowCode
public import IntegerMultBounds.NLogN.IntervalRunPrefix
public import IntegerMultBounds.NLogN.PhaseCellHaloRunMask

/-! Generate gap/body run lengths or their companion flags once per halo phase. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

private def intervals (s t band a b j : ℕ) : List (ℕ × ℕ) :=
  ((List.range j).filter (fun phase => decide (0 < haloLength s t band a b phase))).map
    (fun phase => (haloStart s t band a phase,haloStop s t band b phase))

private theorem intervals_succ (s t band a b j : ℕ) :
    intervals s t band a b (j+1) = intervals s t band a b j ++
      (if 0 < haloLength s t band a b j then
        [(haloStart s t band a j,haloStop s t band b j)] else []) := by
  by_cases h : 0 < haloLength s t band a b j <;>
    simp [intervals,List.range_succ,List.filter_append,h]

def runPairStream (flags : Bool) (A w : ℕ) (xs : List (Bool × ℕ)) : List (Fin (A+4)) :=
  xs.flatMap (fun r => tblPairs A w (if flags then (if r.1 then 1 else 0) else r.2) 0)

def haloRunScanCode (flags : Bool) : TblCode 16 := tblFor 4 15 (haloRunRowCode flags)

theorem haloRunScanCode_do {A W w s t band a b : ℕ} (flags : Bool) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hc : st.val 3 = 0)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w (haloRunScanCode flags) st (fun st' =>
      st'.val 3 = IntervalRunMask.cursor 0 (haloRunIntervals s t band a b) ∧
      st'.acc = (runPairStream flags A w
        (IntervalRunMask.prefixRuns 0 (haloRunIntervals s t band a b))).reverse++st.acc ∧
      ∀ k, k ∉ [(3 : Fin 16),4,8,9,10,11] → st'.val k = st.val k)
      (40*(t-s+1)+3) := by
  let Inv := fun j (st' : TblSt 16 A) =>
    st'.val 3 = IntervalRunMask.cursor 0 (intervals s t band a b j) ∧
    st'.acc = (runPairStream flags A w (IntervalRunMask.prefixRuns 0 (intervals s t band a b j))).reverse++st.acc ∧
    ∀ k, k ∉ [(3 : Fin 16),4,8,9,10,11] → st'.val k = st.val k
  have hN : t-s+1 < 2^W := by have := Nat.sub_le t s; nlinarith only [hwide,this]
  have hloop : TblDo A W w (haloRunScanCode flags) st (fun st' => Inv (t-s+1) st')
      (1+((t-s+1)*(37+1+2)+2)) := by
    apply TblDo.for (t-s+1) 37 hcount hN (by decide) Inv
    · refine ⟨?_,?_,?_⟩
      · simpa [intervals,IntervalRunMask.cursor] using hc
      · simp [intervals,IntervalRunMask.prefixRuns,runPairStream]
      · intro k hk
        have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
        simp [h4]
    · intro j hj st₁ ⟨hcursor,hacc,hf⟩ hindex hn
      have hr := haloRunRowCode_do (A := A) (W := W) (w := w) flags st₁
        ((hf 0 (by simp)).trans hs') ((hf 2 (by simp)).trans hband) hcursor hindex
        ((hf 6 (by simp)).trans hden) ((hf 7 (by simp)).trans hone) ((hf 12 (by simp)).trans hz)
        ((hf 13 (by simp)).trans ha) ((hf 14 (by simp)).trans hb) has hbs hs hst (by omega) hwide
      exact hr.mono (fun st₂ ⟨hcursor₂,hacc₂,hf₂⟩ => by
        refine ⟨(hf₂ 4 (by simp)).trans hindex,(hf₂ 15 (by simp)).trans hn,?_,?_,?_⟩
        · rw [intervals_succ,IntervalRunMask.cursor_append]
          by_cases hpos : 0 < haloLength s t band a b j <;>
            simpa [hpos,IntervalRunMask.cursor] using hcursor₂
        · rw [hacc₂,hacc,intervals_succ,IntervalRunMask.prefixRuns_append]
          by_cases hpos : 0 < haloLength s t band a b j <;>
            have hlt := hpos <;> simp only [haloLength,Nat.sub_pos_iff_lt] at hlt <;>
            simp [hpos,hlt,haloRunPairs,IntervalRunMask.prefixRuns,runPairStream,
              List.flatMap_append,List.reverse_append,List.append_assoc]
        · intro k hk
          have hrest : k ∉ [(3 : Fin 16),8,9,10,11] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto
          have h4 : k ≠ (4 : Fin 16) := by intro he; apply hk; simp [he]
          simpa [h4] using (hf₂ k hrest).trans (hf k hk)) le_rfl
    · intro st' hI _ _
      exact hI
  exact hloop.mono (fun st' hh => by simpa [Inv,intervals,haloRunIntervals,haloCellPhases] using hh) (by omega)

def haloRunCode (flags : Bool) : TblCode 16 :=
  haloRunScanCode flags ;; (tblNatSub 0 3 8 ;; .ins (.emit (if flags then 12 else 8) 12))

theorem haloRunCode_do {A W w s t band a b : ℕ} (flags : Bool) (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hc : st.val 3 = 0)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w (haloRunCode flags) st (fun st' =>
      st'.acc = (runPairStream flags A w
        (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).reverse++st.acc)
      (40*(t-s+1)+6) := by
  have hscan := haloRunScanCode_do (A := A) (W := W) (w := w) flags st hs' hband hc
    hden hone hz hcount ha hb has hbs hs hst hwide
  apply hscan.seq (K₂ := 3)
  intro st₁ ⟨hcursor,hacc,hf⟩
  have hsW : s < 2^W := by nlinarith only [hwide,hst]
  have hsub := tblNatSub_do (A := A) (W := W) (w := w) 0 3 8 st₁
    (by rw [hf 0 (by simp),hs']; exact hsW)
  apply hsub.seq (K₂ := 1)
  intro st₂ he₂
  subst he₂
  apply TblDo.ins (.emit (if flags then 12 else 8) 12)
  rw [IntervalRunMask.runs_eq_prefix]
  cases flags <;>
    simp [TblIns.run,runPairStream,List.flatMap_append,List.reverse_append,List.append_assoc,
      hacc,hcursor,hf 0 (by simp),hs',hf 12 (by simp),hz]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
