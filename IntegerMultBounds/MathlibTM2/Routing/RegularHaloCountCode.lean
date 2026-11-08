module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountRow

/-! Fixed arithmetic controller for the complete regular halo count stream.
Only N, L and the overlap width B are inputs; parity padding is generated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountCode
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz RegularHaloCountRow

def paddedCount (N : ℕ) : ℕ := N+N%2

def countValues (L B N : ℕ) : List ℕ :=
  (List.range (paddedCount N)).flatMap (values L B N)

def initCounts : TblCode 16 :=
  tblBlock 16 [.zero 8,.inc 8,.inc 8,.mod 0 8 9,.add 0 9 15,.sub 1 2 5,.add 1 2 6] (.zero 12)

theorem initCounts_do {A W w L B N : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = B)
    (hgap : B ≤ L) (hwide : N+2 < 2^W) (hsize : L+B < 2^W) :
    TblDo A W w initCounts st (fun st' =>
      st'.val 0 = N ∧ st'.val 1 = L ∧ st'.val 2 = B ∧
      st'.val 5 = L-B ∧ st'.val 6 = L+B ∧ st'.val 12 = 0 ∧
      st'.val 15 = paddedCount N ∧ st'.val 8 = 2 ∧ st'.acc = st.acc) 8 := by
  have hW : W ≠ 0 := by
    intro he
    simp only [he,pow_zero] at hwide
    omega
  apply TblDo.block
  · simp [hW,tblFitsList,TblIns.fits,TblIns.exact,hN,hL,hB]
    omega
  · simp [tblExactList,TblIns.exact,hN,hL,hB,paddedCount]

def enumerate : TblCode 16 := tblFor 4 15 row

theorem enumerate_do {A W w L B N : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = B)
    (hbody : st.val 5 = L-B) (hsingle : st.val 6 = L+B) (hz : st.val 12 = 0)
    (hcount : st.val 15 = paddedCount N) (hwide : paddedCount N < 2^W) :
    TblDo A W w enumerate st (fun st' =>
      st'.acc = ((countValues L B N).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc)
      (10*paddedCount N+3) := by
  have hNwide : N < 2^W := by unfold paddedCount at hwide; omega
  have h := descriptorEnumeration_do row
    (fun j => (values L B N j).flatMap (fun x => tblPairs A w x 0)) st hcount hwide (K := 7) (by
      intro j _ st₁ hf hj
      exact (row_do st₁ ((hf 0 (by simp)).trans hN) ((hf 1 (by simp)).trans hL)
        ((hf 2 (by simp)).trans hB) hj ((hf 5 (by simp)).trans hbody)
        ((hf 6 (by simp)).trans hsingle) ((hf 12 (by simp)).trans hz) hNwide).mono
          (fun st₂ ⟨ha,hframe⟩ => ⟨ha,by
            intro i hi
            apply hframe
            intro he
            subst i
            simp at hi⟩) le_rfl)
  simpa only [enumerate,countValues,List.flatMap_assoc,Nat.mul_comm] using h

def publishClock : TblCode 16 := tblBlock 16 [.div 15 8 11] (.emit 11 12)

theorem publishClock_do {A W w N : ℕ} (st : TblSt 16 A)
    (hcount : st.val 15 = paddedCount N) (htwo : st.val 8 = 2) (hz : st.val 12 = 0) :
    TblDo A W w publishClock st (fun st' =>
      st'.acc = (tblPairs A w (paddedCount N/2) 0).reverse++st.acc ∧
      ∀ i, i ≠ 11 → st'.val i = st.val i) 2 := by
  apply TblDo.block
  · simp [tblFitsList,TblIns.fits]
  · constructor
    · simp [tblExactList,TblIns.exact,hcount,htwo,hz]
    · intro i hi; simp [tblExactList,TblIns.exact,hi]

def generate : TblCode 16 := initCounts ;; publishClock ;; enumerate

theorem generate_do {A W w L B N : ℕ} (st : TblSt 16 A)
    (hN : st.val 0 = N) (hL : st.val 1 = L) (hB : st.val 2 = B)
    (hgap : B ≤ L) (hwide : N+2 < 2^W) (hsize : L+B < 2^W) :
    TblDo A W w generate st (fun st' =>
      st'.acc = (tblPairs A w (paddedCount N/2) 0++
        (countValues L B N).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc)
      (10*paddedCount N+13) := by
  have hi := initCounts_do (A := A) (W := W) (w := w) st hN hL hB hgap hwide hsize
  have he : TblDo A W w generate st (fun st' =>
      st'.acc = (tblPairs A w (paddedCount N/2) 0++
        (countValues L B N).flatMap (fun x => tblPairs A w x 0)).reverse++st.acc)
      (8+(2+(10*paddedCount N+3))) := hi.seq (K₂ := 2+(10*paddedCount N+3))
    (fun st₁ ⟨hN,hL,hB,hbody,hsingle,hz,hcount,htwo,hacc⟩ => by
      have hc := publishClock_do (A := A) (W := W) (w := w) st₁ hcount htwo hz
      exact hc.seq (K₂ := 10*paddedCount N+3) (fun st₂ ⟨hclock,hframe⟩ =>
        (enumerate_do st₂ ((hframe 0 (by decide)).trans hN) ((hframe 1 (by decide)).trans hL)
          ((hframe 2 (by decide)).trans hB) ((hframe 5 (by decide)).trans hbody)
          ((hframe 6 (by decide)).trans hsingle) ((hframe 12 (by decide)).trans hz)
          ((hframe 15 (by decide)).trans hcount) (by unfold paddedCount; omega)).mono
            (fun st₃ ha => by rw [ha,hclock,hacc]; simp [List.reverse_append,List.append_assoc]) le_rfl))
  exact he.mono (fun _ ha => ha) (by omega)

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountCode
