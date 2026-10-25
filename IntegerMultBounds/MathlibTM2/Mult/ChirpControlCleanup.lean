module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlLoop

/-! # Restore the working variables of gathering-control generation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpControlClear : TblCode 10 :=
  tblBlock 10 [.zero 4, .zero 5, .zero 6, .zero 7, .zero 8] (.zero 9)

/-- Clearing the owned words restores a bank with the same four retained inputs. -/
theorem tblChirpControlClear_frame_do {A W e : ℕ} (st u : TblSt 10 A)
    (hframe : ∀ i : Fin 10, i.val < 4 → u.val i = st.val i)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpControlClear u
      (fun z => z.val = st.val ∧ z.acc = u.acc) 6 := by
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits]
  · constructor
    · funext i
      fin_cases i <;> simp (disch := decide) [tblExactList, TblIns.exact, hframe, hzero]
    · rfl

/-- The six owned variables began at zero; the four dimension words are retained. -/
theorem tblChirpControlClear_do {A W e : ℕ} (st u : TblSt 10 A) (s t m w j : ℕ)
    (hready : ChirpControlReady st s t m w 0) (hu : ChirpControlReady u s t m w j)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpControlClear u
      (fun z => z.val = st.val ∧ z.acc = u.acc) 6 := by
  rcases hready with ⟨hs, ht, hm, hw, _⟩
  rcases hu with ⟨hsu, htu, hmu, hwu, _⟩
  apply tblChirpControlClear_frame_do st u ?_ hzero
  intro i hi
  fin_cases i <;> first | (simp at hi; done) | simp [hs, ht, hm, hw, hsu, htu, hmu, hwu]

/-- Sum the actual per-packet bounds once, rather than charging the largest advance per block. -/
theorem chirpControlLoopCost_eq (W e : ℕ) (ds : List ℕ) :
    chirpControlLoopCost W e ds =
      ds.length * (6 * tblC W e + 11 * W + 10) + 6 * ds.sum + 1 := by
  induction ds with
  | nil => simp [chirpControlLoopCost]
  | cons d ds ih =>
    unfold chirpControlLoopCost at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc _ = (6 * tblC W e + 6 * d + 11 * W + 10) +
        ((List.map (fun d => 6 * tblC W e + 6 * d + 11 * W + 10) ds).sum + 1) := by omega
      _ = _ := by rw [ih]; ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
