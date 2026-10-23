module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlLoop

/-! # Restore the working variables of gathering-control generation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpControlClear : TblCode 10 :=
  tblBlock 10 [.zero 4, .zero 5, .zero 6, .zero 7, .zero 8] (.zero 9)

/-- The six owned variables began at zero; the four dimension words are retained. -/
theorem tblChirpControlClear_do {A W e : ℕ} (st u : TblSt 10 A) (s t m w j : ℕ)
    (hready : ChirpControlReady st s t m w 0) (hu : ChirpControlReady u s t m w j)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpControlClear u
      (fun z => z.val = st.val ∧ z.acc = u.acc) 6 := by
  rcases hready with ⟨hs, ht, hm, hw, _⟩
  rcases hu with ⟨hsu, htu, hmu, hwu, _⟩
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits]
  · constructor
    · funext i
      fin_cases i <;> simp (disch := decide) [tblExactList, TblIns.exact, hs, ht, hm, hw, hsu, htu, hmu, hwu,
        hzero]
    · rfl

/-- Sum the actual per-packet bounds once, rather than charging the largest advance per block. -/
theorem chirpControlLoopCost_eq (W e : ℕ) (ds : List ℕ) :
    chirpControlLoopCost W e ds =
      ds.length * (6 * tblC W e + 11 * W + 10) + (4 * W + 2) * ds.sum + 1 := by
  induction ds with
  | nil => simp [chirpControlLoopCost]
  | cons d ds ih =>
    unfold chirpControlLoopCost at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc _ = (6 * tblC W e + W * (4 * d + 11) + 2 * d + 10) +
        ((List.map (fun d => 6 * tblC W e + W * (4 * d + 11) + 2 * d + 10) ds).sum + 1) := by omega
      _ = _ := by rw [ih]; ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
