module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputRows
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedRun

/-! # Coordinate reads after row publication -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem reversedRows_getD {K : Type} (blocks : List (List K)) (L : ℕ)
    (hlen : ∀ row ∈ blocks, row.length = L) (n i : ℕ) (hn : n < blocks.length) (hi : i < L)
    (default : K) :
    (blocks.flatMap List.reverse).getD (n * L + i) default =
      blocks.flatten.getD (n * L + (L - 1 - i)) default := by
  have hflat : blocks.flatten.length = blocks.length * L := length_flatten_const blocks hlen
  have hrev : (blocks.flatMap List.reverse).length = blocks.length * L := by
    simpa only [List.length_flatMap, List.length_reverse, List.length_flatten] using hflat
  have hbound := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hn)
  have hidx : n * L + i < blocks.length * L := by nlinarith
  have href : L - 1 - i < L := by omega
  have hidx' : n * L + (L - 1 - i) < blocks.length * L := by nlinarith
  have hrow : blocks[n].length = L := hlen _ (List.getElem_mem hn)
  have e₁ := getElem_flatMap_len List.reverse L blocks
    (fun row hr => by simp [hlen row hr]) n i hn hi (by rw [hrev]; nlinarith)
  have e₂ := getElem_flatMap_len id L blocks
    (fun row hr => by simp [hlen row hr]) n (L - 1 - i) hn href (by
      simpa only [List.flatMap_id, hflat, Nat.mul_comm L n] using hidx')
  rw [List.getD_eq_getElem _ _ (by simpa [hrev] using hidx),
    List.getD_eq_getElem _ _ (by simpa [hflat] using hidx')]
  simp only [Nat.mul_comm L n] at e₁ e₂
  rw [e₁, List.getElem_reverse]
  simpa only [List.flatMap_id, hrow, id_eq] using e₂.symm

theorem publishedWords_getD {K : Type} (M L : ℕ) (xs : List K) (hlen : xs.length = M * L)
    (n i : ℕ) (hn : n < M) (hi : i < L) (default : K) :
    (publishedWords M L xs).getD (n * L + i) default = xs.getD (n * L + (L - 1 - i)) default := by
  obtain ⟨hflat, hrows⟩ := outputRows_spec M L xs hlen
  simpa only [publishedWords, hflat] using reversedRows_getD (outputRows M L xs) L hrows n i
    (by simpa only [outputRows_length] using hn) hi default

/-- Actual tape-word reads use the same reflection as the numerical cell run. -/
theorem publishedWords_read {A : ℕ} (M L w : ℕ) (xs : List GaussianInt) (hlen : xs.length = M * L)
    (tail : List (Fin (A + 4))) (n i : ℕ) (hn : n < M) (hi : i < L) :
    decodeWord (((cstream A w (publishedWords M L xs) ++ tail).drop ((n * L + i) * w)).take w) =
      decodeWord (((cstream A w xs ++ tail).drop ((n * L + (L - 1 - i)) * w)).take w) := by
  have hbound := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hn)
  have href : L - 1 - i < L := by omega
  have hidx : n * L + i < (publishedWords M L xs).length := by
    rw [publishedWords_length M L xs hlen]; nlinarith
  have hidx' : n * L + (L - 1 - i) < xs.length := by rw [hlen]; nlinarith
  rw [cstream_word w _ tail _ hidx, cstream_word w _ tail _ hidx']
  have hh := publishedWords_getD M L xs hlen n i hn hi 0
  rw [List.getD_eq_getElem _ _ hidx, List.getD_eq_getElem _ _ hidx'] at hh
  rw [hh]

/-- The valid numerical run reads its final value directly from the published
forward-order coordinate, with no additional rounding or error. -/
theorem executedRun_y_published {A : ℕ} (s t p u q l w M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) (n : Fin M) (i : Fin L) (tail : List (Fin (A + 4))) :
    (executedRun s t p u q l w M L j cExp lo C n tail).y i =
      (value q (decodeWord (((cstream A w
        (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo C)) ++ tail).drop
          ((n.val * L + i.val) * w)).take w))).re := by
  have hh := publishedWords_read M L w (executedOutputWords s t p u q l M L j cExp lo C)
    (executedOutputWords_length s t p u q l M L j cExp lo C) tail n i n.isLt i.isLt
  simpa only [executedRun, preparedRun, interiorRun] using
    congrArg (fun z => (value q z).re) hh.symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
