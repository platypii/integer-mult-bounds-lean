module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableBlocks

/-! # Compute input and kernel table shapes from the block length

The input row has offset `m` and length `3m+1`; the kernel row has offset `2m-1`
and length `4m`. Both are computed from the retained block-length word.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def chirpTableOffset (kernel : Bool) (m : ℕ) : ℕ := if kernel then 2 * m - 1 else m

def chirpTableLength (kernel : Bool) (m : ℕ) : ℕ := if kernel then 4 * m else 3 * m + 1

def tblChirpShape (kernel : Bool) : TblCode 48 :=
  if kernel then
    tblBlock 48 [.add 45 45 37, .zero 0, .inc 0, .sub 37 0 37,
      .add 45 45 44, .add 44 44 44] (.zero 0)
  else
    tblBlock 48 [.copy 45 37, .add 45 45 44, .add 44 45 44] (.inc 44)

/-- Shape arithmetic is checked without wraparound, and its temporary word is restored. -/
theorem tblChirpShape_do {A W w : ℕ} (kernel : Bool) (st : TblSt 48 A) (m : ℕ)
    (hm : st.val 45 = m) (h0 : st.val 0 = 0) (hm0 : 1 ≤ m) (hW : 4 * m + 1 < 2 ^ W) :
    TblDo A W w (tblChirpShape kernel) st
      (fun z => z.val = Function.update (Function.update st.val 37 (chirpTableOffset kernel m))
          44 (chirpTableLength kernel m) ∧ z.acc = st.acc)
      (if kernel then 7 else 4) := by
  have hW0 : W ≠ 0 := by
    intro h
    rw [h] at hW
    simp at hW
  cases kernel
  · apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hm]
      omega
    · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      constructor
      · funext i
        by_cases h44 : i = 44
        · subst i; simp [chirpTableLength, hm]; omega
        by_cases h37 : i = 37
        · subst i; simp [chirpTableOffset, hm]
        simp [Function.update_of_ne, h44, h37]
      · trivial
  · apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hm]
      omega
    · simp only [List.cons_append, List.nil_append, tblExactList, TblIns.exact]
      constructor
      · funext i
        by_cases h44 : i = 44
        · subst i; simp [chirpTableLength, hm]; omega
        by_cases h37 : i = 37
        · subst i; simp [chirpTableOffset, hm]; omega
        by_cases hi : i = 0
        · subst i; simp [h0]
        simp [Function.update_of_ne, h44, h37, hi]
      · trivial

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
