module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRawGatherData

/-! # Compute the number of chirp blocks from binary dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def chirpBlockCount (t m : ℕ) : ℕ := (t - 1) / m + 1

def tblChirpBlockCount : TblCode 10 :=
  tblBlock 10 [.zero 8, .inc 8, .sub 1 8 4, .div 4 2 4] (.inc 4)

theorem chirpBlockCount_mul_le (t m : ℕ) : chirpBlockCount t m * m ≤ t + m := by
  have h := Nat.div_mul_le_self (t - 1) m
  unfold chirpBlockCount
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Five checked atoms compute the ceiling division, retaining all dimension inputs. -/
theorem tblChirpBlockCount_do {A W e : ℕ} (st : TblSt 10 A) (t m : ℕ)
    (ht : st.val 1 = t) (hm : st.val 2 = m) (ht0 : 0 < t) (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpBlockCount st
      (fun z => z.val 4 = chirpBlockCount t m ∧
        (∀ i : Fin 10, i.val < 4 → z.val i = st.val i) ∧ z.acc = st.acc ∧
        (∀ i, z.val i < 2 ^ W)) 5 := by
  have htW : t < 2 ^ W := by simpa only [ht] using hfit 1
  have h1 : 1 < 2 ^ W := lt_of_le_of_lt ht0 htW
  have hcount : chirpBlockCount t m < 2 ^ W := by
    have hd := Nat.div_le_self (t - 1) m
    unfold chirpBlockCount
    omega
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, ht, hm, h1]
    have hd := Nat.div_le_self (t - 1) m
    omega
  · constructor
    · simp [tblExactList, TblIns.exact, ht, hm, chirpBlockCount]
    constructor
    · intro i hi
      fin_cases i <;> first | (simp at hi; done) | simp [tblExactList, TblIns.exact]
    constructor
    · rfl
    · intro i
      fin_cases i <;> simp [tblExactList, TblIns.exact, ht, hm]
      all_goals first
        | exact hfit 0
        | exact htW
        | simpa only [hm] using hfit 2
        | exact hfit 3
        | simpa only [chirpBlockCount] using hcount
        | exact hfit 5
        | exact hfit 6
        | exact hfit 7
        | simpa using h1
        | exact hfit 9

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
