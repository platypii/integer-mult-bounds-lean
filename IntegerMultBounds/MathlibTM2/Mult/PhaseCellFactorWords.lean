module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowData

/-! # A single distance vector determines every integer factor row -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators IntegerMultBounds.MathlibTM2.Fast

def distanceFactorWord (P s t u band k : ℕ) : GaussianInt :=
  if k = 0 then 0 else ⟨coefficientNumerator P s t u band k, 0⟩

def distanceFactorWords (P s t u band L : ℕ) : List GaussianInt :=
  (List.range L).map (distanceFactorWord P s t u band)

@[simp] theorem distanceFactorWords_length (P s t u band L : ℕ) :
    (distanceFactorWords P s t u band L).length = L := by simp [distanceFactorWords]

/-- A row consists of a reversed prefix through its zero diagonal, followed by
the forward distance prefix. Exponentials are evaluated once per distance. -/
theorem rowFactorWords_from_distances (P s t u band L i : ℕ) (hi : i < L) :
    rowFactorWords P s t u band L i =
      ((distanceFactorWords P s t u band L).take (i + 1)).reverse ++
        ((distanceFactorWords P s t u band L).drop 1).take (L - i - 1) := by
  apply List.ext_getElem
  · simp [rowFactorWords]
    omega
  · intro j hj hj'
    have hjL : j < L := by simpa [rowFactorWords] using hj
    simp only [rowFactorWords, List.getElem_map, List.getElem_range]
    by_cases hji : j ≤ i
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_reverse, List.length_take, distanceFactorWords_length,
        Nat.min_eq_left (by omega : i + 1 ≤ L), List.getElem_take,
        distanceFactorWords, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
        Nat.min_eq_left (by omega : i + 1 ≤ L)]
      have hidx : i + 1 - 1 - j = i - j := by omega
      rw [hidx]
      by_cases he : j = i
      · subst j
        simp [distanceFactorWord, gap]
        rfl
      · simp [distanceFactorWord, gap, he, Ne.symm he,
          show i - j ≠ 0 by omega, show j - i = 0 by omega]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_take, List.getElem_drop, List.length_reverse, List.length_take,
        distanceFactorWords_length, Nat.min_eq_left (by omega : i + 1 ≤ L),
        distanceFactorWords, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
        Nat.min_eq_left (by omega : i + 1 ≤ L)]
      have hidx : 1 + (j - (i + 1)) = j - i := by omega
      rw [hidx]
      simp [distanceFactorWord, gap, show j ≠ i by omega, show i ≠ j by omega,
        show i - j = 0 by omega, show j - i ≠ 0 by omega]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
