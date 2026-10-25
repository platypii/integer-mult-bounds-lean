module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData

/-! # Structural rows of actual cell output words -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- Split a fixed number of equal-length rows, including empty rows. -/
def outputRows {K : Type*} : ℕ → ℕ → List K → List (List K)
  | 0, _, _ => []
  | M + 1, L, xs => xs.take L :: outputRows M L (xs.drop L)

@[simp] theorem outputRows_length {K : Type*} (M L : ℕ) (xs : List K) :
    (outputRows M L xs).length = M := by
  induction M generalizing xs with
  | zero => rfl
  | succ M ih => simp [outputRows, ih]

theorem outputRows_spec {K : Type*} (M L : ℕ) (xs : List K) (hlen : xs.length = M * L) :
    (outputRows M L xs).flatten = xs ∧ ∀ row ∈ outputRows M L xs, row.length = L := by
  induction M generalizing xs with
  | zero =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp [outputRows, hx]
  | succ M ih =>
      have hL : L ≤ xs.length := by rw [hlen, Nat.succ_mul]; omega
      have hdrop : (xs.drop L).length = M * L := by simp [hlen, Nat.succ_mul]
      obtain ⟨hflat, hrows⟩ := ih (xs.drop L) hdrop
      constructor
      · simpa only [outputRows, List.flatten_cons, hflat] using List.take_append_drop L xs
      · intro row hrow
        simp only [outputRows, List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · simp [List.length_take, Nat.min_eq_left hL]
        · exact hrows row hrow

/-- The coordinate-order publication of a compact reversed-row stream. -/
def publishedWords {K : Type*} (M L : ℕ) (xs : List K) : List K :=
  (outputRows M L xs).flatMap List.reverse

@[simp] theorem publishedWords_length {K : Type*} (M L : ℕ) (xs : List K)
    (hlen : xs.length = M * L) : (publishedWords M L xs).length = M * L := by
  have hh := congrArg List.length (outputRows_spec M L xs hlen).1
  simpa only [publishedWords, List.length_flatMap, List.length_reverse, List.length_flatten] using hh.trans hlen

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- The caller supplies the actual word list, not a row decomposition. -/
theorem publishWords_exec (M L w : ℕ) (xs : List GaussianInt) (hlen : xs.length = M * L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 84], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publishFromDimensionsCost M L w ∧
      Exec body publishFromDimensions (mk v S) m
        (mk v' { S with R := Function.update S.R 93 (cstream A w (publishedWords M L xs) ++ tail) }) := by
  obtain ⟨hflat, hrow⟩ := outputRows_spec M L xs hlen
  exact publishFromDimensions_exec (body := body) M L w (outputRows M L xs)
    (outputRows_length M L xs) hrow v S tail hbatch hrows hwidth (by simpa only [hflat] using hsrc) hclean

@[simp] theorem executedOutputWords_length (s t p u q l M L j cExp : ℕ) (lo : ℕ → ZMod s)
    (C : ℕ → ZMod s → GaussianInt) :
    (executedOutputWords s t p u q l M L j cExp lo C).length = M * L := by
  unfold executedOutputWords
  rw [weightedOutputNumerators_length]
  · exact executedInteriorWords_length s t p u q l M L j cExp lo C
  · simp [executedOutputTable]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
