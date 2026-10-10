import IntegerMultBounds.Schoenhage.Rules
import IntegerMultBounds.Schoenhage.Level

/-! Cutting a word into padded pieces in one streaming pass. The driver is a
ruler that spells, two bits per action, what to emit next: copy the operand's
next bit, emit a padding zero, or end the current piece. With the ruler of
`K` pieces of `M` bits (the top piece takes one more bit) padded to `W` bits,
the emitted words are exactly the `W`-bit words of `pieces M K x`. -/

namespace IntegerMultBounds.Schoenhage

open Strm

namespace Rules

/-- What the ruler asks for. -/
inductive Act | copy | pad | sep

/-- The two-bit spelling of an action. -/
def Act.enc : Act → List Bool
  | .copy => [false, false]
  | .pad => [false, true]
  | .sep => [true, true]

/-- Read a ruler, two bits per action. -/
abbrev split : Rule 1 where
  Q := Option Bool
  q0 := none
  step q b o := match q with
    | none => (some b, none, fun _ => false)
    | some true => (none, some none, fun _ => false)
    | some false => if b then (none, some (some false), fun _ => false)
      else (none, some (some ((o 0).getD false)), fun _ => true)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

/-- The symbols the actions emit, and the operand left unread. -/
def sem : List Act → List Bool → List (Option Bool) × List Bool
  | [], x => ([], x)
  | .copy :: as, x => (some (x.headD false) :: (sem as x.tail).1, (sem as x.tail).2)
  | .pad :: as, x => (some false :: (sem as x).1, (sem as x).2)
  | .sep :: as, x => (none :: (sem as x).1, (sem as x).2)

theorem go_split (x : List Bool) : ∀ (as : List Act),
    go split none (as.flatMap Act.enc) (fun _ => x) = (none, (sem as x).1, fun _ => (sem as x).2)
  | [] => by simp [go, sem]
  | .copy :: as => by
    have ih := go_split x.tail as
    simp only [List.flatMap_cons, Act.enc, List.cons_append, List.nil_append, go, sem]
    rcases x with _ | ⟨b, x⟩
    · simp [go_split [] as] at ih ⊢
    · simp only [List.tail_cons] at ih ⊢
      simp [ih]
  | .pad :: as => by
    have ih := go_split x as
    simp only [List.flatMap_cons, Act.enc, List.cons_append, List.nil_append, go, sem]
    simp [ih]
  | .sep :: as => by
    have ih := go_split x as
    simp only [List.flatMap_cons, Act.enc, List.cons_append, List.nil_append, go, sem]
    simp [ih]

theorem output_split (as : List Act) (x : List Bool) :
    output split (as.flatMap Act.enc) (fun _ => x) = (sem as x).1 ++ [none] := by
  simp [output, go_split]

theorem sem_copies (x : List Bool) (as : List Act) : ∀ c,
    sem (List.replicate c .copy ++ as) x =
      ((fit c x).map some ++ (sem as (x.drop c)).1, (sem as (x.drop c)).2)
  | 0 => by simp [fit]
  | c + 1 => by
    rw [List.replicate_succ, List.cons_append, sem, sem_copies x.tail as c]
    rcases x with _ | ⟨b, x⟩ <;> simp [fit]

theorem sem_pads (x : List Bool) (as : List Act) : ∀ p,
    sem (List.replicate p .pad ++ as) x =
      ((List.replicate p false).map some ++ (sem as x).1, (sem as x).2)
  | 0 => by simp
  | p + 1 => by
    rw [List.replicate_succ, List.cons_append, sem, sem_pads x as p]
    simp [List.replicate_succ]

theorem sem_pads' (x : List Bool) (p : ℕ) :
    sem (List.replicate p .pad) x = ((List.replicate p false).map some, x) := by
  simpa [sem] using sem_pads x [] p

/-- The actions for `K` pieces of `M` bits, the top piece with one more bit, each padded to `W`. -/
def rulerActs (M W : ℕ) : ℕ → List Act
  | 0 => []
  | 1 => List.replicate (M + 1) .copy ++ List.replicate (W - (M + 1)) .pad
  | K + 2 => List.replicate M .copy ++ List.replicate (W - M) .pad ++ [.sep] ++ rulerActs M W (K + 1)

theorem bits_zero (n : ℕ) : bits n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bits, ih, List.replicate_succ]

theorem bits_append_zeros : ∀ (M W u : ℕ), M ≤ W →
    bits M u ++ List.replicate (W - M) false = bits W (u % 2 ^ M)
  | 0, W, u, _ => by simp [bits, bits_zero, Nat.mod_one]
  | M + 1, W + 1, u, h => by
    have ih := bits_append_zeros M W (u / 2) (by omega)
    simp only [bits, List.cons_append, Nat.add_sub_add_right, ih, List.cons.injEq]
    constructor
    · rw [pow_succ, mul_comm, Nat.mod_mul_right_mod]
    · congr 1
      rw [pow_succ, mul_comm, Nat.mod_mul_right_div_self]

theorem bval_drop' (k : ℕ) (v : List Bool) : bval (v.drop k) = bval v / 2 ^ k := by
  by_cases hk : k ≤ v.length
  · exact bval_drop k v hk
  · have h1 : v.drop k = [] := List.drop_eq_nil_of_le (by omega)
    have h2 := bval_lt v
    have h3 : 2 ^ v.length ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1, bval_nil, Nat.div_eq_of_lt (by omega)]

theorem sem_ruler {M W : ℕ} (hMW : M + 1 ≤ W) : ∀ (K : ℕ) (v : List Bool), 0 < K →
    bval v < 2 ^ (M * K + 1) →
    (sem (rulerActs M W K) v).1 ++ [none] = syms ((pieces M K (bval v)).map (bits W))
  | 0, _, h, _ => absurd h (lt_irrefl 0)
  | 1, v, _, hv => by
    rw [rulerActs, sem_copies, sem_pads']
    simp only [List.append_nil, pieces, List.map_cons, List.map_nil, syms_cons, syms_nil]
    rw [fit_eq_bits, ← List.map_append, bits_append_zeros _ _ _ hMW,
      Nat.mod_eq_of_lt (by simpa using hv)]
  | K + 2, v, _, hv => by
    have ih := sem_ruler hMW (K + 1) (v.drop M) (by omega) (by
      rw [bval_drop', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos M), ← pow_add]
      convert hv using 2; ring)
    rw [rulerActs, List.append_assoc, List.append_assoc, sem_copies, sem_pads]
    simp only [List.singleton_append, sem]
    rw [pieces, List.map_cons, syms_cons, ← bval_drop', ← ih, fit_eq_bits,
      ← bits_append_zeros _ _ _ (by omega)]
    simp

/-- The ruler word. -/
def ruler (M W K : ℕ) : List Bool := (rulerActs M W K).flatMap Act.enc

theorem output_split_ruler {M W K : ℕ} (hMW : M + 1 ≤ W) (hK : 0 < K) (v : List Bool)
    (hv : bval v < 2 ^ (M * K + 1)) :
    output split (ruler M W K) (fun _ => v) = syms ((pieces M K (bval v)).map (bits W)) := by
  rw [ruler, output_split, sem_ruler hMW K v hK hv]

end Rules

end IntegerMultBounds.Schoenhage
