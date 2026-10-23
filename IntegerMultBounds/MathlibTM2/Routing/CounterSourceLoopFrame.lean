module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceLoop

/-! Closed output and spectator frame for direct counter source generation. The loop's
accumulator is the reverse of the desired complete profile word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def counterSourceWord (L i : ℕ) : ℕ → List (Fin (A + 4))
  | 0 => []
  | n + 1 => affineProfileFrames (L) [(true, i)] ++ counterSourceWord L (i + 1) n

theorem counterSourceWord_profile (L i n : ℕ) :
    counterSourceWord (A := A) L i n = affineProfileFrames (L)
      (List.ofFn (fun c : Fin n => (true, i + c.val))) := by
  induction n generalizing i with
  | zero => simp [counterSourceWord, affineProfileFrames]
  | succ n ih =>
    simp [counterSourceWord, List.ofFn_succ, affineProfileFrames, ih,
      Nat.add_assoc, Nat.add_comm 1, List.append_assoc]

theorem counterSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (L i : ℕ) (input : List (Fin (A + 4)))
    (j : Fin T) (hc : j ≠ count) (hs : j ≠ saved) (hd : j ≠ dst) (hi : j ≠ rg 0) :
    counterSourceTraceBank R rg count saved dst L i input j = R j := by
  induction input generalizing R i with
  | nil => rfl
  | cons x rest ih =>
    rw [counterSourceTraceBank, ih]
    simp [counterSourceReverseStepBank, hc, hs, hd, hi]

theorem counterSourceTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (hcd : dst ≠ count) (hsd : dst ≠ saved) (hid : dst ≠ rg 0)
    (L i : ℕ) (input : List (Fin (A + 4))) :
    counterSourceTraceBank R rg count saved dst L i input dst =
      (counterSourceWord L i input.length).reverse ++ R dst := by
  induction input generalizing R i with
  | nil => simp [counterSourceTraceBank, counterSourceWord]
  | cons x rest ih =>
    rw [counterSourceTraceBank, ih]
    simp [counterSourceReverseStepBank, counterSourceWord, hcd, hsd, hid,
      List.reverse_append, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
