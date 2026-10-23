module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceLoop

/-! Closed output and spectator frame for affine source generation. The loop's
accumulator is the reverse of the desired complete profile word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def affineSourceWord (Li Lk i k o : ℕ) : ℕ → List (Fin (A + 4))
  | 0 => []
  | n + 1 => affineProfileFrames (Li + Lk) [(true, i * k + o)] ++ affineSourceWord Li Lk (i + 1) k o n

theorem affineSourceWord_profile (Li Lk i k o n : ℕ) :
    affineSourceWord (A := A) Li Lk i k o n = affineProfileFrames (Li + Lk)
      (List.ofFn (fun c : Fin n => (true, (i + c.val) * k + o))) := by
  induction n generalizing i with
  | zero => simp [affineSourceWord, affineProfileFrames]
  | succ n ih =>
    simp [affineSourceWord, List.ofFn_succ, affineProfileFrames, ih,
      Nat.add_assoc, Nat.add_comm 1, List.append_assoc]

theorem affineSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (Li Lk i k o : ℕ) (input : List (Fin (A + 4)))
    (j : Fin T) (hc : j ≠ count) (hs : j ≠ saved) (hd : j ≠ dst) (hi : j ≠ rg 0) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input j = R j := by
  induction input generalizing R i with
  | nil => rfl
  | cons x rest ih =>
    rw [affineSourceTraceBank, ih]
    simp [affineSourceReverseStepBank, hc, hs, hd, hi]

theorem affineSourceTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (hcd : dst ≠ count) (hsd : dst ≠ saved) (hid : dst ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input dst =
      (affineSourceWord Li Lk i k o input.length).reverse ++ R dst := by
  induction input generalizing R i with
  | nil => simp [affineSourceTraceBank, affineSourceWord]
  | cons x rest ih =>
    rw [affineSourceTraceBank, ih]
    simp [affineSourceReverseStepBank, affineSourceWord, hcd, hsd, hid,
      List.reverse_append, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
