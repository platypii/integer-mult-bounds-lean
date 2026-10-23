module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceLoop

/-! Closed output and spectator frame for affine source generation. The loop's
accumulator is the reverse of the desired complete profile word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def optionalAffineSourceWord (Li Lk i k o : ℕ) : List Bool → List (Fin (A + 4))
  | [] => []
  | b :: rest => affineProfileFrames (Li + Lk) [(b, if b then i * k + o else 0)] ++
      optionalAffineSourceWord Li Lk (i + 1) k o rest

theorem optionalAffineSourceWord_length (Li Lk i k o : ℕ) (input : List Bool) :
    (optionalAffineSourceWord (A := A) Li Lk i k o input).length = input.length * (Li + Lk + 3) := by
  induction input generalizing i with
  | nil => simp [optionalAffineSourceWord]
  | cons b rest ih =>
    simp [optionalAffineSourceWord, affineProfileFrames, ih, Nat.add_mul]
    omega

theorem optionalAffineSourceWord_profile (Li Lk i k o n : ℕ) (active : Fin n → Bool) :
    optionalAffineSourceWord (A := A) Li Lk i k o (List.ofFn active) =
      affineProfileFrames (Li + Lk) (List.ofFn (fun c : Fin n =>
        (active c, if active c then (i + c.val) * k + o else 0))) := by
  induction n generalizing i with
  | zero => simp [optionalAffineSourceWord, affineProfileFrames]
  | succ n ih =>
    simp [List.ofFn_succ, optionalAffineSourceWord, affineProfileFrames, ih,
      Nat.add_assoc, Nat.add_comm 1, List.append_assoc]

theorem optionalAffineSourceTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (Li Lk i k o : ℕ) (input : List Bool)
    (j : Fin T) (hc : j ≠ src) (hs : j ≠ saved) (hd : j ≠ dst) (hi : j ≠ rg 0) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input j = R j := by
  induction input generalizing R i with
  | nil => rfl
  | cons x rest ih =>
    rw [optionalAffineSourceTraceBank, ih]
    simp [optionalAffineSourceReverseStepBank, hc, hs, hd, hi]

theorem optionalAffineSourceTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (_hcd : dst ≠ src) (_hsd : dst ≠ saved) (hid : dst ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List Bool) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input dst =
      (optionalAffineSourceWord Li Lk i k o input).reverse ++ R dst := by
  induction input generalizing R i with
  | nil => simp [optionalAffineSourceTraceBank, optionalAffineSourceWord]
  | cons x rest ih =>
    rw [optionalAffineSourceTraceBank, ih]
    simp [optionalAffineSourceReverseStepBank, optionalAffineSourceWord, hid,
      List.reverse_append, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
