module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupLoop

/-! Closed output and spectator frame for affine source generation. The loop's
accumulator is the reverse of the desired complete profile word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def optionalAffineSourceGroupWord (Li Lk i k o g : ℕ) : List Bool → List (Fin (A + 4))
  | [] => []
  | b :: rest => affineProfileFrames (Li + Lk) (List.replicate g (b, if b then i * k + o else 0)) ++
      optionalAffineSourceGroupWord Li Lk (i + 1) k o g rest

theorem optionalAffineSourceGroupWord_length (Li Lk i k o g : ℕ) (input : List Bool) :
    (optionalAffineSourceGroupWord (A := A) Li Lk i k o g input).length = input.length * (g * (Li + Lk + 3)) := by
  induction input generalizing i with
  | nil => simp [optionalAffineSourceGroupWord]
  | cons b rest ih =>
    simp [optionalAffineSourceGroupWord, affineProfileFrames_length, ih, Nat.add_mul]
    omega

theorem optionalAffineSourceGroupWord_profile (Li Lk i k o g n : ℕ) (active : Fin n → Bool) :
    optionalAffineSourceGroupWord (A := A) Li Lk i k o g (List.ofFn active) =
      affineProfileFrames (Li + Lk) ((List.ofFn (fun c : Fin n => List.replicate g
        (active c, if active c then (i + c.val) * k + o else 0))).flatten) := by
  induction n generalizing i with
  | zero => simp [optionalAffineSourceGroupWord, affineProfileFrames]
  | succ n ih =>
    simp only [List.ofFn_succ, optionalAffineSourceGroupWord, List.flatten_cons,
      affineProfileFrames_append, ih]
    simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

theorem optionalAffineSourceGroupTrace_keep (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (Li Lk i k o g : ℕ) (input : List Bool)
    (j : Fin T) (hc : j ≠ src) (hs : j ≠ saved) (hd : j ≠ dst) (hi : j ≠ rg 0) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input j = R j := by
  induction input generalizing R i with
  | nil => rfl
  | cons x rest ih =>
    rw [optionalAffineSourceGroupTraceBank, ih]
    simp [optionalAffineSourceGroupReverseBank, hc, hs, hd, hi]

theorem optionalAffineSourceGroupTrace_output (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (_hcd : dst ≠ src) (_hsd : dst ≠ saved) (hid : dst ≠ rg 0)
    (Li Lk i k o g : ℕ) (input : List Bool) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input dst =
      (optionalAffineSourceGroupWord Li Lk i k o g input).reverse ++ R dst := by
  induction input generalizing R i with
  | nil => simp [optionalAffineSourceGroupTraceBank, optionalAffineSourceGroupWord]
  | cons x rest ih =>
    rw [optionalAffineSourceGroupTraceBank, ih]
    simp [optionalAffineSourceGroupReverseBank, optionalAffineSourceGroupWord, hid,
      List.reverse_append, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
