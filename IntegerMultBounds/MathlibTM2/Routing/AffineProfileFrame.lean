module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileLoop

/-! Closed tape contents after affine profile traversal: complete archived input,
generated coordinates, final index and unchanged spectator tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def affineProfileOutput (Li Lk Ls index k o N : ℕ) : List (Bool × ℕ) → List (Fin (A + 4))
  | [] => []
  | (enabled, q) :: rest => affineProfileOutput Li Lk Ls (index + 1) k o N rest ++
      (binSyms (Li + Lk) (N - 1 - (index * k + o)) ++ separator ::
        (binSyms Ls (if enabled then q + 1 else 0) ++ [separator]))

theorem affineProfileTrace_keep (R : Fin T → List (Fin (A + 4)))
    (rg : AffineProfileReg → Fin T) (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ))
    (j : Fin T) (hs : j ≠ rg .src) (ha : j ≠ rg .archive) (hc : j ≠ rg .index) (hd : j ≠ rg .dst) :
    affineProfileTraceBank R rg Li Lk Ls index k o N entries j = R j := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [affineProfileTraceBank, ih]
    simp [affineProfileCallBank, hs, ha, hc, hd]

theorem affineProfileTrace_src (R : Fin T → List (Fin (A + 4)))
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ))
    (hsrc : R (rg .src) = affineProfileFrames Ls entries) :
    affineProfileTraceBank R rg Li Lk Ls index k o N entries (rg .src) = [] := by
  induction entries generalizing R index with
  | nil => exact hsrc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    apply ih
    simp [affineProfileCallBank, hrg.eq_iff]

theorem affineProfileTrace_archive (R : Fin T → List (Fin (A + 4)))
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ)) :
    affineProfileTraceBank R rg Li Lk Ls index k o N entries (rg .archive) =
      (affineProfileFrames Ls entries).reverse ++ R (rg .archive) := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [affineProfileTraceBank, ih]
    simp [affineProfileCallBank, affineProfileFrames, hrg.eq_iff, List.reverse_append, List.append_assoc]

theorem affineProfileTrace_index (R : Fin T → List (Fin (A + 4)))
    (rg : AffineProfileReg → Fin T) (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ))
    (hc : R (rg .index) = binSyms Li index) :
    affineProfileTraceBank R rg Li Lk Ls index k o N entries (rg .index) =
      binSyms Li (index + entries.length) := by
  induction entries generalizing R index with
  | nil => exact hc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    have hh := ih
      (affineProfileCallBank R rg Li Lk Ls index k o N q x (affineProfileFrames Ls rest))
      (index + 1) (by simp [affineProfileCallBank])
    simpa only [affineProfileTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

theorem affineProfileTrace_output (R : Fin T → List (Fin (A + 4)))
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ)) :
    affineProfileTraceBank R rg Li Lk Ls index k o N entries (rg .dst) =
      affineProfileOutput Li Lk Ls index k o N entries ++ R (rg .dst) := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [affineProfileTraceBank, ih]
    simp [affineProfileCallBank, affineProfileOutput, hrg.eq_iff, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
