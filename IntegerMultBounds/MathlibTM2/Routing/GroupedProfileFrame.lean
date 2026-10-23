module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileLoop

/-! Closed tape contents after grouped profile traversal: complete archived input,
generated coordinates, final index and unchanged spectator tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def groupedProfileOutput (Li Lg Lk Ls index g k b N : ℕ) : List (Bool × ℕ) → List (Fin (A + 4))
  | [] => []
  | (enabled, q) :: rest => groupedProfileOutput Li Lg Lk Ls (index + 1) g k b N rest ++
      (binSyms (Li + Lk) (N - 1 - (index / g * k + (index % g + b))) ++ separator ::
        (binSyms Ls (if enabled then q + 1 else 0) ++ [separator]))

theorem groupedProfileTrace_keep (R : Fin T → List (Fin (A + 4)))
    (rg : GroupedProfileReg → Fin T) (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ))
    (j : Fin T) (hs : j ≠ rg .src) (ha : j ≠ rg .archive) (hc : j ≠ rg (.coordinate (.arithmetic .index))) (hd : j ≠ rg (.coordinate .dst)) :
    groupedProfileTraceBank R rg Li Lg Lk Ls index g k b N entries j = R j := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [groupedProfileTraceBank, ih]
    simp [groupedProfileCallBank, hs, ha, hc, hd]

theorem groupedProfileTrace_src (R : Fin T → List (Fin (A + 4)))
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ))
    (hsrc : R (rg .src) = affineProfileFrames Ls entries) :
    groupedProfileTraceBank R rg Li Lg Lk Ls index g k b N entries (rg .src) = [] := by
  induction entries generalizing R index with
  | nil => exact hsrc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    apply ih
    simp [groupedProfileCallBank, hrg.eq_iff]

theorem groupedProfileTrace_archive (R : Fin T → List (Fin (A + 4)))
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ)) :
    groupedProfileTraceBank R rg Li Lg Lk Ls index g k b N entries (rg .archive) =
      (affineProfileFrames Ls entries).reverse ++ R (rg .archive) := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [groupedProfileTraceBank, ih]
    simp [groupedProfileCallBank, affineProfileFrames, hrg.eq_iff, List.reverse_append, List.append_assoc]

theorem groupedProfileTrace_index (R : Fin T → List (Fin (A + 4)))
    (rg : GroupedProfileReg → Fin T) (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ))
    (hc : R (rg (.coordinate (.arithmetic .index))) = binSyms Li index) :
    groupedProfileTraceBank R rg Li Lg Lk Ls index g k b N entries (rg (.coordinate (.arithmetic .index))) =
      binSyms Li (index + entries.length) := by
  induction entries generalizing R index with
  | nil => exact hc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    have hh := ih
      (groupedProfileCallBank R rg Li Lg Lk Ls index g k b N q x (affineProfileFrames Ls rest))
      (index + 1) (by simp [groupedProfileCallBank])
    simpa only [groupedProfileTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

theorem groupedProfileTrace_output (R : Fin T → List (Fin (A + 4)))
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ)) :
    groupedProfileTraceBank R rg Li Lg Lk Ls index g k b N entries (rg (.coordinate .dst)) =
      groupedProfileOutput Li Lg Lk Ls index g k b N entries ++ R (rg (.coordinate .dst)) := by
  induction entries generalizing R index with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [groupedProfileTraceBank, ih]
    simp [groupedProfileCallBank, groupedProfileOutput, hrg.eq_iff, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
