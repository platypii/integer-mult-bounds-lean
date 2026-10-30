module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeBitData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaChunkLayout

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host

/-- A full rectangular interchange is inverted by exchanging its field widths. -/
theorem swapList_involution {α : Type*} {P H G D B : ℕ} (fill : α) (xs : List α)
    (hlen : xs.length = BinaryAdjacentWidthInterchange.volume P H G D B) :
    swapList P D G H B fill (swapList P H G D B fill xs) = xs := by
  obtain ⟨x,hx⟩ := listArray_of_length xs hlen
  rw [←hx,←ofFn_transpose x fill,←ofFn_transpose (BinaryAdjacentWidthInterchange.transpose x) fill,
    BinaryAdjacentWidthInterchange.transpose_transpose]

theorem runReplicaChunkSwaps_append {α : Type*} (K : ℕ) (fill : α)
    (rs ss : List (ℕ × ℕ)) (xs : List α) :
    runReplicaChunkSwaps K fill (rs++ss) xs =
      runReplicaChunkSwaps K fill ss (runReplicaChunkSwaps K fill rs xs) := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem runReplicaChunkSwaps_length {α : Type*} (K : ℕ) (fill : α)
    (rs : List (ℕ × ℕ)) (V : ℕ) (hvolume : ∀ r ∈ rs, r.1*K*K*r.2 = V)
    (xs : List α) (hlen : xs.length = V) : (runReplicaChunkSwaps K fill rs xs).length = V := by
  induction rs generalizing xs with
  | nil => exact hlen
  | cons r rs ih =>
    apply ih (by intro s hs; exact hvolume s (by simp [hs]))
    simpa only [swapList,List.length_map,List.length_range,Nat.mul_one] using hvolume r (by simp)

/-- Reverse the schedule, not the payload. Every equal-width stage cancels
itself and all stages act on the same complete volume. -/
theorem runReplicaChunkSwaps_reverse_cancel {α : Type*} (K : ℕ) (fill : α)
    (rs : List (ℕ × ℕ)) (V : ℕ) (hvolume : ∀ r ∈ rs, r.1*K*K*r.2 = V)
    (xs : List α) (hlen : xs.length = V) :
    runReplicaChunkSwaps K fill rs.reverse (runReplicaChunkSwaps K fill rs xs) = xs := by
  induction rs generalizing xs with
  | nil => rfl
  | cons r rs ih =>
    have htail : ∀ s ∈ rs, s.1*K*K*s.2 = V := by intro s hs; exact hvolume s (by simp [hs])
    have hlen' : (swapList r.1 K 1 K r.2 fill xs).length = V := by
      simpa only [swapList,List.length_map,List.length_range,Nat.mul_one] using hvolume r (by simp)
    rw [List.reverse_cons,runReplicaChunkSwaps_append]
    change swapList r.1 K 1 K r.2 fill
      (runReplicaChunkSwaps K fill rs.reverse (runReplicaChunkSwaps K fill rs
        (swapList r.1 K 1 K r.2 fill xs))) = xs
    rw [ih htail _ hlen']
    apply swapList_involution
    simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using hlen.trans (hvolume r (by simp)).symm

/-- Completed key-major batches return to replica-major order using the same
stage shapes in reverse. This applies to arbitrary computed payload values. -/
theorem runReplicaChunkSwaps_inverse_words {α : Type*} (K W c : ℕ) (fill : α)
    (f : Fin (K^c) → Fin K → Fin W → α) :
    runReplicaChunkSwaps K fill (replicaChunkSwaps K W c).reverse (keyReplicaWords f) = replicaKeyWords f := by
  have hh := runReplicaChunkSwaps_reverse_cancel K fill (replicaChunkSwaps K W c) (K^c*K*W)
    (replicaChunkSwaps_stage_volume K W c) (replicaKeyWords f) (by simp [replicaKeyWords,Nat.mul_assoc])
  rwa [runReplicaChunkSwaps_words] at hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
