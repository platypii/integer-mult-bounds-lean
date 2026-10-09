import IntegerMultBounds.Machine.ArbitraryWidthPieceLoop
import IntegerMultBounds.Machine.ArbitrarySliceRepeat

/-! The runtime base-digit driver has an exact semantic prefix invariant.
Its cumulative offset plus the unprocessed quotient contribution is the full
width. Consecutive counted slice calls realize precisely the prefix schedule. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPiecePrefix
noncomputable section
open Networks
open ArbitraryWidthPieceLoop (remaining digit count)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

def blocks (m N i : ℕ) : List ℕ :=
  (List.range i).flatMap (fun j => List.replicate (digit m N j) (m^j))

def offset (m N i : ℕ) := (blocks m N i).sum

theorem blocks_zero (m N : ℕ) : blocks m N 0 = [] := rfl

theorem blocks_succ (m N i : ℕ) :
    blocks m N (i+1) = blocks m N i ++ List.replicate (digit m N i) (m^i) := by
  simp [blocks,List.range_succ,List.flatMap_append]

theorem offset_zero (m N : ℕ) : offset m N 0 = 0 := rfl

theorem offset_succ (m N i : ℕ) :
    offset m N (i+1) = offset m N i+digit m N i*m^i := by
  simp only [offset,blocks_succ,List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

theorem digit_remaining (m N i : ℕ) :
    digit m N i+remaining m N (i+1)*m = remaining m N i := by
  rw [← ArbitraryWidthPieceLoop.remaining_succ]
  simpa only [digit,Nat.mul_comm] using Nat.mod_add_div (remaining m N i) m

/-- Exact telescoping identity, including N=0 and every digit prefix. -/
theorem balance (m N i : ℕ) : offset m N i+remaining m N i*m^i = N := by
  induction i with
  | zero => simp [offset,blocks,remaining]
  | succ i ih =>
    calc
      _ = offset m N i+(digit m N i+remaining m N (i+1)*m)*m^i := by
        rw [offset_succ,pow_succ]
        ring
      _ = N := by rw [digit_remaining]; exact ih

theorem prefix_fit (m N i : ℕ) : offset m N i ≤ N := by
  have h := balance m N i
  omega

theorem step_fit (m N i : ℕ) : offset m N i+digit m N i*m^i ≤ N := by
  rw [← offset_succ]
  exact prefix_fit m N (i+1)

theorem offset_count (m N : ℕ) (hm : 2 ≤ m) : offset m N (count m N) = N := by
  have h := balance m N (count m N)
  rw [ArbitraryWidthPieceLoop.exit m N hm,zero_mul,add_zero] at h
  exact h

theorem sum_count (m N : ℕ) (hm : 2 ≤ m) : (blocks m N (count m N)).sum = N :=
  offset_count m N hm

theorem zero_blocks (m i : ℕ) : blocks m 0 i = [] := by
  simp [blocks,digit,remaining]

theorem zero_offset (m i : ℕ) : offset m 0 i = 0 := by rw [offset,zero_blocks]; rfl

theorem blocks_partition (m N k : ℕ) :
    blocks m N (k+1) = ArbitraryWidthPieces.widths m N k := by
  simp [blocks,ArbitraryWidthPieces.widths,ArbitraryWidthPieces.depths,
    digit,remaining,List.map_flatMap]

theorem selected_power_le (m N i : ℕ) (hm : 2 ≤ m) (hi : i < count m N) : m^i ≤ N := by
  exact (Nat.div_pos_iff.mp (ArbitraryWidthPieceLoop.before m N i hm hi)).2

theorem selected_depth (m N i k : ℕ) (hm : 2 ≤ m)
    (hi : i < count m N) (hN : N < m^(k+1)) : i ≤ k := by
  have hr := ArbitraryWidthPieceLoop.before m N i hm hi
  have hp : m^i ≤ N := (Nat.div_pos_iff).mp hr |>.2
  by_contra h
  have hki : k+1 ≤ i := by omega
  have hpow := Nat.pow_le_pow_right (by omega : 0 < m) hki
  omega

/-- All positive repeated slices at a selected level fit individually. -/
theorem repetition_fit (m N i j : ℕ) (hj : j ≤ digit m N i) :
    offset m N i+j*m^i ≤ N := by
  have h := step_fit m N i
  have hmul := Nat.mul_le_mul_right (m^i) hj
  omega

def images {α : Type*} (m N : ℕ) (v : Descriptor) (i : ℕ) (hN : N ≤ v.width)
    (x : Fin (volume prime v) → α) : Fin (volume prime v) → α :=
  ArbitraryWidthSchedule.run (blocks m N i) 0
    (by simpa only [zero_add,offset] using (prefix_fit m N i).trans hN) x

theorem images_zero {α : Type*} (m N : ℕ) (v : Descriptor) (hN : N ≤ v.width)
    (x : Fin (volume prime v) → α) : images m N v 0 hN x = x := rfl

private theorem run_congr {α : Type*} {v : Descriptor} (ws us : List ℕ) (t u : ℕ)
    (he : ws = us) (ht : t = u) (hw : t+ws.sum ≤ v.width) (hu : u+us.sum ≤ v.width)
    (x : Fin (volume prime v) → α) :
    ArbitraryWidthSchedule.run ws t hw x = ArbitraryWidthSchedule.run us u hu x := by
  subst us
  subst u
  rfl

theorem images_succ (m N : ℕ) (v : Descriptor) (i : ℕ) (hN : N ≤ v.width)
    (x : Fin (volume prime v) → ZMod 2) :
    images m N v (i+1) hN x =
      ArbitrarySliceRepeat.images v (offset m N i) (m^i) (digit m N i)
        ((step_fit m N i).trans hN) (images m N v i hN x) := by
  have hf : 0+(blocks m N i ++ List.replicate (digit m N i) (m^i)).sum ≤ v.width := by
    simpa only [List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,zero_add,offset]
      using (step_fit m N i).trans hN
  have h := ArbitrarySliceRepeat.run_append (v := v) (blocks m N i)
    (List.replicate (digit m N i) (m^i)) 0 hf x
  have he := run_congr (v := v) (blocks m N (i+1))
    (blocks m N i ++ List.replicate (digit m N i) (m^i)) 0 0 (blocks_succ m N i) rfl
    (by simpa only [zero_add,offset] using (prefix_fit m N (i+1)).trans hN) hf x
  apply he.trans (h.trans ?_)
  exact run_congr _ _ _ _ rfl (by simp [offset]) _ _ _

theorem images_count {α : Type*} (m N : ℕ) (v : Descriptor) (hm : 2 ≤ m)
    (hN : N = v.width) (x : Fin (volume prime v) → α) :
    images m N v (count m N) hN.le x = Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x := by
  exact ArbitraryWidthSchedule.run_full (blocks m N (count m N)) ((sum_count m N hm).trans hN) x

end
end IntegerMultBounds.Machine.ArbitraryWidthPiecePrefix
