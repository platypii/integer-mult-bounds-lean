module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherBatch
public import IntegerMultBounds.MathlibTM2.Mult.ChirpWindows
public import IntegerMultBounds.MathlibTM2.Fast.ResampASem

/-! # Instantiate the shared sweep at chirp block centres -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Fast.ResampA

def chirpAdvancesFrom (s t m w j M : ℕ) : List ℕ :=
  (List.range M).map (fun i => chirpAdvance s t m (j + i) * w)

theorem chirpAdvancesFrom_succ (s t m w j M : ℕ) :
    chirpAdvancesFrom s t m w j (M + 1) =
      chirpAdvance s t m j * w :: chirpAdvancesFrom s t m w (j + 1) M := by
  simp only [chirpAdvancesFrom, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 2
  omega

theorem chirpDrop_advance (s t m w j : ℕ) (E : List (Fin (A + 4))) :
    (E.drop (chirpCenter s t m j * w)).drop (chirpAdvance s t m j * w) =
      E.drop (chirpCenter s t m (j + 1) * w) := by
  rw [List.drop_drop, ← Nat.add_mul, chirpCenter_add_advance]

/-- Every copy and advance in the actual symbol schedule fits the cyclic source. -/
theorem chirpGatherFits_from {s t m w j M : ℕ} (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (u : ZMod s → GaussianInt) (hvalid : ∀ i < M, (j + i) * m < t) :
    GatherFits ((3 * m + 1) * w)
      ((cstream A w (chirpExtended s m u)).drop (chirpCenter s t m j * w))
      (chirpAdvancesFrom s t m w j M) := by
  induction M generalizing j with
  | zero => trivial
  | succ M ih =>
    rw [chirpAdvancesFrom_succ]
    have hj : j * m < t := by simpa using hvalid 0 (by omega)
    have hc := chirpCenter_lt hs hj
    have hlen : (3 * m + 1) * w ≤
        ((cstream A w (chirpExtended s m u)).drop (chirpCenter s t m j * w)).length := by
      rw [List.length_drop, length_cstream, length_chirpExtended]
      have hb : chirpCenter s t m j + (3 * m + 1) ≤ s + 3 * m := by omega
      have hm := Nat.mul_le_mul_right w hb
      rw [Nat.add_mul] at hm
      omega
    refine ⟨hlen, ?_, ?_⟩
    · exact (Nat.mul_le_mul_right w ((chirpAdvance_le hst ht m j).trans (by omega))).trans hlen
    · rw [chirpDrop_advance]
      apply ih
      intro i hi
      have h := hvalid (i + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h

/-- The sweep's output is the concatenation of the correct windows, in block order. -/
theorem chirpGatherRows_from (s t m w j M : ℕ) (E : List (Fin (A + 4))) :
    gatherRows ((3 * m + 1) * w) (E.drop (chirpCenter s t m j * w))
        (chirpAdvancesFrom s t m w j M) =
      (List.range M).flatMap (fun i => (E.drop (chirpCenter s t m (j + i) * w)).take ((3 * m + 1) * w)) := by
  induction M generalizing j with
  | zero => rfl
  | succ M ih =>
    rw [chirpAdvancesFrom_succ, gatherRows, chirpDrop_advance, ih]
    simp only [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
    congr 1
    apply List.flatMap_congr
    intro i _
    rw [show j + 1 + i = j + i.succ by omega]

/-- The symbol windows retain the original low-bit-first coefficient words. -/
theorem chirpGatherRows (s t m w M : ℕ) (u : ZMod s → GaussianInt) :
    gatherRows ((3 * m + 1) * w) (cstream A w (chirpExtended s m u))
        (chirpAdvancesFrom s t m w 0 M) =
      (List.range M).flatMap (fun n => cstream A w (chirpWindow s t m n u)) := by
  have h := chirpGatherRows_from (A := A) s t m w 0 M (cstream A w (chirpExtended s m u))
  simpa only [chirpCenter_zero, Nat.zero_mul, List.drop_zero, Nat.zero_add,
    rsa_cstream_drop, rsa_cstream_take, chirpWindow] using h

/-- Advance symbols are charged once in total, even for heavily overlapping windows. -/
theorem chirpAdvances_sum (s t m w M : ℕ) :
    (chirpAdvancesFrom s t m w 0 M).sum = chirpCenter s t m M * w := by
  simp only [chirpAdvancesFrom, Nat.zero_add]
  rw [List.sum_map_mul_right, chirpAdvance_sum]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
