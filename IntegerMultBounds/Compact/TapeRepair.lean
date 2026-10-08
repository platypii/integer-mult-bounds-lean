import IntegerMultBounds.Compact.TapeRepairStage
import IntegerMultBounds.Machine.RepairScan

/-! The complete exceptional-address repair on literal tapes (§5): the
flagging and extraction scan followed by the sort, strip and reinsert stage.
The scan's key routine is a parameter whose per-record contract is to read
the rank counter and write the membership flag and the destination rank
`e (T (S⁻¹ q))` in binary; the manuscript realizes it by reversing the eight
modular additions and the rank arithmetic. With that routine, the machine
carries the unflagged actual output stream to the ideal stream on the output
slot, within the key cost plus ten per record, three stream volumes, `74k + 5`
extracted volumes, `2k + 3` per exceptional address, and `k + 14`. -/

namespace IntegerMultBounds.Compact

open Machine.Partition (Record)
open Machine.RepairStage (Keyed raw encTape stage)
open IntegerMultBounds.Machine.RepairScan (flagged KeyContract program scanBank tail
  program_hoare program_cost_le finalStage encode_flagged_length)

section Lists

/-- Rewriting the flags of a list given by a function on positions. -/
theorem flagged_map {n : ℕ} (flag : ℕ → Bool) (j : ℕ) (g : Fin n → Record) :
    flagged flag j ((List.finRange n).map g) =
      (List.finRange n).map fun i : Fin n => ⟨flag (j + (i : ℕ)), (g i).payload⟩ := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, List.map_map, flagged, ih (j + 1),
      List.map_cons, List.map_map]
    simp only [Function.comp, Fin.val_zero, add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- Extracting the flagged records of a list given by a function on positions. -/
theorem items_map {n : ℕ} (flag : ℕ → Bool) (bits : ℕ → List Bool) (j : ℕ) (g : Fin n → Record) :
    Machine.RepairScan.items flag bits j ((List.finRange n).map g) =
      ((List.finRange n).filter fun i : Fin n => flag (j + (i : ℕ))).map
        fun i : Fin n => (bits (j + (i : ℕ)), ⟨true, (g i).payload⟩) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, List.map_map, Machine.RepairScan.items, ih (j + 1),
      List.filter_cons, List.filter_map]
    cases h : flag j <;>
      simp [h, List.map_map, Function.comp_def, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

end Lists

section Pipeline

variable {α : Type*} [Fintype α] {M : ℕ} (e : α ≃ Fin M) (S T : Equiv.Perm α)
  (bad : α → Prop) [DecidablePred bad] (k : ℕ)

/-- The actual output stream before flagging: every record unflagged. -/
def plain (d : α → List Bool) : List Record :=
  (List.finRange M).map fun i => ⟨false, d (e.symm i)⟩

/-- The scan's flag at rank `j`: membership of the address of rank `j`. -/
def rankFlag (j : ℕ) : Bool := if h : j < M then decide (bad (e.symm ⟨j, h⟩)) else false

/-- The scan's key at rank `j`: the destination rank in `k` bits. -/
def rankKey (j : ℕ) : List Bool := if h : j < M then rankBits k (destRank e S T ⟨j, h⟩) else []

omit [Fintype α] in
theorem plain_length (d : α → List Bool) : (plain e d).length = M := by
  simp [plain]

omit [Fintype α] in
theorem rankFlag_fin (i : Fin M) : rankFlag e bad i = decide (bad (e.symm i)) := by
  simp [rankFlag]

omit [Fintype α] in
theorem rankKey_fin (i : Fin M) : rankKey e S T k i = rankBits k (destRank e S T i) := by
  simp [rankKey]

omit [Fintype α] in
theorem rankKey_length (j : ℕ) (hj : j < M) : (rankKey e S T k j).length = k := by
  simp [rankKey, hj, rankBits]

omit [Fintype α] in
/-- The scan's flagged stream is the flagged actual stream. -/
theorem flagged_plain (d : α → List Bool) :
    flagged (rankFlag e bad) 0 (plain e d) = stream e bad d := by
  rw [plain, flagged_map, stream]
  refine List.map_congr_left fun i _ => ?_
  rw [zero_add, rankFlag_fin]

omit [Fintype α] in
/-- The scan's extracted records are the pipeline's keyed extracted records. -/
theorem items_plain (data : α → List Bool) :
    Machine.RepairScan.items (rankFlag e bad) (rankKey e S T k) 0 (plain e (data ∘ S.symm)) =
      items e S T bad k data := by
  rw [plain, items_map, items, extracted, badRanks, List.map_map]
  rw [List.filter_congr (p := fun i : Fin M => rankFlag e bad (0 + i))
    (q := fun i => decide (bad (e.symm i))) (l := List.finRange M)
    (fun i _ => by rw [zero_add, rankFlag_fin])]
  refine List.map_congr_left fun i _ => ?_
  simp [keyedOf, rankKey_fin, Function.comp]

variable (hT : ∀ x, bad (T x) ↔ bad x) (agree : ∀ x, ¬bad x → S x = T x)

/-- The scan-and-stage machine over the pipeline's records. -/
abbrev repairRecords (data : α → List Bool) : List Record := plain e (data ∘ S.symm)

include hT agree in
/-- The complete repair machine on the unflagged actual stream halts with the
ideal stream on the output slot, given a key routine meeting the per-record
contract, within the written bound. -/
theorem tape_repair (hk : M ≤ 2 ^ k) (data : α → List Bool) (c s : ℕ) {qK : ℕ}
    (K : Machine.Program (14 + s) qK 1) (cK : ℕ) (scratch : Machine.Tapes s 1)
    (hK : KeyContract k (repairRecords e S data) (rankFlag e bad) (rankKey e S T k) c s K
      cK scratch) :
    Machine.HoareTime (program s K)
      (fun v => v = (scanBank k (repairRecords e S data) (rankFlag e bad)
        (rankKey e S T k) c 0 [] 0).append scratch)
      (fun v => v = ((stage k (Machine.TapeRadixSort.completed k (raw (items e S T bad k data)))
        (Machine.RepairStage.sortedRaw k (items e S T bad k data))
        (Machine.KeySelect.encode (Machine.RepairStage.sortedRaw k (items e S T bad k data))).length 0
        (encTape (Machine.Partition.encode ((sortedExtracted e S T bad k data).map Prod.snd)))
        (Machine.Partition.encode ((sortedExtracted e S T bad k data).map Prod.snd)).length
        (encTape (Machine.Partition.encode (stream e bad (data ∘ S.symm))))
        (Machine.Partition.encode (stream e bad (data ∘ S.symm))).length
        (encTape (Machine.Partition.encode (stream e bad (data ∘ T.symm))))
        (Machine.Partition.encode (stream e bad (data ∘ T.symm))).length).append
          (tail (repairRecords e S data) c M)).append scratch)
      (M * (cK + 10) + 3 * (Machine.Partition.encode (stream e bad (data ∘ S.symm))).length +
        (74 * k + 5) * (Machine.KeySelect.encode (raw (items e S T bad k data))).length +
        (2 * k + 3) * Nat.card {x // bad x} + k + 14) := by
  have hbits : ∀ j < (repairRecords e S data).length, (rankKey e S T k j).length = k :=
    fun j hj => rankKey_length e S T k j (by rwa [plain_length] at hj)
  have h := program_hoare k (repairRecords e S data) (rankFlag e bad) (rankKey e S T k)
    c s K cK scratch hK hbits
  have hcost := program_cost_le k (repairRecords e S data) (rankFlag e bad)
    (rankKey e S T k) c cK hbits
  rw [items_plain, flagged_plain] at h hcost
  have hp : Machine.Reinsert.fill (stream e bad (data ∘ S.symm))
      ((sortedExtracted e S T bad k data).map Prod.snd) = stream e bad (data ∘ T.symm) :=
    pipeline_exact e S T bad hT agree k hk data
  rw [finalStage, replacements_eq, hp] at h
  have hV : (Machine.DropFlag.encode (repairRecords e S data)).length =
      (Machine.Partition.encode (stream e bad (data ∘ S.symm))).length := by
    rw [← encode_flagged_length (rankFlag e bad) 0, flagged_plain,
      Machine.DropFlag.encode_partition, List.length_map]
  rw [hV, holes_stream, badRanks_length, plain_length] at hcost
  rw [plain_length] at h
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) hcost

end Pipeline

end IntegerMultBounds.Compact
