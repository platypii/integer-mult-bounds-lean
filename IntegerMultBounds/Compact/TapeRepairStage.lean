import IntegerMultBounds.Compact.RepairPipeline
import IntegerMultBounds.Machine.RepairStage

/-! The sorting and reinsertion half of the exceptional-address repair on
literal tapes. The list-level pipeline's extracted records, keyed by their
destination ranks in binary, are exactly the keyed records consumed by the
fixed eleven-tape stage machine; its output tape then holds the stream of the
ideal map. The cost is linear in the key width times the extracted volume plus
the full-stream volume. The flagging scan and the destination-rank arithmetic
that produce the keyed records are the remaining tape obligation. -/

namespace IntegerMultBounds.Compact

open Machine (blank putWord HoareTime)
open Machine.RepairStage (Keyed rawOf encTape stage raw sortedRaw)
open Machine.Partition (Record)
open Machine.RadixSort (sort sort_perm)

/-- The low `k` bits of a rank, least significant first. -/
def rankBits (k i : ℕ) : List Bool := List.ofFn (fun j : Fin k => Nat.testBit i j)

theorem keyAt_ofFn {k : ℕ} (f : Fin k → Bool) (j : ℕ) (hj : j < k) :
    Machine.KeySelect.keyAt j (List.ofFn f) = f ⟨j, hj⟩ := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [List.ofFn_succ]
    cases j with
    | zero => rfl
    | succ j => exact ih (fun i => f i.succ) j (by omega)

theorem keyAt_rankBits (k i j : ℕ) (hj : j < k) :
    Machine.KeySelect.keyAt j (rankBits k i) = Nat.testBit i j :=
  keyAt_ofFn _ j hj

section Pipeline

variable {α : Type*} [Fintype α] {M : ℕ} (e : α ≃ Fin M) (S T : Equiv.Perm α)
  (bad : α → Prop) [DecidablePred bad] (k : ℕ)

/-- A pipeline record with its destination rank as a key prefix. -/
def keyedOf (x : Fin M × Record) : Keyed := (rankBits k x.1, x.2)

/-- The extracted records of the list-level pipeline as keyed tape records. -/
def items (data : α → List Bool) : List Keyed := (extracted e S T bad data).map (keyedOf k)

omit [Fintype α] in
theorem items_keys (data : α → List Bool) : ∀ x ∈ items e S T bad k data, x.1.length = k := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  simp [keyedOf, rankBits]

theorem keyBit_keyedOf (x : Fin M × Record) (j : ℕ) (hj : j < k) :
    Machine.RepairStage.keyBit (keyedOf k x) j = keyBit x j :=
  keyAt_rankBits k x.1 j hj

omit [Fintype α] in
/-- The stage's replacement stream is the pipeline's sorted extracted stream. -/
theorem replacements_eq (data : α → List Bool) :
    Machine.RepairStage.replacements k (items e S T bad k data) =
      (sortedExtracted e S T bad k data).map Prod.snd := by
  unfold Machine.RepairStage.replacements Machine.RepairStage.sortedItems items sortedExtracted
  rw [Machine.RepairStage.sort_map (keyedOf k) keyBit Machine.RepairStage.keyBit k _
    (fun x _ j hj => keyBit_keyedOf k x j hj), List.map_map]
  rfl

omit [Fintype α] in
theorem holes_stream (d : α → List Bool) :
    Machine.Reinsert.holes (stream e bad d) = (badRanks e bad).length := by
  unfold Machine.Reinsert.holes stream badRanks
  rw [List.filter_map, List.length_map]
  rfl

omit [Fintype α] in
theorem items_count (data : α → List Bool) :
    (Machine.RepairStage.replacements k (items e S T bad k data)).length =
      Machine.Reinsert.holes (stream e bad (data ∘ S.symm)) := by
  rw [replacements_eq, List.length_map, sortedExtracted, (sort_perm _ _ _).length_eq, extracted,
    List.length_map, holes_stream]

variable (hT : ∀ x, bad (T x) ↔ bad x) (agree : ∀ x, ¬bad x → S x = T x)

omit [Fintype α] in
include hT agree in
/-- The tape stage on the pipeline's keyed extracted records and the flagged
actual output stream halts with the ideal stream on the output tape, within
`74k + 4` extracted volumes, one full-stream volume, and `k + 7`. -/
theorem tape_pipeline (hk : M ≤ 2 ^ k) (data : α → List Bool) :
    HoareTime Machine.RepairStage.program
      (fun v => v = stage k 0 (raw (items e S T bad k data)) 0 0 (fun _ => blank) 0
        (encTape (Machine.Partition.encode (stream e bad (data ∘ S.symm)))) 0 (fun _ => blank) 0)
      (fun v => v = stage k (Machine.TapeRadixSort.completed k (raw (items e S T bad k data)))
        (sortedRaw k (items e S T bad k data))
        (Machine.KeySelect.encode (sortedRaw k (items e S T bad k data))).length 0
        (encTape (Machine.Partition.encode ((sortedExtracted e S T bad k data).map Prod.snd)))
        (Machine.Partition.encode ((sortedExtracted e S T bad k data).map Prod.snd)).length
        (encTape (Machine.Partition.encode (stream e bad (data ∘ S.symm))))
        (Machine.Partition.encode (stream e bad (data ∘ S.symm))).length
        (encTape (Machine.Partition.encode (stream e bad (data ∘ T.symm))))
        (Machine.Partition.encode (stream e bad (data ∘ T.symm))).length)
      ((74 * k + 4) * (Machine.KeySelect.encode (raw (items e S T bad k data))).length +
        (Machine.Partition.encode (stream e bad (data ∘ S.symm))).length + k + 7) := by
  have h := Machine.RepairStage.stage_hoare k (items e S T bad k data) (items_keys e S T bad k data)
    (stream e bad (data ∘ S.symm)) (items_count e S T bad k data)
  have hcost := Machine.RepairStage.stage_cost_le k (items e S T bad k data)
    (items_keys e S T bad k data) (stream e bad (data ∘ S.symm))
  rw [replacements_eq] at h hcost
  have hp : Machine.Reinsert.fill (stream e bad (data ∘ S.symm))
      ((sortedExtracted e S T bad k data).map Prod.snd) = stream e bad (data ∘ T.symm) :=
    pipeline_exact e S T bad hT agree k hk data
  rw [hp] at h
  exact h.consequence (fun _ hv => hv) (fun _ hv => hv) hcost

/-- The extracted volume is at most the exceptional count times the key width,
flag, delimiter, and largest payload. -/
theorem items_volume_le (data : α → List Bool) (w : ℕ)
    (hw : ∀ x ∈ extracted e S T bad data, x.2.payload.length ≤ w) :
    (Machine.KeySelect.encode (raw (items e S T bad k data))).length ≤
      Nat.card {x // bad x} * (k + 2 + w) := by
  have h := Machine.RepairStage.raw_volume_le k (items e S T bad k data) (items_keys e S T bad k data)
    w (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hw y hy)
  rwa [items, List.length_map, extracted_length] at h

end Pipeline

end IntegerMultBounds.Compact
