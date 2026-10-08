import IntegerMultBounds.Compact.KeyValue
import IntegerMultBounds.Machine.PlacementBank

/-! The key routine placed into the repair scan's bank meets the scan's key
contract for the concrete early instance: at every rank it writes the
membership flag and the destination rank's bits on the key tape and leaves
every other tape, including its own scratch frame, as it was. With it the
complete repair machine of `TapeRepair` runs with a concrete key routine. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Machine
open IntegerMultBounds.Counter (value)

section CounterTape

/-- The counter's separator background in the widened alphabet. -/
def ctrBg : ℤ → Fin 5 := fun j => PartitionMarked.encoding.encode (GrowingCounter.emptyTape j)

theorem putBits_eq (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    putBits f p bs = putWord f p (bs.map bitSymbol) := by
  induction bs generalizing f p with
  | nil => rfl
  | cons b bs ih => rw [putBits_cons, List.map_cons, putWord_cons, ih]

theorem encode_putWord (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4)) :
    (fun j => PartitionMarked.encoding.encode (putWord f p xs j)) =
      putWord (fun j => PartitionMarked.encoding.encode (f j)) p (xs.map PartitionMarked.encoding.encode) := by
  induction xs generalizing f p with
  | nil => rfl
  | cons x xs ih =>
    rw [putWord_cons, List.map_cons, putWord_cons, ih (Function.update f p x) (p + 1)]
    congr 1
    funext j
    by_cases hj : j = p
    · subst hj; simp
    · simp [hj]

/-- The scan's counter tape is the counter word placed over the separator. -/
theorem ctrTape_eq (bs : List Bool) : RepairScan.ctrTape bs = putWord ctrBg 1 (bs.map bitSymbol) := by
  unfold RepairScan.ctrTape ctrBg
  rw [putBits_eq, encode_putWord, List.map_map]
  congr 1

end CounterTape

section Placement

/-- The key routine's scratch frame: the two address words and the eleven
work tapes blank, the control and the three constants as words. -/
def keyScratch (Zb C1 C2 C3 : List Bool) (z c1 c2 c3 : ℤ → Fin 5)
    (pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt : ℤ) : Tapes 15 1 :=
  ⟨fun i => if i = 0 then pV else if i = 1 then pW else if i = 2 then pZ else if i = 3 then pC1
    else if i = 4 then pC2 else if i = 5 then pC3 else if i = 6 then pW1 else if i = 7 then pT
    else if i = 8 then pV1 else if i = 9 then pWr else if i = 10 then pO else if i = 11 then pVr
    else if i = 12 then pOc else if i = 13 then pF else pVt,
   fun i => if i = 0 then (fun _ => blank) else if i = 1 then (fun _ => blank)
    else if i = 2 then putWord z pZ (Zb.map bitSymbol) else if i = 3 then putWord c1 pC1 (C1.map bitSymbol)
    else if i = 4 then putWord c2 pC2 (C2.map bitSymbol) else if i = 5 then putWord c3 pC3 (C3.map bitSymbol)
    else (fun _ => blank)⟩

/-- The routine's tapes in the scan bank: key at twelve, counter at
thirteen, scratch from fourteen. -/
def slot : Fin 17 → Fin (14 + 15) :=
  fun i => if i = 0 then ⟨12, by omega⟩ else if i = 1 then ⟨13, by omega⟩
    else ⟨12 + i.val, by have := i.isLt; omega⟩

theorem slot_injective : Function.Injective slot := by
  intro i j h
  simp only [slot] at h
  split_ifs at h <;> simp only [Fin.ext_iff] at h ⊢ <;> omega

/-- The key routine placed into the scan bank. -/
noncomputable def placedKey (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (Zb : List Bool) :=
  Placement.placed (KeyRoutine.program q b Zb.length hb hbq1)
    (InjectivePlacement.placement (u := 12) slot slot_injective rfl)

/-- The placed key routine meets the scan's key contract. -/
theorem key_contract (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q) (hq1 : b + 3 ≤ q)
    (Zb C1 C2 C3 : List Bool) (z c1 c2 c3 : ℤ → Fin 5)
    (pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt : ℤ)
    (hC1 : C1.length = q - 1) (hC2 : C2.length = q - 1) (hC3 : C3.length = b)
    (hC1v : value C1 = 2 ^ (b + 1)) (hC2v : value C2 + 2 ^ (b + 1) + 1 = 2 ^ (q - 1))
    (hC3v : value C3 + 2 = 2 ^ b) (hz : z (pZ - 1) = blank) (hc1 : c1 (pC1 - 1) = blank)
    (hc2 : c2 (pC2 - 1) = blank) (hc3 : c3 (pC3 - 1) = blank)
    (c : ℕ) (hc : Zb.length * q + Zb.length * b ≤ c) (hcM : Mi q b Zb ≤ 2 ^ c)
    (records : List Partition.Record) (hrec : records.length ≤ Mi q b Zb) :
    RepairScan.KeyContract (Zb.length * q + Zb.length * b) records
      (rankFlag (rankEquiv q b Zb) (badSet q b Zb))
      (rankKey (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (Zb.length * q + Zb.length * b)) c 15
      (placedKey q b hb hbq1 Zb) (KeyRoutine.cost q b Zb.length hb hbq1)
      (keyScratch Zb C1 C2 C3 z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt) := by
  intro j hj
  have hjM : j < Mi q b Zb := by omega
  have hcs : value (RepairScan.counter c j) = j := counter_value c j (by omega)
  have hcsl : Zb.length * q + Zb.length * b ≤ (RepairScan.counter c j).length := by
    rw [RepairScan.counter_length]; exact hc
  have hflag := flag_bridge q b hq1 Zb (RepairScan.counter c j) C1 C2 C3 hC1 hC2 hC3 hC1v hC2v hC3v
    j hjM hcs hcsl
  have hbits := (bits_bridge q b hb hbq1 Zb (RepairScan.counter c j) (by omega) j hjM hcs hcsl).symm
  have hroutine := KeyRoutine.routine_hoare q b hb hbq1 hq1 (RepairScan.counter c j) Zb C1 C2 C3 ctrBg
    z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt hcsl hC1 hC2 hC3 hz hc1 hc2 hc3
  refine InjectivePlacement.hoare_exact (u := 12) hroutine slot slot_injective rfl _ _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · fin_cases x <;> rfl
    · fin_cases x <;> first | rfl | exact ctrTape_eq _
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · fin_cases x
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_head_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨0, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨1, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨2, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨3, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨4, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨5, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨6, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨7, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨8, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨9, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨10, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨11, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨12, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨13, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨14, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨15, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
      · change (Placement.replace _ _ _).head (slot ⟨16, by omega⟩) = _
        rw [InjectivePlacement.replace_head_slot]; rfl
    · fin_cases x
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · rw [InjectivePlacement.replace_tape_other (u := 12) slot slot_injective rfl _ _ _ (by decide)]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨0, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]
        change FlagCopy.keyTape (FlagCopy.keyWord _ _) = FlagCopy.keyTape (FlagCopy.keyWord _ _)
        rw [hflag, hbits]
      · change (Placement.replace _ _ _).tape (slot ⟨1, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]
        exact (ctrTape_eq _).symm
      · change (Placement.replace _ _ _).tape (slot ⟨2, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨3, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨4, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨5, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨6, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨7, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨8, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨9, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨10, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨11, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨12, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨13, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨14, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨15, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl
      · change (Placement.replace _ _ _).tape (slot ⟨16, by omega⟩) = _
        rw [InjectivePlacement.replace_tape_slot]; rfl

end Placement

section Repair

variable (q b : ℕ) (hb : 1 ≤ b) (hbq1 : b + 1 ≤ q)
  (Zb C1 C2 C3 : List Bool) (z c1 c2 c3 : ℤ → Fin 5)
  (pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt : ℤ)

theorem ideal_preserves (y : EarlyAddress (Bi b) (Li q) (controls Zb).length) :
    badSet q b Zb (Tperm q b Zb y) ↔ badSet q b Zb y :=
  not_congr (earlyIdeal_preserves_good (Bi b) (Li q) (Li_pos q) (controls Zb) (controls_bits Zb) y)

theorem program_agrees (y : EarlyAddress (Bi b) (Li q) (controls Zb).length) (hy : ¬ badSet q b Zb y) :
    Sperm q b Zb y = Tperm q b Zb y :=
  early_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q) (controls Zb) (controls_bits Zb) y
    (not_not.mp hy)

theorem Mi_le (hq : 1 ≤ q) : Mi q b Zb ≤ 2 ^ (Zb.length * q + Zb.length * b) := by
  rw [Mi_eq q b Zb hq, pow_add, mul_comm]

/-- The complete repair machine of the compact-control instance: the scan
with the placed key routine, the sort, strip and reinsert stage, carrying the
unflagged actual stream to the ideal stream on the output slot within the
pipeline's bound with the key routine's cost per record. -/
theorem repair_instance (hq1 : b + 3 ≤ q) (hC1 : C1.length = q - 1) (hC2 : C2.length = q - 1)
    (hC3 : C3.length = b)
    (hC1v : value C1 = 2 ^ (b + 1)) (hC2v : value C2 + 2 ^ (b + 1) + 1 = 2 ^ (q - 1))
    (hC3v : value C3 + 2 = 2 ^ b) (hz : z (pZ - 1) = blank) (hc1 : c1 (pC1 - 1) = blank)
    (hc2 : c2 (pC2 - 1) = blank) (hc3 : c3 (pC3 - 1) = blank)
    (c : ℕ) (hc : Zb.length * q + Zb.length * b ≤ c) (hcM : Mi q b Zb ≤ 2 ^ c)
    (data : EarlyAddress (Bi b) (Li q) (controls Zb).length → List Bool) :
    HoareTime (RepairScan.program 15 (placedKey q b hb hbq1 Zb))
      (fun v => v = (RepairScan.scanBank (Zb.length * q + Zb.length * b)
        (repairRecords (rankEquiv q b Zb) (Sperm q b Zb) data)
        (rankFlag (rankEquiv q b Zb) (badSet q b Zb))
        (rankKey (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (Zb.length * q + Zb.length * b)) c 0 [] 0).append
        (keyScratch Zb C1 C2 C3 z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt))
      (fun v => v = ((RepairStage.stage (Zb.length * q + Zb.length * b)
        (TapeRadixSort.completed (Zb.length * q + Zb.length * b)
          (RepairStage.raw (items (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (badSet q b Zb)
            (Zb.length * q + Zb.length * b) data)))
        (RepairStage.sortedRaw (Zb.length * q + Zb.length * b)
          (items (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (badSet q b Zb)
            (Zb.length * q + Zb.length * b) data))
        (KeySelect.encode (RepairStage.sortedRaw (Zb.length * q + Zb.length * b)
          (items (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (badSet q b Zb)
            (Zb.length * q + Zb.length * b) data))).length 0
        (RepairStage.encTape (Partition.encode ((sortedExtracted (rankEquiv q b Zb) (Sperm q b Zb)
          (Tperm q b Zb) (badSet q b Zb) (Zb.length * q + Zb.length * b) data).map Prod.snd)))
        (Partition.encode ((sortedExtracted (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb)
          (badSet q b Zb) (Zb.length * q + Zb.length * b) data).map Prod.snd)).length
        (RepairStage.encTape (Partition.encode (stream (rankEquiv q b Zb) (badSet q b Zb)
          (data ∘ (Sperm q b Zb).symm))))
        (Partition.encode (stream (rankEquiv q b Zb) (badSet q b Zb) (data ∘ (Sperm q b Zb).symm))).length
        (RepairStage.encTape (Partition.encode (stream (rankEquiv q b Zb) (badSet q b Zb)
          (data ∘ (Tperm q b Zb).symm))))
        (Partition.encode (stream (rankEquiv q b Zb) (badSet q b Zb) (data ∘ (Tperm q b Zb).symm))).length).append
          (RepairScan.tail (repairRecords (rankEquiv q b Zb) (Sperm q b Zb) data) c (Mi q b Zb))).append
        (keyScratch Zb C1 C2 C3 z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt))
      (Mi q b Zb * (KeyRoutine.cost q b Zb.length hb hbq1 + 10) +
        3 * (Partition.encode (stream (rankEquiv q b Zb) (badSet q b Zb) (data ∘ (Sperm q b Zb).symm))).length +
        (74 * (Zb.length * q + Zb.length * b) + 5) * (KeySelect.encode (RepairStage.raw
          (items (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (badSet q b Zb)
            (Zb.length * q + Zb.length * b) data))).length +
        (2 * (Zb.length * q + Zb.length * b) + 3) * Nat.card {x // badSet q b Zb x} +
        (Zb.length * q + Zb.length * b) + 14) :=
  tape_repair (rankEquiv q b Zb) (Sperm q b Zb) (Tperm q b Zb) (badSet q b Zb)
    (Zb.length * q + Zb.length * b) (ideal_preserves q b Zb) (program_agrees q b Zb)
    (Mi_le q b Zb (by omega)) data c 15
    (placedKey q b hb hbq1 Zb) (KeyRoutine.cost q b Zb.length hb hbq1)
    (keyScratch Zb C1 C2 C3 z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt)
    (key_contract q b hb hbq1 hq1 Zb C1 C2 C3 z c1 c2 c3 pZ pC1 pC2 pC3 pV pW pW1 pT pV1 pWr pO pVr pOc pF pVt
      hC1 hC2 hC3 hC1v hC2v hC3v hz hc1 hc2 hc3 c hc hcM _ (le_of_eq (plain_length (rankEquiv q b Zb) _)))

end Repair

end IntegerMultBounds.Compact.PowerTwo
