import IntegerMultBounds.Networks.SharedPointLift
import Mathlib.Data.Nat.Pairing

/-! Compact duplicate witnesses use small common-vertex and covered-vertex
masks. Inserting the common point is computed with shifts and masks; soundness
connects those operations to the semantic lifted triple supports. -/

namespace IntegerMultBounds.Networks.SharedPointWitnessCheck

open MaskDAG MaskSignature

variable {n width : ℕ}

/-- Insert one occupied bit at the deleted vertex, shifting higher local bits. -/
def bitLift (c : Fin (n+1)) (mask : BitVec n) : BitVec (n+1) :=
  (mask.setWidth (n+1) &&& (BitVec.allOnes c.val).setWidth (n+1)) |||
    ((mask.setWidth (n+1) >>> c.val) <<< (c.val+1)) ||| MaskDAG.singleton c

private theorem bitLift_get (c : Fin (n+1)) (mask : BitVec n) (i : Fin (n+1)) :
    (bitLift c mask).getLsbD i.val =
      if i.val < c.val then mask.getLsbD i.val
      else if i.val = c.val then true else mask.getLsbD (i.val-1) := by
  have hi := i.isLt
  have hc := c.isLt
  simp only [bitLift, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    MaskDAG.singleton, BitVec.getLsbD_one]
  by_cases hlt : i.val < c.val
  · have hnot : ¬ c.val + 1 ≤ i.val := by omega
    have hnot' : ¬ c.val ≤ i.val := by omega
    simp [hi, hlt, Fin.lt_def, -Fin.val_fin_lt]
    omega
  · by_cases he : i.val = c.val
    · simp [he]
      omega
    · have hle : c.val+1 ≤ i.val := by omega
      have hle' : c.val ≤ i.val := by omega
      have hsub : c.val + (i.val - (c.val+1)) = i.val-1 := by omega
      have hbound : i.val-1 < n+1 := by omega
      have hnz : i.val-c.val ≠ 0 := by omega
      simp [hi, hlt, he, hsub, hbound, hnz, Fin.lt_def, -Fin.val_fin_lt]
      omega

/-- Numeric insertion implements the actual order-preserving deleted-point map. -/
theorem decode_bitLift (c : Fin (n+1)) (mask : BitVec n) :
    decode (bitLift c mask) = insert c ((decode mask).image c.succAbove) := by
  ext i
  by_cases he : i = c
  · subst i
    simp [mem_decode, bitLift_get]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq he
    have hinj : Function.Injective c.succAbove := Fin.succAbove_right_injective
    rw [Finset.mem_insert, Finset.mem_image]
    have hne := Fin.succAbove_ne c j
    simp only [hne, false_or]
    have hex : (∃ a ∈ decode mask, c.succAbove a = c.succAbove j) ↔ j ∈ decode mask := by
      constructor
      · rintro ⟨a, ha, he⟩
        exact hinj he ▸ ha
      · exact fun hj => ⟨j, hj, rfl⟩
    rw [hex, mem_decode, mem_decode, bitLift_get]
    unfold Fin.succAbove
    split
    next h =>
      have hjc : j.val < c.val := h
      simp only [Fin.val_castSucc, ite_eq_left hjc]
    next h =>
      have hjc : c.val ≤ j.val := Nat.le_of_not_gt h
      have hlt : ¬ j.val+1 < c.val := by omega
      have hne : ¬ j.val+1 = c.val := by omega
      simp only [Fin.val_succ, ite_eq_right hlt, ite_eq_right hne, Nat.add_sub_cancel]

abbrev Witness (n : ℕ) := (Fin (n+1) × ℕ) × (Fin (n+1) × ℕ)

/-- Pairing gives a total numeric sort key without trusting node-index bounds. -/
def key (row : Witness n) : ℕ :=
  Nat.pair row.1.1.val (Nat.pair row.1.2 (Nat.pair row.2.1.val row.2.2))

/-- Check owner ordering, actual addition membership, and both lifted signatures. -/
def checkRow (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (row : Witness n) : Bool :=
  decide (row.1.1 < row.2.1 ∧ isAddition row.1.2 = true ∧ isAddition row.2.2 = true) &&
    match coreBank row.1.2, coreBank row.2.2, unionBank row.1.2, unionBank row.2.2 with
    | some lc, some rc, some lu, some ru =>
      decide (lc ≠ 0 ∧ bitLift row.1.1 lc = bitLift row.2.1 rc ∧
        bitLift row.1.1 lu = bitLift row.2.1 ru)
    | _, _, _, _ => false

/-- Every eligible node has a nonempty support and exact bank summaries. -/
def BankCorrect (payload : Fin width → Finset (Fin n)) (support : ℕ → Finset (Fin width))
    (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n)) : Prop :=
  ∀ i, isAddition i = true → (support i).Nonempty ∧
    ∀ c u, coreBank i = some c → unionBank i = some u →
      decode c = core payload (support i) ∧ decode u = union payload (support i)

/-- Each accepted compact witness denotes genuinely equal lifted supports. -/
theorem checkRow_sound (payload : Fin width → Finset (Fin n))
    (hpair : ∀ i, (payload i).card = 2) (support : ℕ → Finset (Fin width))
    (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (hb : BankCorrect payload support isAddition coreBank unionBank) (row : Witness n)
    (hc : checkRow isAddition coreBank unionBank row = true) :
    row.1.1 < row.2.1 ∧ isAddition row.1.2 = true ∧ isAddition row.2.2 = true ∧
      SharedPointLift.lift payload hpair row.1.1 (support row.1.2) =
        SharedPointLift.lift payload hpair row.2.1 (support row.2.2) := by
  obtain ⟨ho, hc⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨horder, ha, hb'⟩ : row.1.1 < row.2.1 ∧ isAddition row.1.2 = true ∧
      isAddition row.2.2 = true := of_decide_eq_true ho
  refine ⟨horder, ha, hb', ?_⟩
  obtain ⟨hneL, hL⟩ := hb row.1.2 ha
  obtain ⟨hneR, hR⟩ := hb row.2.2 hb'
  cases hcl : coreBank row.1.2 with
  | none => simp [hcl] at hc
  | some lc =>
    cases hcr : coreBank row.2.2 with
    | none => simp [hcl, hcr] at hc
    | some rc =>
      cases hul : unionBank row.1.2 with
      | none => simp [hcl, hcr, hul] at hc
      | some lu =>
        cases hur : unionBank row.2.2 with
        | none => simp [hcl, hcr, hul, hur] at hc
        | some ru =>
          obtain ⟨hnz, hec, heu⟩ : lc ≠ 0 ∧ bitLift row.1.1 lc = bitLift row.2.1 rc ∧
              bitLift row.1.1 lu = bitLift row.2.1 ru := by simpa [hcl, hcr, hul, hur] using hc
          obtain ⟨hLc, hLu⟩ := hL lc lu hcl hul
          obtain ⟨hRc, hRu⟩ := hR rc ru hcr hur
          have hcore : (decode lc).Nonempty := by
            apply Finset.nonempty_iff_ne_empty.mpr
            intro he
            exact hnz (decode_injective (he.trans decode_zero.symm))
          have hec' := congrArg decode hec
          have heu' := congrArg decode heu
          rw [decode_bitLift, decode_bitLift] at hec' heu'
          exact SharedPointLift.equal_of_signatures payload hpair row.1.1 row.2.1 _ _ hneL hneR
            _ _ _ _ hLc.symm hLu.symm hRc.symm hRu.symm hec' heu'
            (SharedPointLift.lifted_core_card row.1.1 _ hcore)

/-- Lower bounds connect independently checked chunks into one strict ordering. -/
def Above (previous : Option ℕ) (current : ℕ) : Prop :=
  match previous with | none => True | some p => p < current

instance (previous : Option ℕ) (current : ℕ) : Decidable (Above previous current) := by
  unfold Above
  split <;> infer_instance

def lastKey : Option ℕ → List (Witness n) → Option ℕ
  | previous, [] => previous
  | _, row :: rows => lastKey (some (key row)) rows

/-- The strict sort check also certifies that no witness is counted twice. -/
def checkFrom (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n)) :
    Option ℕ → List (Witness n) → Bool
  | _, [] => true
  | previous, row :: rows => decide (Above previous (key row)) &&
    checkRow isAddition coreBank unionBank row &&
      checkFrom isAddition coreBank unionBank (some (key row)) rows

theorem checkFrom_sound (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (previous : Option ℕ) (rows : List (Witness n))
    (hc : checkFrom isAddition coreBank unionBank previous rows = true) :
    rows.Pairwise (fun a b => key a < key b) ∧
      (∀ row ∈ rows, checkRow isAddition coreBank unionBank row = true) ∧
      (∀ row ∈ rows, Above previous (key row)) := by
  induction rows generalizing previous with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨⟨hp, hr⟩, ht⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left Bool.and_eq_true_iff.mp
    have hp' : Above previous (key row) := of_decide_eq_true hp
    obtain ⟨hs, hall, hlo⟩ := ih (some (key row)) ht
    refine ⟨List.pairwise_cons.mpr ⟨hlo, hs⟩, ?_, ?_⟩
    · intro other ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hr
      · exact hall other ho
    · intro other ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hp'
      · cases previous with
        | none => trivial
        | some p => exact Nat.lt_trans hp' (hlo other ho)

/-- Finset conversion preserves the entire certified witness count. -/
theorem checkFrom_nodup (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (previous : Option ℕ) (rows : List (Witness n))
    (hc : checkFrom isAddition coreBank unionBank previous rows = true) : rows.Nodup := by
  have hs := (checkFrom_sound isAddition coreBank unionBank previous rows hc).1
  exact hs.imp (fun {a b} hlt he => by subst b; exact Nat.lt_irrefl _ hlt)

theorem checkFrom_card (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (previous : Option ℕ) (rows : List (Witness n))
    (hc : checkFrom isAddition coreBank unionBank previous rows = true) : rows.toFinset.card = rows.length :=
  List.toFinset_card_of_nodup (checkFrom_nodup isAddition coreBank unionBank previous rows hc)

theorem checkFrom_append (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (previous : Option ℕ) (first rest : List (Witness n)) :
    checkFrom isAddition coreBank unionBank previous (first ++ rest) =
      (checkFrom isAddition coreBank unionBank previous first &&
        checkFrom isAddition coreBank unionBank (lastKey previous first) rest) := by
  induction first generalizing previous with
  | nil => simp [checkFrom, lastKey]
  | cons row first ih => simp [checkFrom, lastKey, ih, Bool.and_assoc]

theorem checkFrom_append_of (isAddition : ℕ → Bool) (coreBank unionBank : ℕ → Option (BitVec n))
    (previous : Option ℕ) (first rest : List (Witness n))
    (hf : checkFrom isAddition coreBank unionBank previous first = true)
    (hr : checkFrom isAddition coreBank unionBank (lastKey previous first) rest = true) :
    checkFrom isAddition coreBank unionBank previous (first ++ rest) = true := by
  rw [checkFrom_append, hf, hr]
  rfl

/-- Compact classification of an addition-only suffix of an existing DAG. -/
def checkKinds (lower : ℕ) : ℕ → List (MaskDAG.Entry width) → Bool
  | _, [] => true
  | offset, entry :: entries =>
    (if lower ≤ offset then match entry.kind with | .input _ => false | .add _ _ => true else true) &&
      checkKinds lower (offset+1) entries

theorem checkKinds_sound (lower offset : ℕ) (entries : List (MaskDAG.Entry width))
    (hc : checkKinds lower offset entries = true) (i : ℕ) (hi : i < entries.length)
    (hl : lower ≤ offset+i) : ∃ l r, entries[i].kind = .add l r := by
  induction entries generalizing offset i with
  | nil => simp at hi
  | cons entry entries ih =>
    obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hc
    cases i with
    | zero =>
      have hle : lower ≤ offset := by simpa using hl
      simp only [hle, ite_eq_left] at hc
      cases hk : entry.kind with
      | input source => simp [hk] at hc
      | add left right => exact ⟨left, right, hk⟩
    | succ i =>
      exact ih (offset+1) ht i (by simpa using hi) (by omega)

theorem checkKinds_append (lower offset : ℕ) (first rest : List (MaskDAG.Entry width)) :
    checkKinds lower offset (first ++ rest) =
      (checkKinds lower offset first && checkKinds lower (offset+first.length) rest) := by
  induction first generalizing offset with
  | nil => simp [checkKinds]
  | cons entry first ih => simp [checkKinds, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm]

theorem checkKinds_append_of (lower offset : ℕ) (first rest : List (MaskDAG.Entry width))
    (hf : checkKinds lower offset first = true)
    (hr : checkKinds lower (offset+first.length) rest = true) :
    checkKinds lower offset (first ++ rest) = true := by
  rw [checkKinds_append, hf, hr]
  rfl

end IntegerMultBounds.Networks.SharedPointWitnessCheck
