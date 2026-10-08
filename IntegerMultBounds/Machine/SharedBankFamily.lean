import IntegerMultBounds.Machine.SharedBankRawCompose

/-! One fixed physical tape count for a finite cyclic family of clean blocks.
Padding is program extension by unused stationary tapes plus an index-type cast;
it performs no tape copying, head movement, initialization, or extra transition.
The workspace bound depends only on the selected finite machine family. -/
namespace IntegerMultBounds.Machine.SharedBankFamily
open SharedBankStageInput (raw)
open SharedBankSkeleton (Skeleton)
universe u
variable {k t n r a : ℕ}
noncomputable section

/-- Existing leading common data plus blank padding is exactly the larger raw
bank, provided the existing machine contains every permanent tape. -/
theorem raw_append (common : Tapes k a) (hkt : k ≤ t) (extra : ℕ) :
    (raw common t).append (SharedBank.empty extra a) = raw common (t+extra) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp only [Fin.addCases_left,raw,Fin.val_castAdd]
  | right i =>
    have hi : ¬ t+i.val < k := by omega
    simp only [Fin.addCases_right,raw,Fin.val_natAdd,hi,↓reduceDIte,SharedBank.empty]

theorem raw_reindex (common : Tapes k a) (h : t = n) :
    (raw common t).reindex (finCongr h) = raw common n := by
  subst n
  rfl

/-- The full underlying program is extended, with no control-state addition. -/
def padProgram (M : Program t r a) (h : t ≤ n) : Program n r a :=
  reindex (extend M (n-t)) (finCongr (Nat.add_sub_of_le h))

/-- Padding is literal identity on every old physical tape index. -/
theorem pad_slot_value (h : t ≤ n) (i : Fin t) :
    ((finCongr (Nat.add_sub_of_le h)) (Fin.castAdd (n-t) i)).val = i.val := rfl

theorem pad_realizes {M : Program t r a} (h : t ≤ n) (hkt : k ≤ t)
    (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime M (fun v => v = raw before t) (fun v => v = raw after t) cost) :
    HoareTime (padProgram M h) (fun v => v = raw before n) (fun v => v = raw after n) cost := by
  have hp := hoare_reindex_eq (hoare_extend_eq hh (SharedBank.empty (n-t) a)) (finCongr (Nat.add_sub_of_le h))
  simpa only [padProgram,raw_append _ hkt,raw_reindex] using hp

/-- Direct adapter for existing CleanSubbank.bank endpoints. All appended
private tapes remain physically blank; runtime is exactly the original bound. -/
theorem pad_clean_realizes {s : ℕ} {M : Program (k+s) r a} (h : k+s ≤ n)
    (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime M (fun v => v = CleanSubbank.bank (s := s) before)
      (fun v => v = CleanSubbank.bank (s := s) after) cost) :
    HoareTime (padProgram M h) (fun v => v = raw before n) (fun v => v = raw after n) cost := by
  apply pad_realizes h (Nat.le_add_right k s) before after cost
  simpa only [SharedBankRawCompose.bank_eq_raw] using hh

/-- Package any fixed clean block with its actual leading permanent slots. -/
def ofProgram {s : ℕ} (M : Program (k+s) r a) : Skeleton k a where
  tapes := k+s
  states := r
  program := M
  slots := Fin.castAdd s
  slots_injective := Fin.castAdd_injective _ _

@[simp] theorem ofProgram_slots {s : ℕ} (M : Program (k+s) r a) (i : Fin k) :
    ((ofProgram M).slots i).val = i.val := rfl

theorem common_le (block : Skeleton k a) : k ≤ block.tapes := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective block.slots block.slots_injective

/-- Padding keeps the complete fixed skeleton and the same common slot values. -/
def pad (block : Skeleton k a) (h : block.tapes ≤ n) : Skeleton k a where
  tapes := n
  states := block.states
  program := padProgram block.program h
  slots := fun i => Fin.castLE h (block.slots i)
  slots_injective := (Fin.castLE_injective h).comp block.slots_injective

@[simp] theorem pad_tapes (block : Skeleton k a) (h : block.tapes ≤ n) : (pad block h).tapes = n := rfl
@[simp] theorem pad_states (block : Skeleton k a) (h : block.tapes ≤ n) : (pad block h).states = block.states := rfl
@[simp] theorem pad_slots_value (block : Skeleton k a) (h : block.tapes ≤ n) (i : Fin k) :
    ((pad block h).slots i).val = (block.slots i).val := rfl

theorem pad_skeleton_realizes (block : Skeleton k a) (h : block.tapes ≤ n)
    (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime block.program (fun v => v = raw before block.tapes)
      (fun v => v = raw after block.tapes) cost) :
    HoareTime (pad block h).program (fun v => v = raw before n) (fun v => v = raw after n) cost :=
  pad_realizes h (common_le block) before after cost hh

section Family
variable {Label : Type u} [Fintype Label]

/-- A static sum bound also works for an empty family. Width, data and recursive
depth are not arguments of this tape count or the padded transition tables. -/
def tapeCount (blocks : Label → Skeleton k a) : ℕ := k+∑ i, (blocks i).tapes

theorem block_le (blocks : Label → Skeleton k a) (i : Label) : (blocks i).tapes ≤ tapeCount blocks := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (blocks j).tapes) (Finset.mem_univ i)
  exact h.trans (Nat.le_add_left _ _)

theorem common_le_tapeCount (blocks : Label → Skeleton k a) : k ≤ tapeCount blocks := Nat.le_add_right _ _

def uniform (blocks : Label → Skeleton k a) (i : Label) : Skeleton k a := pad (blocks i) (block_le blocks i)

def program (blocks : Label → Skeleton k a) (i : Label) :
    Program (tapeCount blocks) (blocks i).states a := (uniform blocks i).program

@[simp] theorem uniform_tapes (blocks : Label → Skeleton k a) (i : Label) :
    (uniform blocks i).tapes = tapeCount blocks := rfl
@[simp] theorem uniform_states (blocks : Label → Skeleton k a) (i : Label) :
    (uniform blocks i).states = (blocks i).states := rfl

/-- Every label addresses the identical permanent leading bank. This equality
is about the actual compiled slot map, not a logical bank relocation. -/
theorem uniform_slots (blocks : Label → Skeleton k a)
    (hleading : ∀ i j, ((blocks i).slots j).val = j.val) (i : Label) (j : Fin k) :
    (uniform blocks i).slots j = Fin.castLE (common_le_tapeCount blocks) j := by
  apply Fin.ext
  exact hleading i j

theorem realizes (blocks : Label → Skeleton k a) (i : Label)
    (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime (blocks i).program (fun v => v = raw before (blocks i).tapes)
      (fun v => v = raw after (blocks i).tapes) cost) :
    HoareTime (program blocks i) (fun v => v = raw before (tapeCount blocks))
      (fun v => v = raw after (tapeCount blocks)) cost :=
  pad_skeleton_realizes (blocks i) (block_le blocks i) before after cost hh

/-- Dependent semantic states may vary by label; the physical tape count is
still one compile-time constant and every original runtime bound is retained. -/
theorem family_realizes (blocks : Label → Skeleton k a) {Input : Label → Type*}
    (before after : (i : Label) → Input i → Tapes k a) (cost : (i : Label) → Input i → ℕ)
    (hh : ∀ i x, HoareTime (blocks i).program
      (fun v => v = raw (before i x) (blocks i).tapes)
      (fun v => v = raw (after i x) (blocks i).tapes) (cost i x)) :
    ∀ i x, HoareTime (program blocks i)
      (fun v => v = raw (before i x) (tapeCount blocks))
      (fun v => v = raw (after i x) (tapeCount blocks)) (cost i x) :=
  fun i x => realizes blocks i (before i x) (after i x) (cost i x) (hh i x)

/-- The common prefix is exact and every private tape is blank at both block
boundaries, irrespective of which family member will execute next. -/
theorem bank_payload (blocks : Label → Skeleton k a) (common : Tapes k a) :
    SharedBank.payload (raw common (tapeCount blocks)) (Fin.castLE (common_le_tapeCount blocks)) = common :=
  SharedBankRawCompose.payload_raw common _ (fun _ => rfl)

theorem bank_private (blocks : Label → Skeleton k a) (common : Tapes k a) :
    SharedBank.strip (raw common (tapeCount blocks)) (Fin.castLE (common_le_tapeCount blocks)) =
      SharedBank.empty (tapeCount blocks) a := SharedBankRawCompose.strip_raw common _ (fun _ => rfl)

/-- A caller may choose any static common upper bound instead of the sum. -/
def programAt (blocks : Label → Skeleton k a) (N : ℕ) (hN : ∀ i, (blocks i).tapes ≤ N) (i : Label) :
    Program N (blocks i).states a := padProgram (blocks i).program (hN i)

omit [Fintype Label] in
theorem realizesAt (blocks : Label → Skeleton k a) (N : ℕ) (hN : ∀ i, (blocks i).tapes ≤ N)
    (i : Label) (before after : Tapes k a) (cost : ℕ)
    (hh : HoareTime (blocks i).program (fun v => v = raw before (blocks i).tapes)
      (fun v => v = raw after (blocks i).tapes) cost) :
    HoareTime (programAt blocks N hN i) (fun v => v = raw before N) (fun v => v = raw after N) cost :=
  pad_realizes (hN i) (common_le (blocks i)) before after cost hh

/-- Direct finite-family constructor for the actual leading-prefix blocks. -/
def cleanBlocks (work states : Label → ℕ) (machines : (i : Label) → Program (k+work i) (states i) a) :
    Label → Skeleton k a := fun i => ofProgram (machines i)

theorem clean_family_realizes (work states : Label → ℕ)
    (machines : (i : Label) → Program (k+work i) (states i) a) {Input : Label → Type*}
    (before after : (i : Label) → Input i → Tapes k a) (cost : (i : Label) → Input i → ℕ)
    (hh : ∀ i x, HoareTime (machines i)
      (fun v => v = CleanSubbank.bank (s := work i) (before i x))
      (fun v => v = CleanSubbank.bank (s := work i) (after i x)) (cost i x)) :
    ∀ i x, HoareTime (program (cleanBlocks work states machines) i)
      (fun v => v = raw (before i x) (tapeCount (cleanBlocks work states machines)))
      (fun v => v = raw (after i x) (tapeCount (cleanBlocks work states machines))) (cost i x) := by
  apply family_realizes
  intro i x
  simpa only [cleanBlocks,ofProgram,SharedBankRawCompose.bank_eq_raw] using hh i x

theorem clean_family_slots (work states : Label → ℕ)
    (machines : (i : Label) → Program (k+work i) (states i) a) (i : Label) (j : Fin k) :
    (uniform (cleanBlocks work states machines) i).slots j =
      Fin.castLE (common_le_tapeCount (cleanBlocks work states machines)) j :=
  uniform_slots _ (fun _ _ => rfl) i j

end Family
end
end IntegerMultBounds.Machine.SharedBankFamily
