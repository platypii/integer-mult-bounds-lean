import IntegerMultBounds.Machine.DigitInterchangePasses
import IntegerMultBounds.Machine.InjectivePlacement
import Mathlib.Tactic.DeriveFintype

/-! One fixed bank for all width-one digit interchange passes. Stream slots are
named by fixed radix indices; runtime outer, middle and suffix lengths never
enter the machine wiring. Four descriptors and two marked loop clocks are
explicit inputs at this prepared boundary. -/
namespace IntegerMultBounds.Machine.DigitInterchangeBank
open DigitInterchangeRows CyclicRowSplit
noncomputable section
variable {O q C E a : ℕ}

inductive Slot (q : ℕ) where
  | source | dest | first (h : Fin q) | leaf (h d : Fin q) | merged (h : Fin q)
  | rowClock | groupClock | header (j : Fin 4)
  deriving DecidableEq, Fintype

inductive Pass (q : ℕ) where
  | splitOuter | splitInner (h : Fin q) | mergeInner (h : Fin q) | mergeOuter
  deriving DecidableEq

abbrev TapeCount (q : ℕ) := Fintype.card (Slot q)
def slot : Slot q → Fin (TapeCount q) := Fintype.equivFin (Slot q)
def name : Fin (TapeCount q) → Slot q := (Fintype.equivFin (Slot q)).symm
@[simp] theorem name_slot (z : Slot q) : name (slot z) = z := Equiv.symm_apply_apply _ _
@[simp] theorem slot_name (z : Fin (TapeCount q)) : slot (name z) = z := Equiv.apply_symm_apply _ _

def sourceName : Pass q → Slot q
  | .splitOuter => .source | .splitInner h => .first h
  | .mergeInner h => .merged h | .mergeOuter => .source

def roleName : Pass q → Fin q → Slot q
  | .splitOuter,h => .first h | .splitInner h,d => .leaf h d
  | .mergeInner h,d => .leaf d h | .mergeOuter,h => .merged h

def blockHeader : Pass q → Fin 4
  | .splitOuter | .mergeOuter => 0 | _ => 2

def groupHeader : Pass q → Fin 4
  | .splitOuter | .mergeOuter => 1 | _ => 3

abbrev LocalTapes (q : ℕ) := ((1+q)+2)+2

def sourceIndex : Fin (LocalTapes q) := Fin.castAdd 2 (Fin.castAdd 2 (Fin.castAdd q (0 : Fin 1)))
def roleIndex (h : Fin q) : Fin (LocalTapes q) := Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 h))
def rowIndex (z : Fin 2) : Fin (LocalTapes q) := Fin.castAdd 2 (Fin.natAdd (1+q) z)
def groupIndex (z : Fin 2) : Fin (LocalTapes q) := Fin.natAdd ((1+q)+2) z

def activeName (p : Pass q) : Fin (LocalTapes q) → Slot q :=
  Fin.addCases (Fin.addCases (Fin.addCases (fun _ : Fin 1 => sourceName p) (roleName p))
    ![.rowClock,.header (blockHeader p)]) ![.groupClock,.header (groupHeader p)]

def decode (p : Pass q) : Slot q → Option (Fin (LocalTapes q))
  | .source => if p = .splitOuter ∨ p = .mergeOuter then some sourceIndex else none
  | .dest => none
  | .first h => match p with
    | .splitOuter => some (roleIndex h)
    | .splitInner j => if h = j then some sourceIndex else none
    | _ => none
  | .leaf h d => match p with
    | .splitInner j => if h = j then some (roleIndex d) else none
    | .mergeInner j => if d = j then some (roleIndex h) else none
    | _ => none
  | .merged h => match p with
    | .mergeInner j => if h = j then some sourceIndex else none
    | .mergeOuter => some (roleIndex h)
    | _ => none
  | .rowClock => some (rowIndex 0)
  | .groupClock => some (groupIndex 0)
  | .header j => if j = blockHeader p then some (rowIndex 1)
      else if j = groupHeader p then some (groupIndex 1) else none

private theorem decode_active (p : Pass q) (i : Fin (LocalTapes q)) : decode p (activeName p i) = some i := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => fin_cases i; cases p <;> simp [activeName,sourceName,decode,sourceIndex]
      | right h => cases p <;> simp [activeName,roleName,decode,roleIndex]
    | right z => fin_cases z <;> cases p <;> simp [activeName,decode,blockHeader,groupHeader,rowIndex]
  | right z => fin_cases z <;> cases p <;> simp [activeName,decode,blockHeader,groupHeader,groupIndex]

theorem activeName_injective (p : Pass q) : Function.Injective (activeName p) := by
  intro i j h
  have hh := congrArg (decode p) h
  simpa only [decode_active,Option.some.injEq] using hh

def ports (p : Pass q) (i : Fin (LocalTapes q)) := slot (activeName p i)
theorem ports_injective (p : Pass q) : Function.Injective (ports p) :=
  (Fintype.equivFin (Slot q)).injective.comp (activeName_injective p)

theorem tapeCount_ge : LocalTapes q ≤ TapeCount q := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (ports_injective (.splitOuter : Pass q))

def placement (p : Pass q) : Fin (LocalTapes q+(TapeCount q-LocalTapes q)) ≃ Fin (TapeCount q) :=
  InjectivePlacement.placement (ports p) (ports_injective p) (Nat.add_sub_of_le tapeCount_ge)

/-- Ordinal of a pass in the fixed physical schedule. -/
def passIndex : Pass q → ℕ
  | .splitOuter => 0 | .splitInner h => 1+h.val
  | .mergeInner h => 1+q+h.val | .mergeOuter => 1+q+q

def headerWord (bs gs es cs : List Bool) : Fin 4 → List Bool := ![bs,gs,es,cs]

def head : Slot q → ℤ
  | .rowClock | .groupClock | .header _ => 1 | _ => 0

def word (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) : Slot q → ℤ → Fin (a+4)
  | .source => if 1+q+q < k then putWord (fun _ => blank) 0 (sourceWord (outerRows (transpose x)))
      else putWord (fun _ => blank) 0 (sourceWord (outerRows x))
  | .dest => fun _ => blank
  | .first h => if 0 < k then putWord (fun _ => blank) 0 (sourceWord (innerRows x h)) else fun _ => blank
  | .leaf h d => if 1+h.val < k then putWord (fun _ => blank) 0 (roleWord (innerRows x h) d) else fun _ => blank
  | .merged h => if 1+q+h.val < k then putWord (fun _ => blank) 0 (roleWord (outerRows (transpose x)) h) else fun _ => blank
  | .rowClock | .groupClock => CountedLoopReuseAlphabet.empty
  | .header j => CountedLoopReuseAlphabet.binary (headerWord bs gs es cs j)

def bank (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) : Tapes (TapeCount q) a :=
  ⟨fun i => head (name i),fun i => word x bs gs es cs k (name i)⟩

@[simp] theorem bank_head (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) (z : Slot q) :
    (bank x bs gs es cs k).head (slot z) = head z := by simp [bank]
@[simp] theorem bank_tape (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) (z : Slot q) :
    (bank x bs gs es cs k).tape (slot z) = word x bs gs es cs k z := by simp [bank]

theorem active_bank (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) :
    Placement.active (placement p) (bank x bs gs es cs k) =
      ⟨fun i => head (activeName p i),fun i => word x bs gs es cs k (activeName p i)⟩ := by
  rw [placement,InjectivePlacement.active_bank]
  simp only [ports,bank_head,bank_tape]


def localBank (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) : Tapes (LocalTapes q) a :=
  CyclicRowSplit.bank (CyclicRowCopy.bank (word x bs gs es cs k (sourceName p))
    (fun h => word x bs gs es cs k (roleName p h)) 0 (fun _ => 0)
    (headerWord bs gs es cs (blockHeader p))) (headerWord bs gs es cs (groupHeader p))

theorem active_local (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool) (k : ℕ) :
    Placement.active (placement p) (bank x bs gs es cs k) = localBank p x bs gs es cs k := by
  rw [active_bank]
  apply congrArg₂ Tapes.mk
  all_goals
    funext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left z => fin_cases z; cases p <;> simp [activeName,localBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
          CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,head,sourceName,roleName,word]
        | right h => cases p <;> simp [activeName,localBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
          CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,head,sourceName,roleName,word]
      | right z => fin_cases z <;> cases p <;> simp [activeName,localBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
          CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,head,sourceName,roleName,word]
    | right z => fin_cases z <;> cases p <;> simp [activeName,localBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
          CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,head,sourceName,roleName,word]

@[simp] theorem active_source (p : Pass q) : activeName p sourceIndex = sourceName p := by simp [activeName,sourceIndex]
@[simp] theorem active_role (p : Pass q) (h : Fin q) : activeName p (roleIndex h) = roleName p h := by simp [activeName,roleIndex]

private theorem word_frame (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool)
    (z : Slot q) (hz : ∀ i, z ≠ activeName p i) :
    word x bs gs es cs (passIndex p) z = word x bs gs es cs (passIndex p+1) z := by
  have hs : z ≠ sourceName p := by simpa only [active_source] using hz sourceIndex
  have hr : ∀ h, z ≠ roleName p h := fun h => by simpa only [active_role] using hz (roleIndex h)
  have stable (n : ℕ) (f g : ℤ → Fin (a+4)) (hn : n ≠ passIndex p) :
      (if n < passIndex p then f else g) =
        (if n < passIndex p+1 then f else g) := by
    have he : n < passIndex p ↔ n < passIndex p+1 := by omega
    simp only [he]
  cases z with
  | dest => rfl
  | rowClock => rfl
  | groupClock => rfl
  | header j => rfl
  | source =>
    apply stable
    cases p with
    | mergeOuter => exact (hs rfl).elim
    | splitOuter => simp [passIndex] <;> omega
    | splitInner h => simp only [passIndex]; have := h.isLt; omega
    | mergeInner h => simp only [passIndex]; have := h.isLt; omega
  | first h =>
    apply stable
    cases p with
    | splitOuter => exact (hr h rfl).elim
    | splitInner j => simp [passIndex] <;> omega
    | mergeInner j => simp [passIndex] <;> omega
    | mergeOuter => simp [passIndex] <;> omega
  | leaf h d =>
    apply stable
    cases p with
    | splitOuter => simp [passIndex] <;> omega
    | splitInner j =>
      have hn : h ≠ j := by intro he; subst j; exact hr d rfl
      have hn' : h.val ≠ j.val := fun he => hn (Fin.ext he)
      simp only [passIndex]
      omega
    | mergeInner j => simp only [passIndex]; have := h.isLt; omega
    | mergeOuter => simp only [passIndex]; have := h.isLt; omega
  | merged h =>
    apply stable
    cases p with
    | splitOuter => simp [passIndex] <;> omega
    | splitInner j => simp only [passIndex]; have := j.isLt; omega
    | mergeInner j =>
      have hn : h ≠ j := by intro he; subst j; exact hs rfl
      have hn' : h.val ≠ j.val := fun he => hn (Fin.ext he)
      simp only [passIndex]
      omega
    | mergeOuter => simp only [passIndex]; have := h.isLt; omega

theorem frame (p : Pass q) (x : Array O q C E a) (bs gs es cs : List Bool) :
    Placement.extra (placement p) (bank x bs gs es cs (passIndex p)) =
      Placement.extra (placement p) (bank x bs gs es cs (passIndex p+1)) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    apply word_frame
    intro j he
    have hh := congrArg slot he
    simp only [slot_name] at hh
    have ha : slot (activeName p j) = placement p (Fin.castAdd _ j) :=
      (InjectivePlacement.active_slot (ports p) (ports_injective p) _ j).symm
    rw [ha] at hh
    have hf := (placement p).injective hh
    have hv := congrArg Fin.val hf
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hj := j.isLt
    omega

end
end IntegerMultBounds.Machine.DigitInterchangeBank
