import IntegerMultBounds.Machine.RadixZeroFill
import IntegerMultBounds.Machine.FamilyPlacementAlphabet

/-! A finite family of physical prefix-field initializers. Each dimension has
an output, reusable clock, and immutable binary width descriptor. A final spare
tape makes the empty family a genuine machine as well. Only the number of fields
is compiled into the transition table; every width is supplied on a tape. -/
namespace IntegerMultBounds.Machine.PrefixCounterInit
variable {q : ℕ} (hq : 2 ≤ q)

/-- Triple per dimension, plus one untouched spare. -/
def tapeCount : ℕ → ℕ
  | 0 => 1
  | c+1 => 3+tapeCount c

def stateCount : ℕ → ℕ
  | 0 => 1
  | c+1 => 23+stateCount c

theorem tapeCount_eq (c : ℕ) : tapeCount c = 3*c+1 := by
  induction c <;> simp_all [tapeCount]; omega

theorem stateCount_eq (c : ℕ) : stateCount c = 23*c+1 := by
  induction c <;> simp_all [stateCount]; omega

private def haltProgram : Program 1 1 q where
  tapes_pos := by decide
  start := 0
  transition := fun _ _ => none

private def spare : Tapes 1 q := ⟨fun _ => 0, fun _ _ => blank⟩

def program : (c : ℕ) → Program (tapeCount c) (stateCount c) q
  | 0 => haltProgram
  | c+1 => FamilyPlacementAlphabet.sequence (RadixZeroFill.program hq) (program c)

def input : (c : ℕ) → (Fin c → List Bool) → Tapes (tapeCount c) q
  | 0, _ => spare
  | c+1, bs => (RadixZeroFill.input (bs 0)).append (input c (fun i => bs i.succ))

def output : (c : ℕ) → (Fin c → List Bool) → (Fin c → ℕ) → Tapes (tapeCount c) q
  | 0, _, _ => spare
  | c+1, bs, width => (RadixZeroFill.output hq (bs 0) (width 0)).append
      (output c (fun i => bs i.succ) (fun i => width i.succ))

/-- Actual complete initialization, with every join and head restoration charged. -/
theorem initialize_hoare (c : ℕ) (bs : Fin c → List Bool) (width : Fin c → ℕ)
    (hn : ∀ i, Counter.value (bs i) = width i)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) :
    HoareTime (program hq c) (fun v => v = input c bs)
      (fun v => v = output hq c bs width) (15*(∑ i, width i)+29*c) := by
  induction c with
  | zero =>
    rintro v rfl
    refine ⟨0,(spare (q := q)).start haltProgram,?_,rfl,rfl,rfl⟩
    simp
  | succ c ih =>
    have h := FamilyPlacementAlphabet.sequence_hoare
      (RadixZeroFill.fill_zeros_linear hq (bs 0) (width 0) (hn 0) (hc 0))
      (ih (fun i => bs i.succ) (fun i => width i.succ) (fun i => hn i.succ) (fun i => hc i.succ))
    apply h.consequence (fun _ h => h) (fun _ h => h) _
    rw [Fin.sum_univ_succ]
    omega

/-- Physical location of each scheduler field in the initialized family. -/
def fieldSlot : (c : ℕ) → Fin c → Fin (tapeCount c)
  | 0, i => Fin.elim0 i
  | c+1, i => Fin.cases (Fin.castAdd (tapeCount c) (0 : Fin 3)) (fun j => Fin.natAdd 3 (fieldSlot c j)) i

@[simp] theorem fieldSlot_zero (c : ℕ) : fieldSlot (c+1) 0 = Fin.castAdd (tapeCount c) (0 : Fin 3) := rfl

@[simp] theorem fieldSlot_succ (c : ℕ) (i : Fin c) :
    fieldSlot (c+1) i.succ = Fin.natAdd 3 (fieldSlot c i) := rfl

theorem fieldSlot_injective (c : ℕ) : Function.Injective (fieldSlot c) := by
  induction c with
  | zero => intro i; exact Fin.elim0 i
  | succ c ih =>
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => have hh := congrArg Fin.val hij; simp only [fieldSlot_zero,fieldSlot_succ,Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd] at hh; omega
    | succ i =>
      induction j using Fin.cases with
      | zero => have hh := congrArg Fin.val hij; simp only [fieldSlot_zero,fieldSlot_succ,Fin.val_castAdd,Fin.val_zero,Fin.val_natAdd] at hh; omega
      | succ j =>
        apply congrArg Fin.succ
        apply ih
        exact Fin.ext (by have hh := congrArg Fin.val hij; simpa only [fieldSlot_succ,Fin.val_natAdd,Nat.add_left_cancel_iff] using hh)

/-- The exact scheduler bank selected from the concrete machine tapes. -/
def fields (c : ℕ) (v : Tapes (tapeCount c) q) : Tapes c q :=
  ⟨fun i => v.head (fieldSlot c i),fun i => v.tape (fieldSlot c i)⟩

theorem output_fields (c : ℕ) (bs : Fin c → List Bool) (width : Fin c → ℕ) :
    fields c (output hq c bs width) =
      PrefixCounter.tapes (fun _ => RadixZeroFill.radixEmpty)
        (fun i => RadixCounterData.zeros hq (width i)) := by
  induction c with
  | zero => apply congrArg₂ Tapes.mk <;> funext i <;> exact Fin.elim0 i
  | succ c ih =>
    have hh := congrArg Tapes.head (ih (fun i => bs i.succ) (fun i => width i.succ))
    have ht := congrArg Tapes.tape (ih (fun i => bs i.succ) (fun i => width i.succ))
    apply congrArg₂ Tapes.mk
    · funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => simpa only [fields,output,fieldSlot_succ,Tapes.append,Fin.addCases_right,PrefixCounter.tapes] using congrFun hh i
    · funext i
      induction i using Fin.cases with
      | zero =>
        simp only [fieldSlot_zero,output,Tapes.append,Fin.addCases_left,RadixZeroFill.output,
          RadixZeroFill.radixZeros,RadixCounter.digitsTape,RadixCounterData.zeros,List.map_replicate]
        rfl
      | succ i => simpa only [fields,output,fieldSlot_succ,Tapes.append,Fin.addCases_right,PrefixCounter.tapes] using congrFun ht i

end IntegerMultBounds.Machine.PrefixCounterInit
