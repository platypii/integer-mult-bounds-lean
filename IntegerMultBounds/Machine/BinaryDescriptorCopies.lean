import IntegerMultBounds.Machine.BinaryDescriptorCopy
import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.FamilyPlacementAlphabet
import IntegerMultBounds.Machine.ExactFrame

/-! Replicate one supplied binary descriptor onto a fixed number of genuinely
blank tapes. The source is preserved, all resulting heads are restored to one,
and every copy and sequential join is charged. No descriptor length occurs in
the transition table, and no extra workspace tape is used. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorCopies
noncomputable section
variable {q : ℕ}

def single (q : ℕ) (xs : List Bool) : Tapes 1 q :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary xs⟩

def empty (q : ℕ) : Tapes 1 q := ⟨fun _ => 0,fun _ _ => blank⟩

/-- Tape zero is the only supplied descriptor. All n destinations are blank. -/
def input (q : ℕ) : (n : ℕ) → List Bool → Tapes (n+1) q
  | 0,xs => single q xs
  | n+1,xs => (input q n xs).append (empty q)

/-- Explicit initial layout: source zero is preserved input; all destinations
start with a wholly blank tape and head zero. -/
theorem input_layout (q n : ℕ) (xs : List Bool) :
    input q n xs =
      (⟨fun i => if i.val = 0 then 1 else 0,
        fun i => if i.val = 0 then RadixZeroFill.encodedBinary xs else fun _ => blank⟩ : Tapes (n+1) q) := by
  induction n with
  | zero =>
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  | succ n ih =>
    rw [input,ih]
    unfold Tapes.append empty
    congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp


/-- The original and all n copies have identical complete tapes and head one. -/
def output (q : ℕ) (n : ℕ) (xs : List Bool) : Tapes (n+1) q :=
  ⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary xs⟩

theorem output_succ (q n : ℕ) (xs : List Bool) :
    output q (n+1) xs = (output q n xs).append (single q xs) := by
  unfold output single Tapes.append
  congr 1 <;> funext i <;> induction i using Fin.addCases <;> simp

def sourceSlot (n : ℕ) : Fin ((n+1)+1) := Fin.castAdd 1 (0 : Fin (n+1))
def destSlot (n : ℕ) : Fin ((n+1)+1) := Fin.natAdd (n+1) (0 : Fin 1)

def slots (n : ℕ) : Fin 2 → Fin ((n+1)+1) := ![sourceSlot n,destSlot n]

theorem slots_injective (n : ℕ) : Function.Injective (slots n) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    have hv := congrArg Fin.val h
    simp [slots,sourceSlot,destSlot] at hv

def placement (n : ℕ) : Fin (2+n) ≃ Fin ((n+1)+1) :=
  InjectivePlacement.placement (slots n) (slots_injective n) (by omega)

theorem placement_active (n : ℕ) (i : Fin 2) :
    placement n (Fin.castAdd n i) = slots n i :=
  InjectivePlacement.active_slot _ _ _ i

private theorem active_before (q n : ℕ) (xs : List Bool) :
    Placement.active (placement n) ((output q n xs).append (empty q)) =
      BinaryDescriptorCopy.encodedInput q xs := by
  rw [show placement n = InjectivePlacement.placement (slots n) (slots_injective n) (by omega) from rfl,
    InjectivePlacement.active_bank]
  unfold slots sourceSlot destSlot
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [Tapes.append,output,empty,Copy.cfg]

private theorem active_after (q n : ℕ) (xs : List Bool) :
    Placement.active (placement n) (output q (n+1) xs) = BinaryDescriptorCopy.encodedOutput q xs := by
  unfold Placement.active output BinaryDescriptorCopy.encodedOutput Copy.tapes Copy.cfg Config.tapes
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_unchanged (q n : ℕ) (xs : List Bool) :
    Placement.extra (placement n) ((output q n xs).append (empty q)) =
      Placement.extra (placement n) (output q (n+1) xs) := by
  have hleft (j : Fin n) : (placement n (Fin.natAdd 2 j)).val < n+1 := by
    have hn : placement n (Fin.natAdd 2 j) ≠ destSlot n := by
      intro he
      have hd : destSlot n = placement n (Fin.castAdd n (1 : Fin 2)) :=
        (placement_active n 1).symm
      rw [hd] at he
      have hv := congrArg Fin.val ((placement n).injective he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    have hv := (placement n (Fin.natAdd 2 j)).isLt
    have hd : (destSlot n).val = n+1 := rfl
    have hne : (placement n (Fin.natAdd 2 j)).val ≠ n+1 := by
      intro he
      apply hn
      exact Fin.ext (he.trans hd.symm)
    omega
  unfold Placement.extra
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals
    have he : placement n (Fin.natAdd 2 j) = Fin.castAdd 1 ⟨_,hleft j⟩ := Fin.ext rfl
    rw [he]
    simp only [Tapes.append,Fin.addCases_left,output]

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => states n+5

theorem states_eq (n : ℕ) : states n = 5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [states,ih]; omega

/-- Fixed finite control; n copies use exactly n+1 physical tapes. -/
def program (q : ℕ) : (n : ℕ) → Program (n+1) (states n) q
  | 0 => skip 1 q (by decide)
  | n+1 => seq (extend (program q n) 1)
      (Placement.placed (BinaryDescriptorCopy.encodedProgram q) (placement n))

/-- Whole-bank correctness, including restoration of the sole original.
The extra one per copy pays the actual join from the recursive prefix. -/
theorem copies_hoare (q n : ℕ) (xs : List Bool) :
    HoareTime (program q n) (fun v => v = input q n xs) (fun v => v = output q n xs)
      (n*(2*xs.length+6)) := by
  induction n with
  | zero => simpa only [program,states,input,output,single,Nat.zero_mul] using skip_hoare (by decide) (single q xs)
  | succ n ih =>
    have hp := FamilyPlacementAlphabet.extend_hoare ih (empty q)
    have hc := Placement.hoare_at (BinaryDescriptorCopy.encoded_copy_hoare q xs) (placement n)
      ((output q n xs).append (empty q)) (active_before q n xs)
    have hc' : HoareTime (Placement.placed (BinaryDescriptorCopy.encodedProgram q) (placement n))
        (fun v => v = (output q n xs).append (empty q))
        (fun v => v = output q (n+1) xs) (2*xs.length+5) := by
      apply hc.consequence (fun _ h => h) ?_ le_rfl
      rintro v ⟨small,hsmall,rfl⟩
      subst small
      rw [Placement.replace,extra_unchanged,← active_after q n xs]
      exact Placement.view _ _
    exact (hp.seq hc').consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

/-- Canonical descriptors give the usual logarithmic bound in their value. -/
theorem copies_hoare_canonical (q n : ℕ) (xs : List Bool) (hx : GrowingCounterData.Canonical xs) :
    HoareTime (program q n) (fun v => v = input q n xs) (fun v => v = output q n xs)
      (n*(2*(Counter.value xs).log2+8)) := by
  apply (copies_hoare q n xs).consequence (fun _ h => h) (fun _ h => h) ?_
  apply Nat.mul_le_mul_left
  have hh := GrowingCounterData.canonical_width xs hx
  omega

end
end IntegerMultBounds.Machine.BinaryDescriptorCopies
