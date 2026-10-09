import IntegerMultBounds.Machine.RadixHighBlockJoinBank
import IntegerMultBounds.Machine.PlacedDescriptorConstruction
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Physical preparation of ordered high-block joining and separation.
The exponent lives on the retained outer-loop descriptor; power and product
construction reuse the thirteen blank arithmetic tapes. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinSetup
noncomputable section
open RadixHighBlockJoinBank (count)
open SharedPlacementAlphabet (setTape)
variable {q a : ℕ}

def total (q : ℕ) := count q+2

def prefixSlot : Fin (total q) := Fin.castAdd 2 RadixHighBlockJoinBank.prefixSlot
def suffixSlot : Fin (total q) := Fin.castAdd 2 RadixHighBlockJoinBank.suffixSlot
def baseSlot : Fin (total q) := Fin.castAdd 2 RadixHighBlockJoinBank.baseSlot
def originalPrefixSlot : Fin (total q) := Fin.castAdd 2 RadixHighBlockJoinBank.originalPrefixSlot
def originalSuffixSlot : Fin (total q) := Fin.castAdd 2 RadixHighBlockJoinBank.originalSuffixSlot
def scratchSlot (i : Fin 13) : Fin (total q) := Fin.castAdd 2 (RadixHighBlockJoinBank.scratchSlot i)
def exponentSlot : Fin (total q) := Fin.natAdd (count q) 1

def powerSlots : Fin 8 → Fin (total q) :=
  ![scratchSlot 1,scratchSlot 2,scratchSlot 3,scratchSlot 4,scratchSlot 5,
    scratchSlot 0,scratchSlot 6,exponentSlot]

theorem powerSlots_injective : Function.Injective (powerSlots (q := q)) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j
  all_goals simp [powerSlots,scratchSlot,exponentSlot,RadixHighBlockJoinBank.scratchSlot,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals first | rfl | (have hc := RadixHighBlockJoinBank.count_eq q; omega)

def powerPlacement : Fin (8+(total q-8)) ≃ Fin (total q) :=
  InjectivePlacement.placement powerSlots powerSlots_injective
    (by unfold total count RadixDigitMoveCore.count; omega)

@[simp] theorem powerPlacement_active (i : Fin 8) :
    powerPlacement (q := q) (Fin.castAdd (total q-8) i) = powerSlots i :=
  InjectivePlacement.active_slot _ _ _ _

def powerProgram := Placement.placed (FixedBasePowerDescriptor.program (q := a) q)
  (powerPlacement (q := q))

def workingSlot (growPrefix : Bool) : Fin (total q) := if growPrefix then prefixSlot else suffixSlot
def originalSlot (growPrefix : Bool) : Fin (total q) := if growPrefix then originalPrefixSlot else originalSuffixSlot

def productSlots (growPrefix : Bool) : Fin 6 → Fin (total q) :=
  ![scratchSlot 1,workingSlot growPrefix,scratchSlot 2,scratchSlot 0,scratchSlot 3,originalSlot growPrefix]

theorem productSlots_injective (growPrefix : Bool) : Function.Injective (productSlots (q := q) growPrefix) := by
  intro i j h
  have hv := congrArg Fin.val h
  cases growPrefix <;> fin_cases i <;> fin_cases j
  all_goals simp [productSlots,workingSlot,originalSlot,prefixSlot,suffixSlot,originalPrefixSlot,
    originalSuffixSlot,scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
    RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
    RadixHighBlockJoinBank.scratchSlot,Fin.val_castAdd] at hv
  all_goals first | rfl | omega

def productPlacement (growPrefix : Bool) : Fin (6+(total q-6)) ≃ Fin (total q) :=
  InjectivePlacement.placement (productSlots growPrefix) (productSlots_injective growPrefix)
    (by unfold total count RadixDigitMoveCore.count; omega)

@[simp] theorem productPlacement_active (growPrefix : Bool) (i : Fin 6) :
    productPlacement (q := q) growPrefix (Fin.castAdd (total q-6) i) = productSlots growPrefix i :=
  InjectivePlacement.active_slot _ _ _ _

def productProgram (growPrefix : Bool) := Placement.placed
  (BoundedProductDescriptor.program (q := a)) (productPlacement (q := q) growPrefix)

def grownBits (N r : ℕ) := BoundedProductDescriptor.bits N (q^r)
def powerBits (r : ℕ) := FixedBasePowerStep.bits q r

/-- Shared exponent and all outside tapes are retained by physical power
construction; the sole new descriptor occupies arithmetic scratch zero. -/
theorem power_hoare (v : Tapes (total q) a) (r : ℕ) (hq : 2 ≤ q) (rs : List Bool)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs)
    (ha : Placement.active powerPlacement v = FixedBasePowerDescriptor.input rs) :
    HoareTime powerProgram (fun w => w = v)
      (fun w => w = setTape v (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1)
      (FixedBasePowerDescriptor.constant q*q^r) := by
  simpa [powerProgram,powerPlacement_active,powerSlots,powerBits] using
    PlacedDescriptorConstruction.power_hoare powerPlacement v q r hq rs hr cr ha

/-- Generate the enlarged working prefix or suffix while retaining the
original shape and exponent. No product is supplied by the caller. -/
theorem product_hoare (growPrefix : Bool) (v : Tapes (total q) a) (N r : ℕ)
    (hq : 2 ≤ q) (ns : List Bool) (hn : Counter.value ns = N)
    (cn : GrowingCounterData.Canonical ns)
    (ha : Placement.active (productPlacement growPrefix) v =
      BoundedProductDescriptor.input (powerBits (q := q) r) ns) :
    HoareTime (productProgram growPrefix) (fun w => w = v)
      (fun w => w = setTape v (workingSlot growPrefix)
        (RadixZeroFill.encodedBinary (grownBits (q := q) N r)) 1)
      (53*(N*q^r)+28) := by
  have hw := GrowingCounterData.canonical_width ns cn
  rw [hn] at hw
  have hp := GrowingCounterData.canonical_width (powerBits (q := q) r)
    (FixedBasePowerStep.bits_canonical q r)
  rw [powerBits,FixedBasePowerStep.bits_value] at hp
  have h := PlacedDescriptorConstruction.product_hoare (productPlacement growPrefix) v
    (powerBits (q := q) r) ns N (q^r) N (pow_pos (by omega : 0 < q) r)
    (FixedBasePowerStep.bits_value q r) hn le_rfl
    (hp.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1))
    (hw.trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)) ha
  simpa [productProgram,productPlacement_active,productSlots,grownBits] using h


def bank (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) : Tapes (total q) a :=
  (RadixHighBlockJoinBank.bank (q := q) source ss op oe ps es ws).append ctrl

def optionHead : Option (List Bool) → ℤ | none => 0 | some _ => 1
def optionTape : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => CountedLoopReuseAlphabet.binary bs

theorem read_head (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) (i : Fin (count q)) :
    (bank source ss op oe ps es ws ctrl).head (Fin.castAdd 2 i) =
    (if i.val = q+4 then optionHead ps else if i.val = q+5 then optionHead es
     else if i.val = 2*q+31 then optionHead ws
     else if i.val = 2*q+14 ∨ i.val = 2*q+32 ∨ i.val = 2*q+33 then 1 else 0) := by
  simp only [bank,Tapes.append,Fin.addCases_left]
  rfl

theorem read_tape (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) (i : Fin (count q)) :
    (bank source ss op oe ps es ws ctrl).tape (Fin.castAdd 2 i) =
    (if i.val = 0 then source else if i.val = q+4 then optionTape ps
     else if i.val = q+5 then optionTape es else if i.val = 2*q+31 then optionTape ws
     else if i.val = 2*q+14 then CountedLoopReuseAlphabet.binary ss
     else if i.val = 2*q+32 then CountedLoopReuseAlphabet.binary op
     else if i.val = 2*q+33 then CountedLoopReuseAlphabet.binary oe else fun _ => blank) := by
  simp only [bank,Tapes.append,Fin.addCases_left]
  rfl

theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  change (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.binary bs z)) = _
  exact CountedLoopReuseAlphabet.encoding_binary bs

theorem encoded_descriptor (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    BinaryDescriptorStack.descriptor bs := (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem set_prefix (source : ℤ → Fin (a+4)) (ss op oe bs : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) prefixSlot
      (RadixZeroFill.encodedBinary bs) 1 = bank source ss op oe (some bs) es ws ctrl := by
  unfold total
  rw [prefixSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = q+4
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = q+4
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

theorem set_suffix (source : ℤ → Fin (a+4)) (ss op oe bs : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) suffixSlot
      (RadixZeroFill.encodedBinary bs) 1 = bank source ss op oe ps (some bs) ws ctrl := by
  unfold total
  rw [suffixSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = q+5
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = q+5
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

theorem clear_prefix (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) prefixSlot
      (fun _ => blank) 0 = bank source ss op oe none es ws ctrl := by
  unfold total
  rw [prefixSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = q+4
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = q+4
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

theorem clear_suffix (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) suffixSlot
      (fun _ => blank) 0 = bank source ss op oe ps none ws ctrl := by
  unfold total
  rw [suffixSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = q+5
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = q+5
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

theorem set_base (source : ℤ → Fin (a+4)) (ss op oe bs : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) baseSlot
      (RadixZeroFill.encodedBinary bs) 1 = bank source ss op oe ps es (some bs) ctrl := by
  unfold total
  rw [baseSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = 2*q+31
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = 2*q+31
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

theorem clear_base (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) :
    setTape (bank (q := q) source ss op oe ps es ws ctrl) baseSlot
      (fun _ => blank) 0 = bank source ss op oe ps es none ctrl := by
  unfold total
  rw [baseSlot,bank,SharedPlacementAlphabet.setTape_append_left]
  unfold bank
  apply congrArg (fun v : Tapes (count q) a => v.append ctrl)
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : i.val = 2*q+31
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi] <;> (try split_ifs) <;> first | omega | rfl
  · funext i
    by_cases hi : i.val = 2*q+31
    all_goals simp (disch := omega) [setTape,Function.update_apply,RadixHighBlockJoinBank.bank,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
      RadixHighBlockJoinBank.baseSlot,RadixHighBlockJoinBank.spectatorSlot,
      RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      Fin.ext_iff,hi,encoded_binary] <;> (try split_ifs) <;> first | omega | rfl

end
end IntegerMultBounds.Machine.RadixHighBlockJoinSetup
