import IntegerMultBounds.Machine.BoundedProductDescriptor
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Four actual digit-redistribution control descriptors from only canonical
S/P inputs. The fixed one and product P*S are physically written, and their
later erasure is charged. All three product work tapes finish blank/head0. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveCounts
variable {a : ℕ}
noncomputable section

def oneBits := RecursiveChildQuotientsConstant.bits 1
def productBits (P S : ℕ) := BoundedProductDescriptor.bits P S

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- Slots S/P0–1 retained; one2, P*S3 generated; spare/inner/outer4–6. -/
def bank (ss ps : List Bool) (one product : Option (List Bool)) : Tapes 7 a :=
  ⟨(fun i => match i.val with | 0 => 1 | 1 => 1 | 2 => hd one | 3 => hd product | _ => 0),
    (fun i => match i.val with
      | 0 => RadixZeroFill.encodedBinary ss
      | 1 => RadixZeroFill.encodedBinary ps
      | 2 => tp one
      | 3 => tp product
      | _ => fun _ => blank)⟩

def input (ss ps : List Bool) : Tapes 7 a := bank ss ps none none
def output (ss ps : List Bool) (P S : ℕ) : Tapes 7 a :=
  bank ss ps (some oneBits) (some (productBits P S))

def productPlacement : Fin (6+1) ≃ Fin 7 where
  toFun := ![4,3,5,0,6,1,2]
  invFun := ![3,5,6,1,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def oneProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (2 : Fin 7))
def productProgram : Program 7 40 a := Placement.placed BoundedProductDescriptor.program productPlacement
def program := seq (oneProgram (a := a)) productProgram
def cleanupProgram : Program 7 8 a := seq (BinaryDescriptorCleanupList.oneProgram 2)
  (BinaryDescriptorCleanupList.oneProgram 3)

theorem one_value : Counter.value oneBits = 1 := RecursiveChildQuotientsConstant.bits_value _
theorem one_canonical : GrowingCounterData.Canonical oneBits := RecursiveChildQuotientsConstant.bits_canonical _
theorem one_length : oneBits.length = 1 := rfl
theorem product_value (P S : ℕ) : Counter.value (productBits P S) = P*S :=
  BoundedProductDescriptor.bits_value _ _
theorem product_canonical (P S : ℕ) : GrowingCounterData.Canonical (productBits P S) :=
  BoundedProductDescriptor.bits_canonical _ _

/-- The generated descriptors exactly match the initialized digit core's
arbitrary-alphabet binary control representation. -/
theorem encoded_binary (bs : List Bool) : RadixZeroFill.encodedBinary (q := a) bs =
    CountedLoopReuseAlphabet.binary bs := by
  exact CountedLoopReuseAlphabet.encoding_binary bs

theorem one_hoare (ss ps : List Bool) :
    HoareTime (oneProgram (a := a)) (fun v => v = input ss ps)
      (fun v => v = bank ss ps (some oneBits) none) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (2 : Fin 7)) (input ss ps) (by
      rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ hh => hh) _ (by rfl)
  rintro v ⟨small,rfl,rfl⟩
  have he := FiniteReturnStackAt.replace_bank (2 : Fin 7) (input (a := a) ss ps)
    (BinaryDescriptorStack.descriptor oneBits) 1
  change Placement.replace _ _ (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor oneBits) 1) = _
  rw [he]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
  exact BinaryDescriptorStackRoundtrip.descriptor_encoded oneBits

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r a}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t a) (small small' : Tapes s a)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem product_hoare (ss ps : List Bool) (P S : ℕ) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (productProgram (a := a)) (fun v => v = bank ss ps (some oneBits) none)
      (fun v => v = output ss ps P S) (53*(P*S)+28) := by
  have ws := GrowingCounterData.canonical_width ss cs
  have wp := GrowingCounterData.canonical_width ps cp
  have ls := Nat.log2_le_self (Counter.value ss)
  have lp := Nat.log2_le_self (Counter.value ps)
  apply placed_exact productPlacement _ _ _ _ _ _ _
    (BoundedProductDescriptor.construct_hoare ss ps P S P hS hs hp le_rfl (by omega) (by omega))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The whole fixed finite constructor uses only supplied S/P descriptors,
including the physical constant writer and the paid product scratch setup. -/
theorem construct_hoare (ss ps : List Bool) (P S : ℕ) (hP : 0 < P) (hS : 0 < S)
    (hs : Counter.value ss = S) (hp : Counter.value ps = P)
    (cs : GrowingCounterData.Canonical ss) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (program (a := a)) (fun v => v = input ss ps)
      (fun v => v = output ss ps P S) (91*(P*S)) := by
  have h := (one_hoare (a := a) ss ps).seq (product_hoare ss ps P S hS hs hp cs cp)
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh) (by have hv := Nat.mul_pos hP hS; omega)

/-- Erase both generated descriptors without changing either immutable input.
All four control heads and the three scratch heads are exact at both ends. -/
theorem cleanup_hoare (ss ps : List Bool) (P S : ℕ) (hP : 0 < P) (hS : 0 < S) :
    HoareTime (cleanupProgram (a := a)) (fun v => v = output ss ps P S)
      (fun v => v = input ss ps) (15*(P*S)) := by
  have h := BinaryDescriptorCleanupList.one_hoare (2 : Fin 7) (output (a := a) ss ps P S) oneBits
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm rfl
  have he : SharedPlacementAlphabet.setTape (output (a := a) ss ps P S) 2 (fun _ => blank) 0 =
      bank ss ps none (some (productBits P S)) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  have hh := BinaryDescriptorCleanupList.one_hoare (3 : Fin 7)
    (bank (a := a) ss ps none (some (productBits P S))) (productBits P S)
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm rfl
  have he' : SharedPlacementAlphabet.setTape (bank (a := a) ss ps none (some (productBits P S)))
      3 (fun _ => blank) 0 = input ss ps := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he'] at hh
  have hw := GrowingCounterData.canonical_width _ (product_canonical P S)
  have hl := Nat.log2_le_self (Counter.value (productBits P S))
  rw [product_value] at hw hl
  exact (h.seq hh).consequence (fun _ hv => hv) (fun _ hv => hv)
    (by rw [one_length]; have hp := Nat.mul_pos hP hS; omega)

end
end IntegerMultBounds.Machine.RadixDigitMoveCounts
