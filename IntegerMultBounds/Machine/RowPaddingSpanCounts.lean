import IntegerMultBounds.Machine.BoundedProductDescriptor
import IntegerMultBounds.Machine.BinarySubReuse
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physical valid-span and padding-span descriptor construction. The original
row count, rounded row count and row length are immutable inputs. Subtraction
may retain high zeros; product synthesis canonicalizes its output directly.
All temporary descriptors and all marker setup and cleanup are charged. -/
namespace IntegerMultBounds.Machine.RowPaddingSpanCounts
variable {q : ℕ}
noncomputable section

private def head : Option (List Bool) → ℤ
  | none => 0
  | some _ => 1
private def tape : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some xs => RadixZeroFill.encodedBinary xs

/-- Slots: R, rounded R, L, difference scratch, valid span, padding span,
then three product work tapes. Every unspecified tape is wholly blank. -/
def bank (rs rps ls : List Bool) (diff valid pad : Option (List Bool)) : Tapes 9 q :=
  ⟨![1,1,1,head diff,head valid,head pad,0,0,0],
   ![RadixZeroFill.encodedBinary rs,RadixZeroFill.encodedBinary rps,
     RadixZeroFill.encodedBinary ls,tape diff,tape valid,tape pad,
     fun _ => blank,fun _ => blank,fun _ => blank]⟩

def input (rs rps ls : List Bool) : Tapes 9 q := bank rs rps ls none none none

def validBits (R L : ℕ) := BoundedProductDescriptor.bits R L
def padBits (R R' L : ℕ) := BoundedProductDescriptor.bits (R'-R) L

def output (rs rps ls : List Bool) (R R' L : ℕ) : Tapes 9 q :=
  bank rs rps ls none (some (validBits R L)) (some (padBits R R' L))

def subPlacement : Fin (3+6) ≃ Fin 9 where
  toFun := ![1,0,3,2,4,5,6,7,8]
  invFun := ![1,0,3,2,4,5,6,7,8]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def validPlacement : Fin (6+3) ≃ Fin 9 where
  toFun := ![6,4,7,2,8,0,1,3,5]
  invFun := ![5,6,3,7,1,8,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def padPlacement : Fin (6+3) ≃ Fin 9 where
  toFun := ![6,5,7,2,8,3,0,1,4]
  invFun := ![6,7,3,5,8,1,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def subProgram : Program 9 13 q := Placement.placed
  (Alphabet.program RadixToBinary.binaryEncoding BinarySubReuse.program) subPlacement

def validProgram : Program 9 40 q :=
  Placement.placed BoundedProductDescriptor.program validPlacement

def padProgram : Program 9 40 q :=
  Placement.placed BoundedProductDescriptor.program padPlacement

/-- One fixed 97-state program, independent of all three input values. -/
def program : Program 9 97 q :=
  seq (seq (seq subProgram validProgram) padProgram) (BinaryDescriptorCleanupList.oneProgram 3)

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r q}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t q) (small small' : Tapes s q)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

theorem sub_hoare (rs rps ls : List Bool) :
    HoareTime (subProgram (q := q)) (fun v => v = input rs rps ls)
      (fun v => v = bank rs rps ls (some (BinarySubReuse.difference rps rs)) none none)
      (4*BinarySubReuse.width rps rs+14) := by
  have h := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q))
    (BinarySubReuse.sub_hoare rps rs)
  have hh : HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinarySubReuse.program)
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank rps rs (fun _ => blank) 1 1 0))
      (fun v => v = Alphabet.mapTapes RadixToBinary.binaryEncoding
        (BinarySubReuse.bank rps rs (CountedCopyReuse.binary (BinarySubReuse.difference rps rs)) 1 1 1))
      (4*BinarySubReuse.width rps rs+14) :=
    h.consequence (fun _ h => ⟨_,rfl,h⟩) (by rintro v ⟨w,rfl,h⟩; exact h) le_rfl
  apply placed_exact subPlacement _ _ _ _ _ _ _ hh
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem valid_hoare (rs rps ls ds : List Bool) (R R' L : ℕ)
    (hL : 0 < L) (hl : Counter.value ls = L) (hr : Counter.value rs = R)
    (hR : R ≤ R') (wl : ls.length ≤ L+1) (wr : rs.length ≤ R'+1) :
    HoareTime (validProgram (q := q))
      (fun v => v = bank rs rps ls (some ds) none none)
      (fun v => v = bank rs rps ls (some ds) (some (validBits R L)) none)
      (53*(R'*L)+28) := by
  apply placed_exact validPlacement _ _ _ _ _ _ _
    (BoundedProductDescriptor.construct_hoare ls rs R L R' hL hl hr hR wl wr)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem pad_hoare (rs rps ls ds : List Bool) (R R' L : ℕ)
    (hL : 0 < L) (hl : Counter.value ls = L) (hd : Counter.value ds = R'-R)
    (wl : ls.length ≤ L+1) (wd : ds.length ≤ R'+1) :
    HoareTime (padProgram (q := q))
      (fun v => v = bank rs rps ls (some ds) (some (validBits R L)) none)
      (fun v => v = bank rs rps ls (some ds) (some (validBits R L)) (some (padBits R R' L)))
      (53*(R'*L)+28) := by
  apply placed_exact padPlacement _ _ _ _ _ _ _
    (BoundedProductDescriptor.construct_hoare ls ds (R'-R) L R' hL hl hd (Nat.sub_le _ _) wl wd)
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem clean_hoare (rs rps ls ds : List Bool) (R R' L : ℕ) :
    HoareTime (BinaryDescriptorCleanupList.oneProgram (a := q) (3 : Fin 9))
      (fun v => v = bank rs rps ls (some ds) (some (validBits R L)) (some (padBits R R' L)))
      (fun v => v = output rs rps ls R R' L) (2*ds.length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (3 : Fin 9)
    (bank (q := q) rs rps ls (some ds) (some (validBits R L)) (some (padBits R R' L))) ds
    (BinaryDescriptorStackRoundtrip.descriptor_encoded ds).symm rfl
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Both span counts are actually synthesized from the three preserved input
headers. Even zero padding is supported, and temporary tapes finish blank. -/
theorem construct_hoare (rs rps ls : List Bool) (R R' L : ℕ)
    (hr : Counter.value rs = R) (hp : Counter.value rps = R') (hl : Counter.value ls = L)
    (cr : GrowingCounterData.Canonical rs) (cp : GrowingCounterData.Canonical rps)
    (cl : GrowingCounterData.Canonical ls) (hR : R ≤ R') (hL : 0 < L) :
    HoareTime (program (q := q)) (fun v => v = input rs rps ls)
      (fun v => v = output rs rps ls R R' L) (112*(R'*L)+83) := by
  have wr := GrowingCounterData.canonical_width rs cr
  have wp := GrowingCounterData.canonical_width rps cp
  have wl := GrowingCounterData.canonical_width ls cl
  have lr := Nat.log2_le_self (Counter.value rs)
  have lp := Nat.log2_le_self (Counter.value rps)
  have ll := Nat.log2_le_self (Counter.value ls)
  rw [hr] at wr lr
  rw [hp] at wp lp
  rw [hl] at wl ll
  have hd := BinarySubReuse.difference_value rps rs (by omega)
  rw [hr,hp] at hd
  have wd := BinarySubReuse.difference_length rps rs
  have h := (((sub_hoare (q := q) rs rps ls).seq
    (valid_hoare rs rps ls _ R R' L hL hl hr hR (by omega) (by omega))).seq
    (pad_hoare rs rps ls _ R R' L hL hl hd (by omega) (by omega))).seq
    (clean_hoare rs rps ls _ R R' L)
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  have hm : R' ≤ R'*L := Nat.le_mul_of_pos_right _ hL
  dsimp [BinarySubReuse.width]
  omega

theorem valid_value (R L : ℕ) : Counter.value (validBits R L) = R*L :=
  BoundedProductDescriptor.bits_value _ _

theorem pad_value (R R' L : ℕ) : Counter.value (padBits R R' L) = (R'-R)*L :=
  BoundedProductDescriptor.bits_value _ _

theorem span_sum (R R' L : ℕ) (hR : R ≤ R') :
    Counter.value (validBits R L)+Counter.value (padBits R R' L) = R'*L := by
  rw [valid_value,pad_value,← Nat.add_mul,Nat.add_sub_of_le hR]

theorem valid_canonical (R L : ℕ) : GrowingCounterData.Canonical (validBits R L) :=
  BoundedProductDescriptor.bits_canonical _ _

theorem pad_canonical (R R' L : ℕ) : GrowingCounterData.Canonical (padBits R R' L) :=
  BoundedProductDescriptor.bits_canonical _ _

/-- The two generated descriptors are ready for the counted padding primitive. -/
theorem ready (rs rps ls : List Bool) (R R' L : ℕ) :
    (output (q := q) rs rps ls R R' L).head 4 = 1 ∧
    (output (q := q) rs rps ls R R' L).tape 4 = RadixZeroFill.encodedBinary (validBits R L) ∧
    (output (q := q) rs rps ls R R' L).head 5 = 1 ∧
    (output (q := q) rs rps ls R R' L).tape 5 = RadixZeroFill.encodedBinary (padBits R R' L) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem valid_positive (R L : ℕ) (hR : 0 < R) (hL : 0 < L) :
    0 < Counter.value (validBits R L) := by
  rw [valid_value]
  exact Nat.mul_pos hR hL

end
end IntegerMultBounds.Machine.RowPaddingSpanCounts
