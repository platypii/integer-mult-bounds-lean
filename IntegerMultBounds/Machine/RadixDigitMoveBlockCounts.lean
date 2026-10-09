import IntegerMultBounds.Machine.RadixDigitMoveCounts

/-! Physical dimension products for digit movement with an arbitrary trailing
block. Only canonical P,S,E are supplied; S*E and P*S are generated and cleaned. -/
namespace IntegerMultBounds.Machine.RadixDigitMoveBlockCounts
variable {a : ℕ}
noncomputable section

private def hd : Option (List Bool) → ℤ | none => 0 | some _ => 1
private def tp : Option (List Bool) → ℤ → Fin (a+4)
  | none => fun _ => blank
  | some bs => RadixZeroFill.encodedBinary bs

/-- P,S,E0–2 retained; S*E3/P*S4 generated; spare/inner/outer5–7. -/
def bank (ps ss es : List Bool) (se ps' : Option (List Bool)) : Tapes 8 a :=
  ⟨(fun i => match i.val with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | 3 => hd se
    | 4 => hd ps'
    | _ => 0),
   (fun i => match i.val with
    | 0 => RadixZeroFill.encodedBinary ps
    | 1 => RadixZeroFill.encodedBinary ss
    | 2 => RadixZeroFill.encodedBinary es
    | 3 => tp se
    | 4 => tp ps'
    | _ => fun _ => blank)⟩

def input (ps ss es : List Bool) : Tapes 8 a := bank ps ss es none none
def seBits (S E : ℕ) := BoundedProductDescriptor.bits S E
def psBits (P S : ℕ) := BoundedProductDescriptor.bits P S
def output (ps ss es : List Bool) (P S E : ℕ) : Tapes 8 a :=
  bank ps ss es (some (seBits S E)) (some (psBits P S))

def sePlacement : Fin (6+2) ≃ Fin 8 where
  toFun := ![5,3,6,2,7,1,0,4]
  invFun := ![6,5,3,1,7,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def psPlacement : Fin (6+2) ≃ Fin 8 where
  toFun := ![5,4,6,1,7,0,2,3]
  invFun := ![5,3,6,7,1,0,2,4]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def seProgram : Program 8 40 a := Placement.placed BoundedProductDescriptor.program sePlacement
def psProgram : Program 8 40 a := Placement.placed BoundedProductDescriptor.program psPlacement
def program : Program 8 80 a := seq seProgram psProgram
def cleanupProgram : Program 8 8 a := seq (BinaryDescriptorCleanupList.oneProgram 3) (BinaryDescriptorCleanupList.oneProgram 4)

theorem se_value (S E : ℕ) : Counter.value (seBits S E) = S*E := BoundedProductDescriptor.bits_value _ _
theorem ps_value (P S : ℕ) : Counter.value (psBits P S) = P*S := BoundedProductDescriptor.bits_value _ _
theorem se_canonical (S E : ℕ) : GrowingCounterData.Canonical (seBits S E) := BoundedProductDescriptor.bits_canonical _ _
theorem ps_canonical (P S : ℕ) : GrowingCounterData.Canonical (psBits P S) := BoundedProductDescriptor.bits_canonical _ _

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

theorem se_hoare (ps ss es : List Bool) (S E : ℕ) (hE : 0 < E)
    (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cs : GrowingCounterData.Canonical ss) (ce : GrowingCounterData.Canonical es) :
    HoareTime (seProgram (a := a)) (fun v => v = input ps ss es)
      (fun v => v = bank ps ss es (some (seBits S E)) none) (53*(S*E)+28) := by
  have ws := GrowingCounterData.canonical_width ss cs
  have we := GrowingCounterData.canonical_width es ce
  have ls := Nat.log2_le_self (Counter.value ss)
  have le := Nat.log2_le_self (Counter.value es)
  apply placed_exact sePlacement _ _ _ _ _ _ _
    (BoundedProductDescriptor.construct_hoare es ss S E S hE he hs le_rfl (by omega) (by omega))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem ps_hoare (ps ss es : List Bool) (P S E : ℕ) (hS : 0 < S)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss) :
    HoareTime (psProgram (a := a)) (fun v => v = bank ps ss es (some (seBits S E)) none)
      (fun v => v = output ps ss es P S E) (53*(P*S)+28) := by
  have wp := GrowingCounterData.canonical_width ps cp
  have ws := GrowingCounterData.canonical_width ss cs
  have lp := Nat.log2_le_self (Counter.value ps)
  have ls := Nat.log2_le_self (Counter.value ss)
  apply placed_exact psPlacement _ _ _ _ _ _ _
    (BoundedProductDescriptor.construct_hoare ss ps P S P hS hs hp le_rfl (by omega) (by omega))
  all_goals apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem construct_hoare (ps ss es : List Bool) (P S E : ℕ)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value ps = P) (hs : Counter.value ss = S) (he : Counter.value es = E)
    (cp : GrowingCounterData.Canonical ps) (cs : GrowingCounterData.Canonical ss)
    (ce : GrowingCounterData.Canonical es) :
    HoareTime (program (a := a)) (fun v => v = input ps ss es)
      (fun v => v = output ps ss es P S E) (163*(P*S*E)) := by
  have h := (se_hoare (a := a) ps ss es S E hE hs he cs ce).seq
    (ps_hoare ps ss es P S E hS hp hs cp cs)
  apply h.consequence (fun _ h => h) (fun _ h => h)
  have hv := Nat.mul_pos (Nat.mul_pos hP hS) hE
  have h1 := Nat.le_mul_of_pos_left (S*E) hP
  have h2 := Nat.le_mul_of_pos_right (P*S) hE
  nlinarith

theorem cleanup_hoare (ps ss es : List Bool) (P S E : ℕ)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E) :
    HoareTime (cleanupProgram (a := a)) (fun v => v = output ps ss es P S E)
      (fun v => v = input ps ss es) (20*(P*S*E)) := by
  have h := BinaryDescriptorCleanupList.one_hoare (3 : Fin 8) (output (a := a) ps ss es P S E) (seBits S E)
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm rfl
  have heq : SharedPlacementAlphabet.setTape (output (a := a) ps ss es P S E) 3 (fun _ => blank) 0 =
      bank ps ss es none (some (psBits P S)) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [heq] at h
  have hh := BinaryDescriptorCleanupList.one_hoare (4 : Fin 8)
    (bank (a := a) ps ss es none (some (psBits P S))) (psBits P S)
    (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm rfl
  have heq' : SharedPlacementAlphabet.setTape (bank (a := a) ps ss es none (some (psBits P S)))
      4 (fun _ => blank) 0 = input ps ss es := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [heq'] at hh
  have ws := GrowingCounterData.canonical_width _ (se_canonical S E)
  have wp := GrowingCounterData.canonical_width _ (ps_canonical P S)
  have ls := Nat.log2_le_self (Counter.value (seBits S E))
  have lp := Nat.log2_le_self (Counter.value (psBits P S))
  rw [se_value] at ws ls
  rw [ps_value] at wp lp
  apply (h.seq hh).consequence (fun _ h => h) (fun _ h => h)
  have hv := Nat.mul_pos (Nat.mul_pos hP hS) hE
  have h1 := Nat.le_mul_of_pos_left (S*E) hP
  have h2 := Nat.le_mul_of_pos_right (P*S) hE
  nlinarith

end
end IntegerMultBounds.Machine.RadixDigitMoveBlockCounts
