import IntegerMultBounds.Machine.FixedBasePowerUntilRange

/-! Paid numerical range preparation from the sole runtime binary width.
The machine constructs 2^u, then the least enclosing fixed-radix power and
its exponent, retaining the original width and clearing every scratch tape. -/
namespace IntegerMultBounds.Machine.RadixRangeDescriptors
noncomputable section

def exponent (radix u : ℕ) := Nat.clog radix (2^u)
def binaryBits (u : ℕ) := FixedBasePowerStep.bits 2 u
def radixBits (radix u : ℕ) := FixedBasePowerStep.bits radix (exponent radix u)
def exponentBits (radix u : ℕ) := FixedBasePowerUntil.counter (exponent radix u)

def input (us : List Bool) : Tapes 12 0 :=
  (FixedBasePowerDescriptor.input us).append (SharedBank.empty 4 0)

def middle (u : ℕ) (us : List Bool) : Tapes 12 0 :=
  (FixedBasePowerDescriptor.output 2 u us).append (SharedBank.empty 4 0)

/-- Retained input width7; constructed binary range5, radix range10,
radix width11. All other tapes are wholly blank at head zero. -/
def output (radix u : ℕ) (us : List Bool) : Tapes 12 0 :=
  ⟨fun i => if i.val = 5 ∨ i.val = 7 ∨ i.val = 10 ∨ i.val = 11 then 1 else 0,
    fun i => match i.val with
      | 5 => RadixZeroFill.encodedBinary (binaryBits u)
      | 7 => BinaryDescriptorStack.descriptor us
      | 10 => RadixZeroFill.encodedBinary (radixBits radix u)
      | 11 => BinaryDescriptorStack.descriptor (exponentBits radix u)
      | _ => fun _ => blank⟩

def placement : Fin (9+3) ≃ Fin 12 where
  toFun := ![0,1,2,3,4,10,5,11,6,7,8,9]
  invFun := ![0,1,2,3,4,6,8,9,10,11,5,7]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem active_middle (u : ℕ) (us : List Bool) :
    Placement.active placement (middle u us) = FixedBasePowerUntil.input (binaryBits u) := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem active_output (radix u : ℕ) (us : List Bool) :
    Placement.active placement (output radix u us) =
      FixedBasePowerUntil.output radix (exponent radix u) (binaryBits u) := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem extra_output (radix u : ℕ) (us : List Bool) :
    Placement.extra placement (middle u us) = Placement.extra placement (output radix u us) := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · have hb : RadixZeroFill.encodedBinary (q := 0) us = CountedLoopReuseAlphabet.binary us := by
        change (fun z => (RadixToBinary.binaryEncoding (q := 0)).encode (CountedCopyReuse.binary us z)) = _
        exact CountedLoopReuseAlphabet.encoding_binary (a := 0) us
      exact hb.symm.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded us).symm
    · rfl
    · rfl

def program (radix : ℕ) := seq (extend (FixedBasePowerDescriptor.program (q := 0) 2) 4)
  (Placement.placed (FixedBasePowerUntil.program (q := 0) radix) placement)

def constant (radix : ℕ) :=
  FixedBasePowerDescriptor.constant 2+FixedBasePowerUntil.constant radix*radix+1

theorem construct_hoare (radix u : ℕ) (hr : 2 ≤ radix) (us : List Bool)
    (hu : Counter.value us = u) (cu : GrowingCounterData.Canonical us) :
    HoareTime (program radix) (fun v => v = input us) (fun v => v = output radix u us)
      (constant radix*2^u) := by
  have hfirst := hoare_extend_eq (FixedBasePowerDescriptor.constructs_linear (q := 0) 2 u (by omega) us hu cu)
    (SharedBank.empty 4 0)
  have hpower := FixedBasePowerUntilRange.constructs_threshold_linear (q := 0) radix (2^u) hr
    (Nat.two_pow_pos u) (binaryBits u) (FixedBasePowerStep.bits_value 2 u) (FixedBasePowerStep.bits_canonical 2 u)
  have hplaced := Placement.hoare_at hpower placement (middle u us) (active_middle u us)
  have hsecond : HoareTime (Placement.placed (FixedBasePowerUntil.program (q := 0) radix) placement)
      (fun v => v = middle u us) (fun v => v = output radix u us)
      ((FixedBasePowerUntil.constant radix*radix)*2^u) := by
    apply hplaced.consequence (fun _ h => h) _ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    rw [Placement.replace,extra_output radix u us]
    have ha := active_output radix u us
    unfold exponent at ha
    rw [← ha]
    exact Placement.view _ _
  apply (hfirst.seq hsecond).consequence (fun _ h => h) (fun _ h => h)
  have hN : 1 ≤ 2^u := Nat.one_le_iff_ne_zero.mpr (Nat.two_pow_pos u).ne'
  unfold constant
  nlinarith

theorem binary_value (u : ℕ) : Counter.value (binaryBits u) = 2^u := FixedBasePowerStep.bits_value 2 u
theorem radix_value (radix u : ℕ) : Counter.value (radixBits radix u) = radix^exponent radix u :=
  FixedBasePowerStep.bits_value radix _
theorem exponent_value (radix u : ℕ) : Counter.value (exponentBits radix u) = exponent radix u :=
  FixedBasePowerUntil.counter_value _

theorem binary_canonical (u : ℕ) : GrowingCounterData.Canonical (binaryBits u) :=
  FixedBasePowerStep.bits_canonical 2 u
theorem radix_canonical (radix u : ℕ) : GrowingCounterData.Canonical (radixBits radix u) :=
  FixedBasePowerStep.bits_canonical radix _
theorem exponent_canonical (radix u : ℕ) : GrowingCounterData.Canonical (exponentBits radix u) :=
  FixedBasePowerUntil.counter_canonical _

theorem range_bounds (radix u : ℕ) (hr : 2 ≤ radix) :
    2^u ≤ radix^exponent radix u ∧ radix^exponent radix u < radix*2^u :=
  ⟨FixedBasePowerUntilBound.dominates radix (2^u) hr,
    FixedBasePowerUntilRange.final_power_lt radix (2^u) hr (Nat.two_pow_pos u)⟩

theorem exponent_le (radix u : ℕ) (hr : 2 ≤ radix) : exponent radix u ≤ u :=
  (Nat.clog_le_iff_le_pow (by omega)).mpr (Nat.pow_le_pow_left hr u)

def cleanupSlots : List (Fin 12) := [5,10,11]
def cleanupWords (radix u : ℕ) (i : Fin 12) : List Bool := match i.val with
  | 5 => binaryBits u | 10 => radixBits radix u | 11 => exponentBits radix u | _ => []
def cleanupProgram := BinaryDescriptorCleanupList.program (a := 0) (by decide : 0 < 12) cleanupSlots

theorem cleanup_hoare (radix u : ℕ) (us : List Bool) :
    HoareTime cleanupProgram (fun v => v = output radix u us) (fun v => v = input us)
      (BinaryDescriptorCleanupList.cost cleanupSlots (cleanupWords radix u)) := by
  have h := BinaryDescriptorCleanupList.cleanup_hoare (a := 0) (by decide : 0 < 12)
    cleanupSlots (by decide) (cleanupWords radix u) (output radix u us) (by
      intro i hi
      simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl
      all_goals first | exact ⟨rfl,rfl⟩ | exact ⟨rfl,(BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm⟩)
  have he : BinaryDescriptorCleanupList.cleared cleanupSlots (output radix u us) = input us := by
    have hb : BinaryDescriptorStack.descriptor (a := 0) us = CountedLoopReuseAlphabet.binary us := by
      rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
      change (fun z => (RadixToBinary.binaryEncoding (q := 0)).encode (CountedCopyReuse.binary us z)) = _
      exact CountedLoopReuseAlphabet.encoding_binary (a := 0) us
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> first | rfl | exact hb
  rw [he] at h
  exact h

private theorem length_le (xs : List Bool) (cx : GrowingCounterData.Canonical xs)
    (L : ℕ) (hL : 0 < L) (hx : Counter.value xs ≤ L) : xs.length ≤ 2*L := by
  have hw := GrowingCounterData.canonical_width xs cx
  have hl := Nat.log2_le_self (Counter.value xs)
  omega

theorem cleanup_cost_bound (radix u : ℕ) (hr : 2 ≤ radix) :
    BinaryDescriptorCleanupList.cost cleanupSlots (cleanupWords radix u) ≤ (12*radix+15)*2^u := by
  have hN := Nat.two_pow_pos u
  have hL : 0 < radix*2^u := Nat.mul_pos (by omega) hN
  have hn : 2^u ≤ radix*2^u := by nlinarith
  have he := exponent_le radix u hr
  have hu := FixedBasePowerDescriptor.depth_le_power 2 u (by omega)
  have hm := (range_bounds radix u hr).2.le
  have hw : ∀ i ∈ cleanupSlots, (cleanupWords radix u i).length ≤ 2*(radix*2^u) := by
    intro i hi
    simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact length_le _ (binary_canonical u) _ hL (by rw [binary_value]; exact hn)
    · exact length_le _ (radix_canonical radix u) _ hL (by rw [radix_value]; exact hm)
    · exact length_le _ (exponent_canonical radix u) _ hL (by rw [exponent_value]; omega)
  have hc := BinaryDescriptorCleanupList.cost_le cleanupSlots (cleanupWords radix u) (2*(radix*2^u)) hw
  simp only [cleanupSlots,List.length_cons,List.length_nil] at hc
  unfold cleanupSlots
  nlinarith

theorem cleanup_linear (radix u : ℕ) (hr : 2 ≤ radix) (us : List Bool) :
    HoareTime cleanupProgram (fun v => v = output radix u us) (fun v => v = input us)
      ((12*radix+15)*2^u) :=
  (cleanup_hoare radix u us).consequence (fun _ h => h) (fun _ h => h) (cleanup_cost_bound radix u hr)

end
end IntegerMultBounds.Machine.RadixRangeDescriptors
