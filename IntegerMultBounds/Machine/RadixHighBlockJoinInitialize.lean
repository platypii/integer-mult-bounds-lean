import IntegerMultBounds.Machine.RadixHighBlockJoinSetup

/-! Complete physical high-block join/separate preparation from sole original
P/S/E descriptors and a retained rho. Every generated power/product is created
on blank tape; the temporary q^rho is erased before the body begins. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinInitialize
noncomputable section
open RadixHighBlockJoinSetup
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {q a : ℕ}

def controls (clock : ℤ → Fin (a+4)) (p : ℤ) (rs : List Bool) : Tapes 2 a :=
  CountedLoopReuseAlphabet.controls clock (CountedLoopReuseAlphabet.binary rs) p 1

def input (source : ℤ → Fin (a+4)) (ss op oe : List Bool) (ctrl : Tapes 2 a) :=
  bank (q := q) source ss op oe none none none ctrl

def selected (growPrefix : Bool) (op oe : List Bool) := if growPrefix then op else oe

def copied (growPrefix : Bool) (source : ℤ → Fin (a+4)) (ss op oe : List Bool) (ws : Option (List Bool)) (ctrl : Tapes 2 a) :=
  bank (q := q) source ss op oe (if growPrefix then none else some op) (if growPrefix then some oe else none) ws ctrl

def prepared (growPrefix : Bool) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (N r : ℕ) (ctrl : Tapes 2 a) :=
  bank (q := q) source ss op oe (if growPrefix then some (grownBits (q := q) N r) else some op)
    (if growPrefix then some oe else some (grownBits (q := q) N r)) (some (bits q)) ctrl

private theorem copy_ne (g : Bool) : originalSlot (q := q) (!g) ≠ workingSlot (!g) := by
  intro he
  have hv := congrArg Fin.val he
  cases g <;> simp [originalSlot,workingSlot,originalPrefixSlot,originalSuffixSlot,prefixSlot,suffixSlot,
    RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
    RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot] at hv <;> omega

def copyProgram (g : Bool) := BinaryDescriptorInstall.program a
  (originalSlot (q := q) (!g)) (workingSlot (!g)) (copy_ne g)
def baseProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) q)
  (FiniteReturnStackAt.placement (baseSlot (q := q)))
def erasePower := BinaryDescriptorCleanupList.oneProgram (a := a) (scratchSlot (q := q) 0)
def program (g : Bool) := seq (seq (seq (seq (copyProgram (q := q) (a := a) g) baseProgram)
  powerProgram) (productProgram g)) erasePower

theorem copy_hoare (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe : List Bool) (ctrl : Tapes 2 a) :
    HoareTime (copyProgram (q := q) (a := a) g) (fun v => v = input source ss op oe ctrl)
      (fun v => v = copied g source ss op oe none ctrl) (2*(selected (!g) op oe).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (originalSlot (q := q) (!g)) (workingSlot (!g)) (copy_ne g)
    (input (q := q) source ss op oe ctrl) (selected (!g) op oe) ?_ ?_ ?_ ?_
  · apply h.consequence (fun _ h => h) _ le_rfl
    rintro v rfl
    cases g
    · exact set_prefix source ss op oe op none none none ctrl
    · exact set_suffix source ss op oe oe none none none ctrl
  all_goals cases g
  · change (bank (q := q) source ss op oe none none none ctrl).tape (Fin.castAdd 2 RadixHighBlockJoinBank.originalPrefixSlot) = RadixZeroFill.encodedBinary op
    rw [read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.originalPrefixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).tape (Fin.castAdd 2 RadixHighBlockJoinBank.originalSuffixSlot) = RadixZeroFill.encodedBinary oe
    rw [read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.originalSuffixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).head (Fin.castAdd 2 RadixHighBlockJoinBank.originalPrefixSlot) = 1
    rw [read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.originalPrefixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).head (Fin.castAdd 2 RadixHighBlockJoinBank.originalSuffixSlot) = 1
    rw [read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.originalSuffixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).tape (Fin.castAdd 2 RadixHighBlockJoinBank.prefixSlot) = (fun _ => blank)
    rw [read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.prefixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).tape (Fin.castAdd 2 RadixHighBlockJoinBank.suffixSlot) = (fun _ => blank)
    rw [read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.suffixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).head (Fin.castAdd 2 RadixHighBlockJoinBank.prefixSlot) = 0
    rw [read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.prefixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]
  · change (bank (q := q) source ss op oe none none none ctrl).head (Fin.castAdd 2 RadixHighBlockJoinBank.suffixSlot) = 0
    rw [read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.suffixSlot,optionHead,optionTape,encoded_binary,ite_eq_right,ite_eq_left]

theorem base_hoare (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es : Option (List Bool)) (ctrl : Tapes 2 a) :
    HoareTime (baseProgram (q := q) (a := a)) (fun v => v = bank source ss op oe ps es none ctrl)
      (fun v => v = bank source ss op oe ps es (some (bits q)) ctrl) (RecursiveChildQuotientsConstant.cost q) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) q)
    (FiniteReturnStackAt.placement (baseSlot (q := q))) (bank source ss op oe ps es none ctrl) (by
      rw [FiniteReturnStackAt.active_bank]
      simp only [baseSlot,read_head,read_tape]
      simp (disch := omega) [read_head,read_tape,optionHead,optionTape,
      RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.baseSlot,
      RadixHighBlockJoinBank.spectatorSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      RadixHighBlockJoinBank.scratchSlot,-Fin.val_eq_zero_iff,ite_eq_right,ite_eq_left])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank,← encoded_descriptor]
  exact set_base source ss op oe (bits q) ps es none ctrl

private theorem scratch_view (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (ps es ws : Option (List Bool)) (ctrl : Tapes 2 a) (i : Fin 13) :
    (bank (q := q) source ss op oe ps es ws ctrl).head (scratchSlot i) = 0 ∧
    (bank (q := q) source ss op oe ps es ws ctrl).tape (scratchSlot i) = (fun _ => blank) := by
  have hi := i.isLt
  have h0 : 2*q+18+i.val ≠ 0 := by omega
  have h1 : 2*q+18+i.val ≠ q+4 := by omega
  have h2 : 2*q+18+i.val ≠ q+5 := by omega
  have h3 : 2*q+18+i.val ≠ 2*q+31 := by omega
  have h4 : 2*q+18+i.val ≠ 2*q+14 := by omega
  have h5 : 2*q+18+i.val ≠ 2*q+32 := by omega
  have h6 : 2*q+18+i.val ≠ 2*q+33 := by omega
  simp only [scratchSlot,read_head,read_tape,RadixHighBlockJoinBank.scratchSlot,Fin.val_mk,
    h0,h1,h2,h3,h4,h5,h6,ite_false,false_or,and_self]

theorem active_power (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool) (ps es ws : Option (List Bool))
    (clock : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.active (powerPlacement (q := q)) (bank source ss op oe ps es ws (controls clock p rs)) =
      FixedBasePowerDescriptor.input rs := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp only [Placement.active,powerPlacement_active]
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 1) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 1).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 2) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 2).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 3) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 3).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 4) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 4).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 5) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 5).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 0) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 0).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head (scratchSlot 6) = 0
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 6).1
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).head exponentSlot = 1
      simp only [bank,exponentSlot,Tapes.append,Fin.addCases_right]
      rfl
  · funext i
    fin_cases i <;> simp only [Placement.active,powerPlacement_active]
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 1) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 1).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 2) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 2).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 3) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 3).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 4) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 4).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 5) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 5).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 0) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 0).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape (scratchSlot 6) = (fun _ => blank)
      exact (scratch_view source ss op oe ps es ws (controls clock p rs) 6).2
    · change (bank (q := q) source ss op oe ps es ws (controls clock p rs)).tape exponentSlot = CountedLoopReuseAlphabet.binary rs
      simp only [bank,exponentSlot,Tapes.append,Fin.addCases_right]
      rfl

private theorem set_comm {T : ℕ} (v : Tapes T a) (i j : Fin T) (hi : i ≠ j)
    (f g : ℤ → Fin (a+4)) (p r : ℤ) : setTape (setTape v i f p) j g r = setTape (setTape v j g r) i f p := by
  apply congrArg₂ Tapes.mk <;> funext k
  all_goals by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [setTape,Function.update_apply]

private theorem working_scratch_ne (g : Bool) : workingSlot (q := q) g ≠ scratchSlot 0 := by
  intro he
  have hv := congrArg Fin.val he
  cases g <;> simp [workingSlot,prefixSlot,suffixSlot,scratchSlot,RadixHighBlockJoinBank.prefixSlot,
    RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.scratchSlot] at hv <;> omega

theorem active_product (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (r : ℕ) (ctrl : Tapes 2 a) :
    Placement.active (productPlacement (q := q) g)
      (setTape (copied g source ss op oe (some (bits q)) ctrl) (scratchSlot 0)
        (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1) =
      BoundedProductDescriptor.input (powerBits (q := q) r) (selected g op oe) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals cases g <;> fin_cases i
  all_goals simp only [Placement.active,productPlacement_active]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 1) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (suffixSlot) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [suffixSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 2) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 0) = 1
    rw [Function.update_self]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 3) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).head (scratchSlot 0) 1 (originalSuffixSlot) = 1
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [originalSuffixSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 1) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (prefixSlot) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [prefixSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 2) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 0) = 1
    rw [Function.update_self]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (scratchSlot 3) = 0
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).head (scratchSlot 0) 1 (originalPrefixSlot) = 1
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [originalPrefixSlot,read_head]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 1) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (suffixSlot) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [suffixSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 2) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 0) = RadixZeroFill.encodedBinary (powerBits (q := q) r)
    rw [Function.update_self]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 3) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe (some op) none (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (originalSuffixSlot) = RadixZeroFill.encodedBinary oe
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [originalSuffixSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 1) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (prefixSlot) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [prefixSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 2) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 0) = RadixZeroFill.encodedBinary (powerBits (q := q) r)
    rw [Function.update_self]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (scratchSlot 3) = (fun _ => blank)
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [scratchSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]
  · change Function.update (bank (q := q) source ss op oe none (some oe) (some (bits q)) ctrl).tape (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) (originalPrefixSlot) = RadixZeroFill.encodedBinary op
    rw [Function.update_of_ne (by
      intro he
      have hv := congrArg Fin.val he
      simp [scratchSlot,prefixSlot,suffixSlot,originalPrefixSlot,originalSuffixSlot,
        RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,RadixHighBlockJoinBank.suffixSlot,
        RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot] at hv <;> omega)]
    simp only [originalPrefixSlot,read_tape]
    simp (disch := omega) [RadixHighBlockJoinBank.scratchSlot,RadixHighBlockJoinBank.prefixSlot,
      RadixHighBlockJoinBank.suffixSlot,RadixHighBlockJoinBank.originalPrefixSlot,RadixHighBlockJoinBank.originalSuffixSlot,
      optionHead,optionTape,ite_eq_right,ite_eq_left,encoded_binary,-Fin.val_eq_zero_iff]

theorem set_product (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe : List Bool)
    (N r : ℕ) (ctrl : Tapes 2 a) :
    setTape (setTape (copied (q := q) g source ss op oe (some (bits q)) ctrl) (scratchSlot 0)
      (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1) (workingSlot g)
      (RadixZeroFill.encodedBinary (grownBits (q := q) N r)) 1 =
    setTape (prepared g source ss op oe N r ctrl) (scratchSlot 0)
      (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1 := by
  rw [set_comm _ _ _ (working_scratch_ne g).symm]
  apply congrArg (fun v => setTape v (scratchSlot 0) (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1)
  cases g
  · exact set_suffix source ss op oe _ _ _ _ ctrl
  · exact set_prefix source ss op oe _ _ _ _ ctrl

theorem erase_power (source : ℤ → Fin (a+4)) (ss op oe : List Bool) (ps es ws : Option (List Bool))
    (ctrl : Tapes 2 a) (r : ℕ) :
    HoareTime (erasePower (q := q) (a := a))
      (fun v => v = setTape (bank source ss op oe ps es ws ctrl) (scratchSlot 0)
        (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1)
      (fun v => v = bank source ss op oe ps es ws ctrl) (2*(powerBits (q := q) r).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (scratchSlot (q := q) 0)
    (setTape (bank source ss op oe ps es ws ctrl) (scratchSlot 0)
      (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1) (powerBits (q := q) r)
    (by simp [setTape,encoded_descriptor]) (by simp [setTape])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  rw [SharedPlacementAlphabet.setTape_setTape]
  have ht := (scratch_view (q := q) source ss op oe ps es ws ctrl 0).2
  have hh := (scratch_view (q := q) source ss op oe ps es ws ctrl 0).1
  rw [← ht,← hh,SharedPlacementAlphabet.setTape_self]

/-- Total paid preparation budget, including all four sequencing steps. -/
def cost (q : ℕ) (g : Bool) (op oe : List Bool) (N r : ℕ) :=
  RecursiveChildQuotientsConstant.cost q + FixedBasePowerDescriptor.constant q*q^r +
    53*(N*q^r) + 2*(selected (!g) op oe).length + 2*(powerBits (q := q) r).length + 41

/-- Construct all working descriptors from their sole retained originals. -/
theorem initializes (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (clock : ℤ → Fin (a+4)) (p : ℤ) (N r : ℕ) (hq : 2 ≤ q)
    (hn : Counter.value (selected g op oe) = N)
    (cn : GrowingCounterData.Canonical (selected g op oe))
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a) g)
      (fun v => v = input source ss op oe (controls clock p rs))
      (fun v => v = prepared g source ss op oe N r (controls clock p rs))
      (cost q g op oe N r) := by
  let ctrl := controls clock p rs
  have hcopy := copy_hoare (q := q) g source ss op oe ctrl
  have hbase := base_hoare (q := q) source ss op oe
    (if g then none else some op) (if g then some oe else none) ctrl
  have hpower := power_hoare (copied g source ss op oe (some (bits q)) ctrl)
    r hq rs hr cr (active_power source ss op oe rs _ _ _ clock p)
  have hproduct := product_hoare g
    (setTape (copied g source ss op oe (some (bits q)) ctrl) (scratchSlot 0)
      (RadixZeroFill.encodedBinary (powerBits (q := q) r)) 1)
    N r hq (selected g op oe) hn cn (active_product g source ss op oe r ctrl)
  simp only [set_product] at hproduct
  have herase := erase_power (q := q) source ss op oe
    (if g then some (grownBits (q := q) N r) else some op)
    (if g then some oe else some (grownBits (q := q) N r)) (some (bits q)) ctrl r
  apply ((((hcopy.seq hbase).seq hpower).seq hproduct).seq herase).consequence
    (fun _ h => h) (fun _ h => h)
  simp only [cost]
  omega

def coefficient (q : ℕ) := RecursiveChildQuotientsConstant.cost q + FixedBasePowerDescriptor.constant q + 128

theorem cost_linear (g : Bool) (op oe : List Bool) (N r V : ℕ) (hV : 0 < V)
    (co : GrowingCounterData.Canonical (selected (!g) op oe))
    (ho : Counter.value (selected (!g) op oe) ≤ V)
    (hp : q^r ≤ V) (hn : N*q^r ≤ V) : cost q g op oe N r ≤ coefficient q*V := by
  have wo := (GrowingCounterData.canonical_width _ co).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have wp := (GrowingCounterData.canonical_width _ (FixedBasePowerStep.bits_canonical q r)).trans
    (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  rw [FixedBasePowerStep.bits_value] at wp
  have hc := Nat.le_mul_of_pos_right (RecursiveChildQuotientsConstant.cost q) hV
  have hpower := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant q) hp
  dsimp only [cost,coefficient,powerBits]
  nlinarith

/-- Uniform preparation budget under a caller's total volume bound. -/
theorem initializes_linear (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (clock : ℤ → Fin (a+4)) (p : ℤ) (N r V : ℕ) (hq : 2 ≤ q) (hV : 0 < V)
    (hn : Counter.value (selected g op oe) = N)
    (cn : GrowingCounterData.Canonical (selected g op oe))
    (co : GrowingCounterData.Canonical (selected (!g) op oe))
    (ho : Counter.value (selected (!g) op oe) ≤ V) (hp : q^r ≤ V) (hN : N*q^r ≤ V)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a) g)
      (fun v => v = input source ss op oe (controls clock p rs))
      (fun v => v = prepared g source ss op oe N r (controls clock p rs))
      (coefficient q*V) := by
  exact (initializes g source ss op oe rs clock p N r hq hn cn hr cr).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear g op oe N r V hV co ho hp hN)

/-- Preparation is linear in the entire physical payload volume. -/
theorem initializes_volume (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe rs : List Bool)
    (clock : ℤ → Fin (a+4)) (p : ℤ) (P S E r : ℕ) (hq : 2 ≤ q)
    (hP : 0 < P) (hS : 0 < S) (hE : 0 < E)
    (hp : Counter.value op = P) (he : Counter.value oe = E)
    (cp : GrowingCounterData.Canonical op) (ce : GrowingCounterData.Canonical oe)
    (hr : Counter.value rs = r) (cr : GrowingCounterData.Canonical rs) :
    HoareTime (program (q := q) (a := a) g)
      (fun v => v = input source ss op oe (controls clock p rs))
      (fun v => v = prepared g source ss op oe (if g then P else E) r (controls clock p rs))
      (coefficient q*(P*S*q^r*E)) := by
  have hpow : 0 < q^r := pow_pos (by omega : 0 < q) r
  have hPS := Nat.mul_pos hP hS
  have hV := Nat.mul_pos (Nat.mul_pos hPS hpow) hE
  have hPv : P ≤ P*S*q^r*E := (Nat.le_mul_of_pos_right P hS).trans
    ((Nat.le_mul_of_pos_right (P*S) hpow).trans (Nat.le_mul_of_pos_right (P*S*q^r) hE))
  have hEv : E ≤ P*S*q^r*E := Nat.le_mul_of_pos_left E (Nat.mul_pos hPS hpow)
  have hpowv : q^r ≤ P*S*q^r*E := (Nat.le_mul_of_pos_left (q^r) hPS).trans
    (Nat.le_mul_of_pos_right (P*S*q^r) hE)
  have hPpow : P*q^r ≤ P*S*q^r*E :=
    (Nat.mul_le_mul_right (q^r) (Nat.le_mul_of_pos_right P hS)).trans
      (Nat.le_mul_of_pos_right (P*S*q^r) hE)
  have hEpow : E*q^r ≤ P*S*q^r*E := by
    simpa only [Nat.mul_comm E (q^r)] using
      Nat.mul_le_mul_right E (Nat.le_mul_of_pos_left (q^r) hPS)
  apply initializes_linear g source ss op oe rs clock p (if g then P else E) r
    (P*S*q^r*E) hq hV _ _ _ _ hpowv _ hr cr
  all_goals cases g <;> simp_all [selected]

end
end IntegerMultBounds.Machine.RadixHighBlockJoinInitialize
