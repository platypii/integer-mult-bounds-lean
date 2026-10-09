import IntegerMultBounds.Machine.ArbitraryWidthHighFoldSemantics
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! Construct all six folded root headers from the sole original header bank.
Every input remains literal, and the private arithmetic workspace is restored. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeaders
noncomputable section
variable {a : ℕ}
open RecursiveInterchangeLayout (Descriptor)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def words (v : Descriptor) (hs : Fin 6 → List Bool) : Fin 6 → List Bool :=
  ![ArbitraryWidthHighPrefix.bits v.beforeRows v.rows v.beforeH,bits 1,bits 1,hs 3,hs 4,hs 5]

def bank (hs : Fin 6 → List Bool) (ds : Fin 6 → Option (List Bool)) : Tapes 16 a :=
  ⟨fun i => if i.val < 6 then 1 else if h : i.val < 12 then
      RecursiveDimensionBank.head (ds ⟨i.val-6,by omega⟩) else 0,
   fun i => if h : i.val < 6 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩)
      else if h : i.val < 12 then RecursiveDimensionBank.tape (ds ⟨i.val-6,by omega⟩)
      else fun _ => blank⟩
def state (v : Descriptor) (hs : Fin 6 → List Bool) (k : ℕ) : Tapes 16 a :=
  bank hs (fun i => if i.val < k then some (words v hs i) else none)
def input (hs : Fin 6 → List Bool) : Tapes 16 a := bank hs (fun _ => none)
def output (v : Descriptor) (hs : Fin 6 → List Bool) : Tapes 16 a := state v hs 6

def prefixPlacement : Fin (8+8) ≃ Fin 16 where
  toFun := ![0,1,2,12,6,13,14,15,3,4,5,7,8,9,10,11]
  invFun := ![0,1,2,8,9,10,4,11,12,13,14,15,3,5,6,7]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def prefixProgram := Placement.placed (ArbitraryWidthHighPrefix.program (a := a)) prefixPlacement

def constantProgram (i : Fin 16) := Placement.placed
  (RecursiveChildQuotientsConstant.program (a := a) 1) (FiniteReturnStackAt.placement i)
def copy3 : Program 16 5 a := BinaryDescriptorInstall.program a 3 9 (by decide)
def copy4 : Program 16 5 a := BinaryDescriptorInstall.program a 4 10 (by decide)
def copy5 : Program 16 5 a := BinaryDescriptorInstall.program a 5 11 (by decide)
def program := seq (seq (seq (seq (seq (prefixProgram (a := a)) (constantProgram 7))
  (constantProgram 8)) copy3) copy4) copy5

def cost (v : Descriptor) (hs : Fin 6 → List Bool) :=
  ArbitraryWidthHighPrefix.cost v.beforeRows v.rows v.beforeH+1+9+1+9+1+
    (2*(hs 3).length+5)+1+(2*(hs 4).length+5)+1+(2*(hs 5).length+5)

private theorem prefix_active_input (hs : Fin 6 → List Bool) :
    Placement.active prefixPlacement (input (a := a) hs) =
      ArbitraryWidthHighPrefix.input (fun i => hs (Fin.castAdd 3 i)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem prefix_active_output (v : Descriptor) (hs : Fin 6 → List Bool) :
    Placement.active prefixPlacement (state (a := a) v hs 1) =
      ArbitraryWidthHighPrefix.output v.beforeRows v.rows v.beforeH
        (fun i => hs (Fin.castAdd 3 i)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
private theorem prefix_frame (v : Descriptor) (hs : Fin 6 → List Bool) :
    Placement.extra prefixPlacement (input (a := a) hs) =
      Placement.extra prefixPlacement (state v hs 1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem prefix_constructs (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs) :
    HoareTime (prefixProgram (a := a)) (fun z => z = input hs)
      (fun z => z = state v hs 1) (ArbitraryWidthHighPrefix.cost v.beforeRows v.rows v.beforeH) := by
  have h := ArbitraryWidthHighPrefix.constructs (a := a) v.beforeRows v.rows v.beforeH
    hp.2.1 hp.2.2.1 (fun i => hs (Fin.castAdd 3 i))
    (by intro i; fin_cases i <;> exact hh.1 _) (fun i => hh.2 _)
  have ht := Placement.hoare_at h prefixPlacement (input hs) (prefix_active_input hs)
  apply ht.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,prefix_frame,← prefix_active_output]
  exact Placement.view _ _

private theorem constant_hoare (i : Fin 16) (z : Tapes 16 a)
    (ht : z.tape i = fun _ => blank) (hh : z.head i = 0) :
    HoareTime (constantProgram i) (fun w => w = z)
      (fun w => w = setTape z i (BinaryDescriptorStack.descriptor (bits 1)) 1) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement i) z (by rw [FiniteReturnStackAt.active_bank]; simp [ht,hh])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank i z _ _

private theorem constant1_constructs (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (constantProgram (a := a) 7) (fun z => z = state v hs 1)
      (fun z => z = state v hs 2) 9 := by
  have h := constant_hoare (7 : Fin 16) (state (a := a) v hs 1) rfl rfl
  have he : setTape (state (a := a) v hs 1) 7
      (BinaryDescriptorStack.descriptor (bits 1)) 1 = state v hs 2 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
    exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [he] at h
  exact h

private theorem constant2_constructs (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (constantProgram (a := a) 8) (fun z => z = state v hs 2)
      (fun z => z = state v hs 3) 9 := by
  have h := constant_hoare (8 : Fin 16) (state (a := a) v hs 2) rfl rfl
  have he : setTape (state (a := a) v hs 2) 8
      (BinaryDescriptorStack.descriptor (bits 1)) 1 = state v hs 3 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> try rfl
    exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [he] at h
  exact h

private theorem copy3_constructs (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (copy3 (a := a)) (fun z => z = state v hs 3)
      (fun z => z = state v hs 4) (2*(hs 3).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (3 : Fin 16) 9 (by decide)
    (state (a := a) v hs 3) (hs 3) rfl rfl rfl rfl
  have he : setTape (state (a := a) v hs 3) 9
      (RadixZeroFill.encodedBinary (hs 3)) 1 = state v hs 4 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem copy4_constructs (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (copy4 (a := a)) (fun z => z = state v hs 4)
      (fun z => z = state v hs 5) (2*(hs 4).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (4 : Fin 16) 10 (by decide)
    (state (a := a) v hs 4) (hs 4) rfl rfl rfl rfl
  have he : setTape (state (a := a) v hs 4) 10
      (RadixZeroFill.encodedBinary (hs 4)) 1 = state v hs 5 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

private theorem copy5_constructs (v : Descriptor) (hs : Fin 6 → List Bool) :
    HoareTime (copy5 (a := a)) (fun z => z = state v hs 5)
      (fun z => z = state v hs 6) (2*(hs 5).length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (5 : Fin 16) 11 (by decide)
    (state (a := a) v hs 5) (hs 5) rfl rfl rfl rfl
  have he : setTape (state (a := a) v hs 5) 11
      (RadixZeroFill.encodedBinary (hs 5)) 1 = state v hs 6 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

theorem constructs (v : Descriptor) (hs : Fin 6 → List Bool)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs) :
    HoareTime (program (a := a)) (fun z => z = input hs)
      (fun z => z = output v hs) (cost v hs) :=
  (((((prefix_constructs v hs hp hh).seq (constant1_constructs v hs)).seq
    (constant2_constructs v hs)).seq (copy3_constructs v hs)).seq
    (copy4_constructs v hs)).seq (copy5_constructs v hs)

theorem headers (v : Descriptor) (hs : Fin 6 → List Bool)
    (hh : RecursiveDimensionBank.Headers v hs) :
    RecursiveDimensionBank.Headers (ArbitraryWidthHighFoldSemantics.folded v) (words v hs) := by
  constructor
  · intro i; fin_cases i
    · exact ArbitraryWidthHighPrefix.bits_value _ _ _
    · exact RecursiveChildQuotientsConstant.bits_value 1
    · exact RecursiveChildQuotientsConstant.bits_value 1
    · exact hh.1 3
    · exact hh.1 4
    · exact hh.1 5
  · intro i; fin_cases i
    · exact ArbitraryWidthHighPrefix.bits_canonical _ _ _
    · exact RecursiveChildQuotientsConstant.bits_canonical 1
    · exact RecursiveChildQuotientsConstant.bits_canonical 1
    · exact hh.2 3
    · exact hh.2 4
    · exact hh.2 5

theorem cost_linear (v : Descriptor) (hs : Fin 6 → List Bool) (V : ℕ)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs)
    (hprefix : v.beforeRows*v.rows*v.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values v i ≤ V) : cost v hs ≤ 224*V := by
  have hV : 0 < V := lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1) hprefix
  have hAR : v.beforeRows*v.rows ≤ V :=
    (Nat.le_mul_of_pos_right _ hp.2.2.1).trans hprefix
  have hl := GrowingCounterData.canonical_width
    (ArbitraryWidthHighPrefix.intermediate v.beforeRows v.rows)
    (BoundedProductDescriptor.bits_canonical _ _)
  rw [ArbitraryWidthHighPrefix.intermediate_value] at hl
  have hlog := Nat.log2_le_self (v.beforeRows*v.rows)
  have h3 := GrowingCounterData.canonical_width (hs 3) (hh.2 3)
  have h4 := GrowingCounterData.canonical_width (hs 4) (hh.2 4)
  have h5 := GrowingCounterData.canonical_width (hs 5) (hh.2 5)
  rw [hh.1 3] at h3
  rw [hh.1 4] at h4
  rw [hh.1 5] at h5
  have l3 := Nat.log2_le_self (RecursiveDimensionBank.values v 3)
  have l4 := Nat.log2_le_self (RecursiveDimensionBank.values v 4)
  have l5 := Nat.log2_le_self (RecursiveDimensionBank.values v 5)
  have b3 := hv 3
  have b4 := hv 4
  have b5 := hv 5
  unfold cost ArbitraryWidthHighPrefix.cost
  omega

theorem constructs_linear (v : Descriptor) (hs : Fin 6 → List Bool) (V : ℕ)
    (hp : v.Positive) (hh : RecursiveDimensionBank.Headers v hs)
    (hprefix : v.beforeRows*v.rows*v.beforeH ≤ V)
    (hv : ∀ i, RecursiveDimensionBank.values v i ≤ V) :
    HoareTime (program (a := a)) (fun z => z = input hs)
      (fun z => z = output v hs) (224*V) :=
  (constructs v hs hp hh).consequence (fun _ h => h) (fun _ h => h)
    (cost_linear v hs V hp hh hprefix hv)

theorem output_headers (v : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 6) :
    (output (a := a) v hs).head (Fin.natAdd 6 (Fin.castAdd 4 i)) = 1 ∧
    (output (a := a) v hs).tape (Fin.natAdd 6 (Fin.castAdd 4 i)) =
      RadixZeroFill.encodedBinary (words v hs i) := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

theorem output_frame (v : Descriptor) (hs : Fin 6 → List Bool) (i : Fin 16)
    (hi : i.val < 6 ∨ 12 ≤ i.val) :
    (output (a := a) v hs).head i = (input (a := a) hs).head i ∧
    (output (a := a) v hs).tape i = (input (a := a) hs).tape i := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | norm_num at hi

end
end IntegerMultBounds.Machine.ArbitraryWidthHighFoldHeaders
