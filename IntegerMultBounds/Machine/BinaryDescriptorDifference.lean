import IntegerMultBounds.Machine.BinarySubReuse
import IntegerMultBounds.Machine.BinaryDescriptorNormalize
import IntegerMultBounds.Machine.BinaryCanonicalData
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant

/-! Immutable marked-descriptor subtraction with a canonical output. The
literal subtractor, forward scan, zero trimming and all rewinds are paid;
no padded operands or derived result are supplied to the fixed program. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorDifference
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)

def bank (xs ys : List Bool) (out : ℤ → Fin (a+4)) (r : ℤ) : Tapes 3 a :=
  ⟨![1,1,r],![CountedLoopReuseAlphabet.binary xs,CountedLoopReuseAlphabet.binary ys,out]⟩

def input (xs ys : List Bool) := bank (a := a) xs ys (fun _ => blank) 0
def output (xs ys zs : List Bool) := bank (a := a) xs ys (BinaryDescriptorStack.descriptor zs) 1

def subtractProgram := Alphabet.program (CountedLoopReuseAlphabet.encoding a) BinarySubReuse.program

def outputPlacement : Fin (1+2) ≃ Fin 3 := FiniteReturnStackAt.placement (2 : Fin 3)
def normalizeProgram := Placement.placed (BinaryDescriptorNormalize.program (a := a)) outputPlacement

def program := seq (subtractProgram (a := a)) normalizeProgram

theorem mapped_bank (xs ys : List Bool) (out : ℤ → Fin 4) (r : ℤ) :
    Alphabet.mapTapes (CountedLoopReuseAlphabet.encoding a) (BinarySubReuse.bank xs ys out 1 1 r) =
      bank xs ys (fun j => (CountedLoopReuseAlphabet.encoding a).encode (out j)) r := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact CountedLoopReuseAlphabet.encoding_binary xs
    · exact CountedLoopReuseAlphabet.encoding_binary ys
    · rfl

private theorem subtracts (xs ys : List Bool) :
    HoareTime (subtractProgram (a := a)) (fun v => v = input xs ys)
      (fun v => v = output xs ys (BinarySubReuse.difference xs ys))
      (4*max xs.length ys.length+14) := by
  have h := Alphabet.map_hoare (CountedLoopReuseAlphabet.encoding a) (BinarySubReuse.sub_hoare xs ys)
  have hb : (fun j => (CountedLoopReuseAlphabet.encoding a).encode (CountedCopyReuse.binary (BinarySubReuse.difference xs ys) j)) =
      BinaryDescriptorStack.descriptor (a := a) (BinarySubReuse.difference xs ys) := by
    rw [CountedLoopReuseAlphabet.encoding_binary,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact (CountedLoopReuseAlphabet.encoding_binary _).symm
  apply h.consequence _ _ le_rfl
  · rintro v rfl
    refine ⟨BinarySubReuse.bank xs ys (fun _ => blank) 1 1 0,rfl,?_⟩
    rw [mapped_bank]
    rfl
  · rintro v ⟨w,rfl,rfl⟩
    rw [mapped_bank,hb]
    rfl

private theorem normalizes (xs ys zs : List Bool) :
    ∃ ws : List Bool, GrowingCounterData.Canonical ws ∧ Counter.value ws = Counter.value zs ∧
      ws.length ≤ zs.length ∧ HoareTime (normalizeProgram (a := a))
        (fun v => v = output xs ys zs) (fun v => v = output xs ys ws) (2*zs.length+6) := by
  obtain ⟨ws,hc,hv,hl,h⟩ := BinaryDescriptorNormalize.normalizes (a := a) zs
  have ha : Placement.active outputPlacement (output (a := a) xs ys zs) = BinaryDescriptorNormalize.bank zs := by
    rw [outputPlacement,FiniteReturnStackAt.active_bank]
    rfl
  have hh := Placement.hoare_at h outputPlacement (output (a := a) xs ys zs) ha
  refine ⟨ws,hc,hv,hl,hh.consequence (fun _ h => h) ?_ le_rfl⟩
  rintro v ⟨w,rfl,rfl⟩
  change Placement.replace outputPlacement (output xs ys zs)
    (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor ws) 1) = _
  rw [outputPlacement,FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The two original canonical operands and their heads are retained;
zero difference has the canonical empty binary word and head one. -/
theorem difference_hoare (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs) :
    HoareTime (program (a := a)) (fun v => v = input xs ys)
      (fun v => v = output xs ys (RecursiveChildQuotientsConstant.bits (Counter.value xs-Counter.value ys)))
      (6*max xs.length ys.length+21) := by
  obtain ⟨ws,hc,hv,hl,hn⟩ := normalizes (a := a) xs ys (BinarySubReuse.difference xs ys)
  have hw : ws = RecursiveChildQuotientsConstant.bits (Counter.value xs-Counter.value ys) :=
    BinaryCanonicalData.value_injective _ _ hc (RecursiveChildQuotientsConstant.bits_canonical _)
      ((hv.trans (BinarySubReuse.difference_value xs ys hle)).trans
        (RecursiveChildQuotientsConstant.bits_value _).symm)
  rw [hw] at hn
  apply ((subtracts (a := a) xs ys).seq hn).consequence (fun _ h => h) (fun _ h => h)
  rw [BinarySubReuse.difference_length]
  omega

theorem difference_linear (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs)
    (cx : GrowingCounterData.Canonical xs) (cy : GrowingCounterData.Canonical ys) :
    HoareTime (program (a := a)) (fun v => v = input xs ys)
      (fun v => v = output xs ys (RecursiveChildQuotientsConstant.bits (Counter.value xs-Counter.value ys)))
      (6*Counter.value xs+27) := by
  apply (difference_hoare (a := a) xs ys hle).consequence (fun _ h => h) (fun _ h => h)
  have hx := GrowingCounterData.canonical_width xs cx
  have hy := GrowingCounterData.canonical_width ys cy
  have lx := Nat.log2_le_self (Counter.value xs)
  have ly := Nat.log2_le_self (Counter.value ys)
  omega

end
end IntegerMultBounds.Machine.BinaryDescriptorDifference
