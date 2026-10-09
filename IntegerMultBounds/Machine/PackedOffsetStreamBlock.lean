import IntegerMultBounds.Machine.PackedOffsetStreamEmit
import IntegerMultBounds.Machine.BinaryCanonicalTrim

/-! One runtime-width packed block becomes a canonical offset stream word.
Its complete scratch tape starts and ends blank, including its marker. -/
namespace IntegerMultBounds.Machine.PackedOffsetStreamBlock
open MarkedWordCleanup (one empty)
open CountedCopyReuse (binary)
noncomputable section

def canonical (xs : List Bool) : List Bool := (BinaryCanonicalTrim.normalize_exists (a := 0) xs).choose

theorem canonical_facts (xs : List Bool) :
    GrowingCounterData.Canonical (canonical xs) ∧ Counter.value (canonical xs) = Counter.value xs ∧
      (canonical xs).length ≤ xs.length := by
  have hh := (BinaryCanonicalTrim.normalize_exists (a := 0) xs).choose_spec
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

def work (f scratch g : ℤ → Fin 4) (p r q : ℤ) (bs : List Bool) : Tapes 5 0 :=
  (CountedCopyReuse.bank f scratch CountedCopyReuse.empty (binary bs) p r 1 1).append (one g q)
def bank (f g : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) := work f (fun _ => blank) g p 0 q bs

def scratchPlacement : Fin (1+4) ≃ Fin 5 := Equiv.swap 0 1
def atScratch {s : ℕ} (M : Program 1 s 0) := Placement.placed M scratchPlacement

theorem scratch_hoare {s cost : ℕ} (M : Program 1 s 0) (h h' : ℤ → Fin 4) (r r' : ℤ)
    (hh : HoareTime M (fun v => v = one h r) (fun v => v = one h' r') cost)
    (f g : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    HoareTime (atScratch M) (fun v => v = work f h g p r q bs)
      (fun v => v = work f h' g p r' q bs) cost := by
  have ha : Placement.active scratchPlacement (work f h g p r q bs) = one h r := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ht := Placement.hoare_at hh scratchPlacement _ ha
  apply ht.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def normalize : Program 1 6 0 := seq StepLeft.program BinaryCanonicalTrim.program

theorem normalizes (xs : List Bool) :
    HoareTime normalize (fun v => v = one (binary xs) (1+xs.length))
      (fun v => v = one (binary (canonical xs)) 1) (xs.length+5) := by
  have hn := (BinaryCanonicalTrim.normalize_exists (a := 0) xs).choose_spec.2.2.2
  have he (xs : List Bool) : BinaryDescriptorStack.descriptor (a := 0) xs = binary xs :=
    (BinaryOffsetStreamRead.binary_word xs).symm
  change HoareTime BinaryCanonicalTrim.program
    (fun v => v = one (BinaryDescriptorStack.descriptor xs) xs.length)
    (fun v => v = one (BinaryDescriptorStack.descriptor (canonical xs)) 1) (xs.length+3) at hn
  rw [he xs,he (canonical xs)] at hn
  have hs := StepLeft.step_hoare (binary xs) (1+xs.length)
  simp only [add_sub_cancel_left] at hs
  exact (hs.seq hn).consequence (fun _ h => h) (fun _ h => h) (by omega)

def emitPlacement : Fin (2+3) ≃ Fin 5 where
  toFun := ![1,4,0,2,3]
  invFun := ![2,0,3,4,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
def emitProgram := Placement.placed PackedOffsetStreamEmit.program emitPlacement

theorem emits (xs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ) (bs : List Bool) :
    HoareTime emitProgram (fun v => v = work f (binary xs) g p 1 q bs)
      (fun v => v = bank f (putWord g q (PackedOffsetStreamEmit.encoded xs))
        p (q+(PackedOffsetStreamEmit.encoded xs).length) bs) (2*xs.length+6) := by
  have ha : Placement.active emitPlacement (work f (binary xs) g p 1 q bs) = Copy.tapes (binary xs) g 1 q := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hh := Placement.hoare_at (PackedOffsetStreamEmit.emits xs g q) emitPlacement _ ha
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def program : Program 5 30 0 := seq (seq (seq (atScratch MarkedWordCleanup.markProgram)
  (extend CountedCopyReuse.program 1)) (atScratch normalize)) emitProgram

theorem runs (xs bs : List Bool) (f g : ℤ → Fin 4) (p q : ℤ)
    (hb : Counter.value bs = xs.length) :
    HoareTime program (fun v => v = bank (putWord f p (xs.map bitSymbol)) g p q bs)
      (fun v => v = bank (putWord f p (xs.map bitSymbol))
        (putWord g q (PackedOffsetStreamEmit.encoded (canonical xs)))
        (p+xs.length) (q+(PackedOffsetStreamEmit.encoded (canonical xs)).length) bs)
      (8*xs.length+7*bs.length+31) := by
  let src := putWord f p (xs.map bitSymbol)
  have h₀ := scratch_hoare _ _ _ _ _ (MarkedWordCleanup.mark_hoare ([] : List (Fin 4))) src g p q bs
  have h₁ := hoare_extend_eq (CountedCopyReuse.copy_hoare f empty p 1 (xs.map bitSymbol) bs
    (by simpa using hb)) (one g q)
  rw [show putWord empty 1 (xs.map bitSymbol) = binary xs from (BinaryOffsetStreamRead.binary_word xs).symm] at h₁
  simp only [List.length_map] at h₁
  have h₂ := scratch_hoare _ _ _ _ _ (normalizes xs) src g (p+xs.length) q bs
  have h₃ := emits (canonical xs) src g (p+xs.length) q bs
  have hl := (canonical_facts xs).2.2
  exact (((h₀.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.PackedOffsetStreamBlock
