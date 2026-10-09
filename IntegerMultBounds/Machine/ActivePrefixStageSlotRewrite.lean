import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physically replace the source/target slot words between fixed binary
row-addition instructions. Old descriptors are scanned and erased; the next
literal pair is written and rewound by finite control. Every join is paid. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageSlotRewrite
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def write (slot : Fin t) (n : ℕ) :=
  Placement.placed (RecursiveChildQuotientsConstant.program (a := a) n)
    (FiniteReturnStackAt.placement slot)

def program (slot : Fin t) (n : ℕ) :=
  seq (BinaryDescriptorCleanupList.oneProgram slot) (write (a := a) slot n)

def updated (slot : Fin t) (n : ℕ) (v : Tapes t a) :=
  setTape v slot (BinaryDescriptorStack.descriptor (bits n)) 1

def cost (xs : List Bool) (n : ℕ) := 2*xs.length+5+RecursiveChildQuotientsConstant.cost n

theorem writes (slot : Fin t) (n : ℕ) (v : Tapes t a)
    (ht : v.tape slot=fun _ => blank) (hh : v.head slot=0) :
    HoareTime (write slot n) (fun w => w=v) (fun w => w=updated slot n v)
      (RecursiveChildQuotientsConstant.cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh])
  apply h.consequence (fun _ h => h) ?_ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem runs (slot : Fin t) (n : ℕ) (v : Tapes t a) (xs : List Bool)
    (ht : v.tape slot=BinaryDescriptorStack.descriptor xs) (hh : v.head slot=1) :
    HoareTime (program slot n) (fun w => w=v) (fun w => w=updated slot n v) (cost xs n) := by
  have he := BinaryDescriptorCleanupList.one_hoare slot v xs ht hh
  have hw := writes slot n (setTape v slot (fun _ => blank) 0)
    (by simp [setTape]) (by simp [setTape])
  have h := he.seq hw
  apply h.consequence (fun _ h => h) ?_ (by unfold cost; omega)
  rintro w rfl
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=slot <;> simp [setTape,hi]

theorem frame (slot i : Fin t) (n : ℕ) (v : Tapes t a) (hi : i≠slot) :
    (updated slot n v).head i=v.head i ∧ (updated slot n v).tape i=v.tape i := by
  simp [updated,setTape,hi]

def pair (source target : Fin t) (i j : ℕ) :=
  seq (program (a := a) source i) (program target j)

theorem pair_runs (source target : Fin t) (hd : target≠source) (i j : ℕ)
    (v : Tapes t a) (xs ys : List Bool)
    (hx : v.tape source=BinaryDescriptorStack.descriptor xs) (hhx : v.head source=1)
    (hy : v.tape target=BinaryDescriptorStack.descriptor ys) (hhy : v.head target=1) :
    HoareTime (pair source target i j) (fun w => w=v)
      (fun w => w=updated target j (updated source i v)) (cost xs i+cost ys j+1) := by
  have hf := frame source target i v hd
  exact ((runs source i v xs hx hhx).seq
    (runs target j (updated source i v) ys (hf.2.trans hy) (hf.1.trans hhy))).consequence
      (fun _ h => h) (fun _ h => h) (by omega)

theorem cost_bound (xs : List Bool) (n V : ℕ)
    (hc : GrowingCounterData.Canonical xs) (hv : Counter.value xs≤V) (hn : n≤V) :
    cost xs n≤5*V+16 := by
  have hx := GrowingCounterData.canonical_width xs hc
  have hy := GrowingCounterData.canonical_width (bits n) (RecursiveChildQuotientsConstant.bits_canonical n)
  rw [RecursiveChildQuotientsConstant.bits_value] at hy
  have hxl := Nat.log2_le_self (Counter.value xs)
  have hyl := Nat.log2_le_self n
  unfold cost RecursiveChildQuotientsConstant.cost
  omega

/-- Rewriting both control words has linear cost in any common bound on the
old and new slot indices. No cost depends on the stage implementation. -/
theorem pair_cost_bound (xs ys : List Bool) (i j V : ℕ)
    (hx : GrowingCounterData.Canonical xs) (hy : GrowingCounterData.Canonical ys)
    (hvx : Counter.value xs≤V) (hvy : Counter.value ys≤V) (hi : i≤V) (hj : j≤V) :
    cost xs i+cost ys j+1≤10*V+33 := by
  have h1 := cost_bound xs i V hx hvx hi
  have h2 := cost_bound ys j V hy hvy hj
  omega

end
end IntegerMultBounds.Machine.ActivePrefixStageSlotRewrite
