import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
import IntegerMultBounds.Machine.BinaryDescriptorCompare

/-! Runtime f=1 versus f≥2 selection from the retained original f word.
The literal one descriptor is physically written and erased; only the
comparison bit survives until its separately paid selecting cleanup. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageWidthSelector
noncomputable section
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def input (fs : List Bool) : Tapes 3 a :=
  ⟨![0,1,0],![fun _ => blank,BinaryDescriptorStack.descriptor fs,fun _ => blank]⟩
def output (fs : List Bool) : Tapes 3 a :=
  ⟨![0,1,0],![fun _ => blank,BinaryDescriptorStack.descriptor fs,BinaryDescriptorCompare.result (bits 1) fs]⟩

def initializer := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (0 : Fin 3))
def eraseOne := BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 3)
def program := seq (seq (initializer (a := a)) BinaryDescriptorCompare.program) eraseOne

def cost (fs : List Bool) := BinaryDescriptorCompare.cost (bits 1) fs+17

theorem initializes (fs : List Bool) : HoareTime (initializer (a := a))
    (fun v => v=input fs) (fun v => v=BinaryDescriptorCompare.input (bits 1) fs) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (0 : Fin 3)) (input fs)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) ?_ (by decide)
  rintro v ⟨w,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem erases_one (fs : List Bool) : HoareTime (eraseOne (a := a))
    (fun v => v=BinaryDescriptorCompare.output (bits 1) fs) (fun v => v=output fs) 6 := by
  have h := BinaryDescriptorCleanupList.one_hoare (0 : Fin 3)
    (BinaryDescriptorCompare.output (q := a) (bits 1) fs) (bits 1) rfl rfl
  apply h.consequence (fun _ h => h) ?_ (by decide)
  rintro v rfl
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (fs : List Bool) : HoareTime (program (a := a))
    (fun v => v=input fs) (fun v => v=output fs) (cost fs) := by
  exact (((initializes fs).seq (BinaryDescriptorCompare.compare_hoare (bits 1) fs)).seq (erases_one fs)).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

def cleanup : Program 3 2 a := BinaryDescriptorCompare.eraseFlag

theorem cleans (fs : List Bool) : HoareTime (cleanup (a := a))
    (fun v => v=output fs) (fun v => v=input fs) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (output (a := a) fs)).consequence
    (fun _ h => h) ?_ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> by_cases hz : z=0
    all_goals simp [output,BinaryDescriptorCompare.result,hz]
    all_goals intro he; rw [he]

def test (sy : Fin 3 → Fin (a+4)) : Bool := decide (sy 2=bitSymbol true)

theorem test_eq (fs : List Bool) : test (output (a := a) fs).reads=decide (1<Counter.value fs) := by
  change decide (bitSymbol (a := a) (decide (Counter.value (bits 1)<Counter.value fs))=bitSymbol true)=_
  rw [RecursiveChildQuotientsConstant.bits_value]
  by_cases h : 1<Counter.value fs <;> simp [h,bitSymbol,Fin.ext_iff]

theorem true_iff (fs : List Bool) (f : ℕ) (hv : Counter.value fs=f) :
    test (output (a := a) fs).reads=true ↔ 2≤f := by rw [test_eq,hv]; simp; omega

theorem false_iff (fs : List Bool) (f : ℕ) (hv : Counter.value fs=f) (hf : 0<f) :
    test (output (a := a) fs).reads=false ↔ f=1 := by rw [test_eq,hv]; simp; omega

theorem cost_bound (fs : List Bool) (f V : ℕ) (hv : Counter.value fs=f)
    (hc : GrowingCounterData.Canonical fs) (hf : f≤V) (hV : 0<V) : cost fs+1≤40*V := by
  have hl := GrowingCounterData.canonical_width fs hc
  rw [hv] at hl
  have hh := Nat.log2_le_self f
  have ho : (bits 1).length=1 := by decide
  unfold cost BinaryDescriptorCompare.cost
  rw [ho]
  omega

theorem width_le_volume {s : CompactGadgetReservationShape.Shape} (v : ActivePrefixStageParameters.Stage s)
    (rows : ℕ) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows)
    (hrecord : s.bits+1≤s.payload) : v.f≤rows*s.recordWidth := by
  rcases ActivePrefixStageGeometry.source_order v with h | h
  · exact (ActivePrefixStageHeadersBudget.original_bounds .early v rows hG hGK h hr hrecord).1 7
  · exact (ActivePrefixStageHeadersBudget.original_bounds .late v rows hG hGK h hr hrecord).1 7

/-- The complete select/clean/branch overhead is linear in full logical
volume, with the f header read directly from original slot seven. -/
theorem stage_cost_bound {s : CompactGadgetReservationShape.Shape} (v : ActivePrefixStageParameters.Stage s)
    (rows : ℕ) (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows)
    (hrecord : s.bits+1≤s.payload) : cost (bits v.f)+4≤43*(rows*s.recordWidth) := by
  have hf := width_le_volume v rows hG hGK hr hrecord
  have hp : 0<s.payload := by omega
  have hV : 0<rows*s.recordWidth := by unfold CompactGadgetReservationShape.Shape.recordWidth; positivity
  have hh := cost_bound (bits v.f) v.f (rows*s.recordWidth) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) hf hV
  omega

end
end IntegerMultBounds.Machine.ActivePrefixStageWidthSelector
