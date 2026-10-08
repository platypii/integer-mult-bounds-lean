import IntegerMultBounds.Machine.BinaryDescriptorDivisionBoundary
import IntegerMultBounds.Machine.CleanExecution

/-! Fully prepared and cleaned marked-binary descriptor division. Inputs start
at head one; all scratch and trackers start blank/head-zero. The fixed machine
retains both exact inputs, returns a canonical marked quotient/head-one, and
physically erases/rewinds every private tape, including the shifted remainder. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorDivision
variable {a : ℕ}
noncomputable section

def core (a : ℕ) := seq (seq BinaryDescriptorDivisionBoundary.prepare (BinaryDescriptorDivisionRaw.program a))
  BinaryDescriptorDivisionBoundary.finish

def right : Fin 6 → Bool := ![true,true,false,false,false,false]
def keep : Fin 6 → Bool := ![true,true,false,false,false,true]

def program (a : ℕ) := CleanExecution.program (core a) right keep

def input (ys ds : List Bool) : Tapes 12 a :=
  (BinaryDescriptorDivisionBoundary.input ys ds).append (SharedBank.empty 6 a)

def retained (ys ds zs : List Bool) : Tapes 6 a :=
  BinaryDescriptorDivisionRaw.bank (BinaryDescriptorStack.descriptor ys) (BinaryDescriptorStack.descriptor ds)
    (fun _ => blank) (fun _ => blank) (fun _ => blank) (BinaryDescriptorStack.descriptor zs) 1 1 0 0 0 1

def output (ys ds zs : List Bool) : Tapes 12 a := (retained ys ds zs).append (SharedBank.empty 6 a)

def coreCost (ys ds : List Bool) : ℕ :=
  (∑ i ∈ Finset.range ys.length, (BinaryDivide.costAt ys ds i+2))+3*ys.length+20

def cost (ys ds : List Bool) : ℕ := 32*coreCost ys ds+70

private theorem retained_eq (ys ds zs : List Bool) :
    TrackedCleanupList.retained keep (BinaryDescriptorDivisionBoundary.output (a := a) ys ds zs) = retained ys ds zs := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [keep,BinaryDescriptorDivisionBoundary.output,BinaryDescriptorDivisionRaw.bank]

/-- The exact division result is produced with every private tape blank and
every private head at zero; no free cleanup or coordinate reset is assumed. -/
theorem divide_hoare (ys ds : List Bool) (hd : 0 < Counter.value ds) :
    ∃ zs : List Bool, GrowingCounterData.Canonical zs ∧ Counter.value zs = Counter.value ys / Counter.value ds ∧
      zs.length ≤ ys.length ∧
      HoareTime (program a) (fun w => w = input ys ds) (fun w => w = output ys ds zs) (cost ys ds) := by
  obtain ⟨zs,hcanon,hval,hlen,hdiv⟩ := BinaryDescriptorDivisionRaw.divide_hoare (a := a) ys ds hd
  have hcore : HoareTime (core a)
      (fun w => w = BinaryDescriptorDivisionBoundary.input ys ds)
      (fun w => w = BinaryDescriptorDivisionBoundary.output ys ds zs) (coreCost ys ds) := by
    have h := ((BinaryDescriptorDivisionBoundary.prepare_hoare (a := a) ys ds).seq hdiv).seq
      (BinaryDescriptorDivisionBoundary.finish_hoare ys ds zs)
    exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold coreCost; omega)
  have hh : (BinaryDescriptorDivisionBoundary.input (a := a) ys ds).head = TrackedInit.position right := by
    funext i; fin_cases i <;> rfl
  have hw : ∀ i, keep i = false → (BinaryDescriptorDivisionBoundary.input (a := a) ys ds).tape i = fun _ => blank := by
    intro i hi; fin_cases i <;> simp [keep] at hi <;> rfl
  have hclean := CleanExecution.realizes (core a) right keep
    (BinaryDescriptorDivisionBoundary.input ys ds) (BinaryDescriptorDivisionBoundary.output ys ds zs)
    (coreCost ys ds) hh hw hcore
  rw [retained_eq] at hclean
  exact ⟨zs,hcanon,hval,hlen,hclean⟩

/-- An explicit polynomial bit-length budget before logical-volume charging. -/
theorem cost_le (ys ds : List Bool) :
    cost ys ds ≤ 32*(ys.length*(4*ys.length+6*ds.length+30))+710 := by
  have h := BinaryDivide.cost_le ys ds
  unfold cost coreCost
  nlinarith

end
end IntegerMultBounds.Machine.BinaryDescriptorDivision
