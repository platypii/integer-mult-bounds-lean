import IntegerMultBounds.Machine.RecursiveVolumeConstruct
import IntegerMultBounds.Machine.CleanExecution

/-! Fully clean physical volume synthesis. The only retained tapes are the six
original headers, the newly initialized empty clock, and the canonical volume
descriptor; every intermediate dimension and tracker is physically erased. -/
namespace IntegerMultBounds.Machine.RecursiveVolumeClean
open RecursiveInterchangeLayout (Descriptor volume)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def right (i : Fin 17) : Bool := decide (3 ≤ i.val ∧ i.val < 9)
def keep (i : Fin 17) : Bool := decide (i = 0 ∨ i = 16) || right i

def clock : Option (List Bool) → ℤ → Fin (q+4)
  | none => fun _ => blank
  | some _ => CountedLoopReuseAlphabet.empty

def retained (hs : Fin 6 → List Bool) (bs : Option (List Bool)) : Tapes 17 q :=
  ⟨![RecursiveDimensionBank.head bs,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,RecursiveDimensionBank.head bs],
   ![clock bs,fun _ => blank,fun _ => blank,RadixZeroFill.encodedBinary (hs 0),
     RadixZeroFill.encodedBinary (hs 1),RadixZeroFill.encodedBinary (hs 2),
     RadixZeroFill.encodedBinary (hs 3),RadixZeroFill.encodedBinary (hs 4),
     RadixZeroFill.encodedBinary (hs 5),fun _ => blank,fun _ => blank,fun _ => blank,
     fun _ => blank,fun _ => blank,fun _ => blank,fun _ => blank,RecursiveDimensionBank.tape bs]⟩

def bank (hs : Fin 6 → List Bool) (bs : Option (List Bool)) : Tapes 34 q :=
  (retained hs bs).append (SharedBank.empty 17 q)

def program := CleanExecution.program (RecursiveVolumeConstruct.program hq) right keep

def bound (V : ℕ) : ℕ := 36279*V+15503

private theorem input_eq (hs : Fin 6 → List Bool) :
    RecursiveVolumeConstruct.input (q := q) hs = retained hs none := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem retained_eq (hs : Fin 6 → List Bool) (v : Descriptor) :
    TrackedCleanupList.retained keep (RecursiveVolumeConstruct.output hq hs v) =
      retained hs (some (RecursiveVolumeConstruct.bits (q := q) v)) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem realizes (v : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) :
    HoareTime (program hq) (fun w => w = bank hs none)
      (fun w => w = bank hs (some (RecursiveVolumeConstruct.bits (q := q) v))) (bound (volume q v)) := by
  have hh := CleanExecution.realizes (RecursiveVolumeConstruct.program hq) right keep
    (RecursiveVolumeConstruct.input hs) (RecursiveVolumeConstruct.output hq hs v) _
    (by rw [input_eq]; funext i; fin_cases i <;> rfl)
    (by intro i hi; rw [input_eq]; fin_cases i <;> simp_all [keep,right] <;> rfl)
    (RecursiveVolumeConstruct.constructs_hoare hq v hs hv hp)
  rw [retained_eq,input_eq] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by unfold bound; omega)

theorem bound_linear (V : ℕ) (hV : 0 < V) : bound V ≤ 51782*V := by
  unfold bound
  omega

private theorem advance_length (n : ℕ) (bs : List Bool) :
    (GrowingCounterData.advance n bs).length ≤ bs.length+n := by
  induction n generalizing bs with
  | zero => simp [GrowingCounterData.advance]
  | succ n ih =>
    have hh := ih (GrowingCounterData.increment bs)
    have hi := (GrowingCounterData.increment_length bs).2
    simp only [GrowingCounterData.advance]
    omega

theorem bits_length (v : Descriptor) : (RecursiveVolumeConstruct.bits (q := q) v).length ≤ volume q v := by
  have hh := advance_length (volume q v) []
  have he : v.beforeRows*v.rows*v.beforeH*q^v.width*(v.between*(q^v.width*v.afterD)) = volume q v := by
    unfold volume
    ring
  simpa only [RecursiveVolumeConstruct.bits,DimensionProductDescriptor.bits,he,List.length_nil,Nat.zero_add] using hh

/-- All private tapes, including trackers, are blank with zero heads. -/
theorem private_blank (hs : Fin 6 → List Bool) (bs : Option (List Bool))
    (i : Fin 17) (hi : keep i = false) :
    (bank (q := q) hs bs).head (Fin.castAdd 17 i) = 0 ∧
    (bank (q := q) hs bs).tape (Fin.castAdd 17 i) = fun _ => blank := by
  fin_cases i <;> simp_all [keep,right] <;> exact ⟨rfl,rfl⟩

theorem trackers_blank (hs : Fin 6 → List Bool) (bs : Option (List Bool)) (i : Fin 17) :
    (bank (q := q) hs bs).head (Fin.natAdd 17 i) = 0 ∧
    (bank (q := q) hs bs).tape (Fin.natAdd 17 i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

end
end IntegerMultBounds.Machine.RecursiveVolumeClean
