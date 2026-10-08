import IntegerMultBounds.Machine.RecursiveChildDimensions
import IntegerMultBounds.Machine.CleanExecution

/-! Child-dimension construction with all arithmetic scratch, powers, temporary
products and trackers physically erased. Six parent headers and two explicit
quotients remain, alongside the three new child spectator headers. -/
namespace IntegerMultBounds.Machine.RecursiveChildDimensionsClean
open RecursiveInterchangeLayout (Descriptor child volume)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def right (z : Fin 19) : Bool := decide (3 ≤ z.val ∧ z.val < 11)
def keep (z : Fin 19) : Bool := right z || decide (z.val = 15 ∨ z.val = 17 ∨ z.val = 18)

def cleanDescriptors (ds : Fin 8 → Option (List Bool)) : Fin 8 → Option (List Bool) :=
  ![none,none,none,none,ds 4,none,ds 6,ds 7]

def input (hs : Fin 6 → List Bool) (bs rs : List Bool) : Tapes 38 q :=
  (RecursiveChildDimensions.input hs bs rs).append (SharedBank.empty 19 q)

def output (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) : Tapes 38 q :=
  (RecursiveChildDimensions.bank hs bs rs
    (cleanDescriptors (RecursiveChildDimensions.ds8 hq v b i j))).append (SharedBank.empty 19 q)

def program {m : ℕ} (i j : Fin m) :=
  CleanExecution.program (RecursiveChildDimensions.program hq i j) right keep

private theorem input_head (hs : Fin 6 → List Bool) (bs rs : List Bool) :
    (RecursiveChildDimensions.input (q := q) hs bs rs).head = TrackedInit.position right := by
  funext z
  fin_cases z <;> rfl

private theorem input_private (hs : Fin 6 → List Bool) (bs rs : List Bool) (z : Fin 19) (hz : keep z = false) :
    (RecursiveChildDimensions.input (q := q) hs bs rs).tape z = fun _ => blank := by
  apply (RecursiveChildDimensions.input_blank hs bs rs z ?_).2
  simp only [keep,right,Bool.or_eq_false_iff,decide_eq_false_iff_not] at hz
  exact hz.1

private theorem retained_bank (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ds : Fin 8 → Option (List Bool)) :
    TrackedCleanupList.retained keep (RecursiveChildDimensions.bank (q := q) hs bs rs ds) =
      RecursiveChildDimensions.bank hs bs rs (cleanDescriptors ds) := by
  apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

/-- Explicit canonical quotient inputs are consumed unchanged. Everything
computed temporarily is erased; child spectators are the only added headers. -/
theorem constructs_hoare (roles b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    HoareTime (program hq i j) (fun w => w = input hs bs rs)
      (fun w => w = output hq v hs bs rs b i j)
      (97*(48*(m-1)+512)*volume q (child q roles b v i j)+11756) := by
  have hh := CleanExecution.realizes (RecursiveChildDimensions.program hq i j) right keep
    (RecursiveChildDimensions.input hs bs rs) (RecursiveChildDimensions.output hq v hs bs rs b i j)
    _ (input_head hs bs rs) (input_private hs bs rs)
    (RecursiveChildDimensions.constructs_hoare hq roles b v hs bs rs i j hv hvpos hb cb hr hdiv)
  simp only [RecursiveChildDimensions.output,retained_bank] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

def childSlots (z : Fin 6) : Fin 38 := Fin.castAdd 19 (RecursiveChildDimensions.childSlots z)

private theorem clean_headers (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ds : Fin 8 → Option (List Bool)) (z : Fin 6) :
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).head (RecursiveChildDimensions.childSlots z) =
      (RecursiveChildDimensions.bank (q := q) hs bs rs ds).head (RecursiveChildDimensions.childSlots z) ∧
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).tape (RecursiveChildDimensions.childSlots z) =
      (RecursiveChildDimensions.bank (q := q) hs bs rs ds).tape (RecursiveChildDimensions.childSlots z) := by
  unfold RecursiveChildDimensions.bank cleanDescriptors RecursiveChildDimensions.childSlots
  fin_cases z <;> norm_num [Matrix.cons_val]

theorem output_headers (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 6) :
    (output hq v hs bs rs b i j).head (childSlots z) = 1 ∧
    (output hq v hs bs rs b i j).tape (childSlots z) =
      RadixZeroFill.encodedBinary (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j z) := by
  simp only [output,childSlots,Tapes.append,Fin.addCases_left]
  obtain ⟨hh,ht⟩ := clean_headers (q := q) hs bs rs (RecursiveChildDimensions.ds8 hq v b i j) z
  rw [hh,ht]
  exact RecursiveChildDimensions.output_headers hq v hs bs rs b i j z

/-- The exact child descriptor and role-stream volume agree with the pure layout. -/
theorem constructs_child (roles b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (i j : Fin m) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hrows : Counter.value rs = v.rows/roles) (crows : GrowingCounterData.Canonical rs)
    (hw : v.width = m*b) (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    HoareTime (program hq i j) (fun w => w = input hs bs rs)
      (fun w => w = output hq v hs bs rs b i j ∧
        RecursiveDimensionBank.Headers (child q roles b v i j)
          (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j) ∧
        (∀ z : Fin 6, w.head (childSlots z) = 1 ∧ w.tape (childSlots z) =
          RadixZeroFill.encodedBinary (RecursiveChildDimensions.childHeaders (q := q) v hs bs rs b i j z)) ∧
        volume q (child q roles b v i j) = volume q v/roles)
      (97*(48*(m-1)+512)*(volume q v/roles)+11756) := by
  have hvol := RecursiveInterchangeLayout.child_volume_div q roles b v i j hw hr hdiv
  rw [← hvol]
  apply (constructs_hoare hq roles b v hs bs rs i j hv hvpos hb cb hr hdiv).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,RecursiveChildDimensions.child_headers roles b v hs bs rs i j hv hb cb hrows crows,
    output_headers hq v hs bs rs b i j,rfl⟩

private theorem clean_inputs (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ds : Fin 8 → Option (List Bool)) (z : Fin 8) :
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).head (RecursiveChildDimensions.inputSlot z) =
      (RecursiveChildDimensions.bank (q := q) hs bs rs ds).head (RecursiveChildDimensions.inputSlot z) ∧
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).tape (RecursiveChildDimensions.inputSlot z) =
      (RecursiveChildDimensions.bank (q := q) hs bs rs ds).tape (RecursiveChildDimensions.inputSlot z) := by
  unfold RecursiveChildDimensions.bank cleanDescriptors RecursiveChildDimensions.inputSlot
  fin_cases z <;> norm_num [Matrix.cons_val,Fin.natAdd,Fin.castAdd,Fin.castLE]

/-- Cleanup also preserves the parent and quotient headers exactly. -/
theorem inputs_preserved (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 8) :
    (output hq v hs bs rs b i j).head (Fin.castAdd 19 (RecursiveChildDimensions.inputSlot z)) =
      (input (q := q) hs bs rs).head (Fin.castAdd 19 (RecursiveChildDimensions.inputSlot z)) ∧
    (output hq v hs bs rs b i j).tape (Fin.castAdd 19 (RecursiveChildDimensions.inputSlot z)) =
      (input (q := q) hs bs rs).tape (Fin.castAdd 19 (RecursiveChildDimensions.inputSlot z)) := by
  simp only [output,input,Tapes.append,Fin.addCases_left]
  obtain ⟨hh,ht⟩ := clean_inputs (q := q) hs bs rs (RecursiveChildDimensions.ds8 hq v b i j) z
  rw [hh,ht]
  exact RecursiveChildDimensions.inputs_preserved hq v hs bs rs b i j z

private theorem clean_private (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (ds : Fin 8 → Option (List Bool)) (z : Fin 19) (hz : keep z = false) :
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).head z = 0 ∧
    (RecursiveChildDimensions.bank (q := q) hs bs rs (cleanDescriptors ds)).tape z = fun _ => blank := by
  fin_cases z <;> first | exact ⟨rfl,rfl⟩ | (norm_num [keep,right] at hz)

theorem private_blank (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 19) (hz : keep z = false) :
    (output hq v hs bs rs b i j).head (Fin.castAdd 19 z) = 0 ∧
    (output hq v hs bs rs b i j).tape (Fin.castAdd 19 z) = fun _ => blank := by
  simp only [output,Tapes.append,Fin.addCases_left]
  exact clean_private hs bs rs _ z hz

theorem trackers_blank (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    (b : ℕ) {m : ℕ} (i j : Fin m) (z : Fin 19) :
    (output hq v hs bs rs b i j).head (Fin.natAdd 19 z) = 0 ∧
    (output hq v hs bs rs b i j).tape (Fin.natAdd 19 z) = fun _ => blank := by
  simp only [output,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

end
end IntegerMultBounds.Machine.RecursiveChildDimensionsClean
