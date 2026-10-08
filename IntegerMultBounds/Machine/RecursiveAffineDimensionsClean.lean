import IntegerMultBounds.Machine.RecursiveAffineDimensionsBound
import IntegerMultBounds.Machine.RecursiveChildHeaderHandoff

/-! Within-group spectator construction with a fixed physical output placement
and full private cleanup. New headers occupy exactly the child handoff ports,
so occupied old headers can be replaced by the existing paid handoff machine. -/
namespace IntegerMultBounds.Machine.RecursiveAffineDimensionsClean
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveAffineDimensions (Group)
variable {q : ℕ} (hq : 2 ≤ q)
noncomputable section

def view (b : ℕ) (v : Descriptor) {m : ℕ} (j i : Fin m) : Group → Descriptor
  | .h => RecursiveAffineViews.withinH q b v j i
  | .d => RecursiveAffineViews.withinD q b v j i

def headers (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) : Fin 6 → List Bool :=
  let xs := RecursiveAffineDimensions.words hq v b j i g
  ![hs 0,rs,xs (match g with | .h => 4 | .d => 6),bs,xs 1,xs 7]

theorem headers_spec (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) (hv : RecursiveDimensionBank.Headers v hs)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs)
    (hr : Counter.value rs = v.rows) (cr : GrowingCounterData.Canonical rs) :
    RecursiveDimensionBank.Headers (view (q := q) b v j i g) (headers hq b v hs bs rs j i g) := by
  constructor
  · intro z
    cases g <;> fin_cases z <;>
      simp only [headers,view,RecursiveDimensionBank.values,RecursiveAffineViews.withinH,RecursiveAffineViews.withinD,
        RecursiveAffineDimensions.words,RecursiveAffineDimensions.powerBits,RecursiveAffineDimensions.exponent,
        RecursiveAffineDimensions.productLeft,RecursiveAffineDimensions.productRight,Fin.addCases]
    all_goals first | exact hv.1 0 | exact hr | exact hb |
      exact DimensionProductDescriptor.bits_value _ _ | exact RadixPowerMultipleDescriptor.bits_value _ _
  · intro z
    cases g <;> fin_cases z <;>
      simp only [headers,RecursiveAffineDimensions.words,RecursiveAffineDimensions.powerBits,
        RecursiveAffineDimensions.exponent,RecursiveAffineDimensions.productLeft,RecursiveAffineDimensions.productRight,
        Fin.addCases]
    all_goals first | exact hv.2 0 | exact cr | exact cb |
      exact DimensionProductDescriptor.bits_canonical _ _ | exact RadixPowerMultipleDescriptor.bits_canonical _ _

/-- A fixed relabelling makes the constructor write directly into handoff ports.
It fixes every input header and quotient tape. There is no runtime permutation. -/
def placement : Group → (Fin 19 ≃ Fin 19)
  | .h => Equiv.swap 12 17
  | .d => (Equiv.swap 12 15).trans (Equiv.swap 15 17)

def alignedProgram {m : ℕ} (j i : Fin m) (g : Group) :=
  reindex (RecursiveAffineDimensions.program hq j i g) (placement g)

def alignedOutput (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) :=
  (RecursiveAffineDimensions.state hq v hs bs rs b j i g 8).reindex (placement g)

private theorem input_reindex (hs : Fin 6 → List Bool) (bs rs : List Bool) (g : Group) :
    (RecursiveChildDimensions.input (q := q) hs bs rs).reindex (placement g) =
      RecursiveChildDimensions.input hs bs rs := by
  cases g <;> apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

def output (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) : Tapes 38 q :=
  let ch := headers hq b v hs bs rs j i g
  (RecursiveChildDimensions.bank hs bs rs ![none,none,none,none,some (ch 2),none,some (ch 4),some (ch 5)]).append
    (SharedBank.empty 19 q)

def program {m : ℕ} (j i : Fin m) (g : Group) :=
  CleanExecution.program (alignedProgram hq j i g) RecursiveChildDimensionsClean.right RecursiveChildDimensionsClean.keep

private theorem retained_output (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) :
    (TrackedCleanupList.retained RecursiveChildDimensionsClean.keep (alignedOutput hq b v hs bs rs j i g)).append
      (SharedBank.empty 19 q) = output hq b v hs bs rs j i g := by
  congr 1
  cases g <;> apply congrArg₂ Tapes.mk <;> funext z <;> fin_cases z <;> rfl

theorem constructs_hoare (b : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (bs rs : List Bool)
    {m : ℕ} (j i : Fin m) (g : Group) (hji : j < i) (hw : v.width=m*b)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive)
    (hb : Counter.value bs = b) (cb : GrowingCounterData.Canonical bs) :
    HoareTime (program hq j i g) (fun w => w = RecursiveChildDimensionsClean.input hs bs rs)
      (fun w => w = output hq b v hs bs rs j i g) (97*(96*m+512)*volume q v+11756) := by
  have hh := hoare_reindex_eq (RecursiveAffineDimensions.constructs_hoare hq v hs bs rs b j i g hv hp hb cb) (placement g)
  rw [input_reindex] at hh
  have hc := CleanExecution.realizes (alignedProgram hq j i g)
    RecursiveChildDimensionsClean.right RecursiveChildDimensionsClean.keep
    (RecursiveChildDimensions.input hs bs rs) (alignedOutput hq b v hs bs rs j i g) _
    (by funext z; fin_cases z <;> rfl)
    (by intro z hz; apply (RecursiveChildDimensions.input_blank hs bs rs z ?_).2
        simp only [RecursiveChildDimensionsClean.keep,RecursiveChildDimensionsClean.right,
          Bool.or_eq_false_iff,decide_eq_false_iff_not] at hz
        exact hz.1) hh
  rw [retained_output] at hc
  apply hc.consequence (fun _ h => h) (fun _ h => h) ?_
  have hbnd := RecursiveAffineDimensionsBound.cost_le hq v hp b j i hji hw g
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveAffineDimensionsClean
