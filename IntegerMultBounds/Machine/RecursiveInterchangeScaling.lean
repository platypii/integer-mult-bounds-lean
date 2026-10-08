import IntegerMultBounds.Machine.RecursiveInterchangeLayout
import IntegerMultBounds.Machine.FlatAffineScalingPayload

/-! Actual normalized H/D scalings on the seven-factor recursive interface.
Spectator cardinalities and row count are arbitrary positive integers. The
fiber views are casts of the same serialized word, not tape transpositions.
This interface assumes canonical prefix/modulus/suffix descriptors; physically
constructing them from the recursive descriptor remains a separate obligation. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeScaling
open RecursiveInterchangeLayout (Descriptor volume)
open Networks
open ActualAffineScaling (modulus)
open Shared50ModularControl (prime)
noncomputable section

inductive Target where | h | d
  deriving DecidableEq

structure Address (v : Descriptor) where
  beforeRows : Fin v.beforeRows
  row : Fin v.rows
  before : Fin v.beforeH
  h : Fin (modulus v.width)
  middle : Fin v.between
  d : Fin (modulus v.width)
  after : Fin v.afterD

private def pack {m n : ℕ} (a : Fin m) (b : Fin n) : Fin (m*n) := finProdFinEquiv (a,b)
private theorem pack_val {m n : ℕ} (a : Fin m) (b : Fin n) : (pack a b).val = a.val*n+b.val := by simp [pack,finProdFinEquiv]; ring

def index {v : Descriptor} (x : Address v) : Fin (volume prime v) :=
  pack (pack (pack (pack (pack (pack x.beforeRows x.row) x.before) x.h) x.middle) x.d) x.after

/-- The flattened index is literally the manuscript's original field order. -/
theorem index_val {v : Descriptor} (x : Address v) :
    (index x).val = RecursiveInterchangeLayout.index prime v x.beforeRows.val x.row.val x.before.val
      x.h.val x.middle.val x.d.val x.after.val := by
  simp [index,pack,finProdFinEquiv,RecursiveInterchangeLayout.index,modulus]
  ring

def prefixSize (v : Descriptor) : Target → ℕ
  | .h => v.beforeRows*v.rows*v.beforeH
  | .d => v.beforeRows*v.rows*v.beforeH*modulus v.width*v.between

def suffix (v : Descriptor) : Target → ℕ
  | .h => v.between*modulus v.width*v.afterD
  | .d => v.afterD

def prefixIndex {v : Descriptor} (x : Address v) : (t : Target) → Fin (prefixSize v t)
  | .h => pack (pack x.beforeRows x.row) x.before
  | .d => pack (pack (pack (pack x.beforeRows x.row) x.before) x.h) x.middle

def suffixIndex {v : Descriptor} (x : Address v) : (t : Target) → Fin (suffix v t)
  | .h => pack (pack x.middle x.d) x.after
  | .d => x.after

def coordinate {v : Descriptor} (x : Address v) : Target → Fin (modulus v.width)
  | .h => x.h
  | .d => x.d

theorem split_volume (v : Descriptor) (t : Target) :
    volume prime v = prefixSize v t*(modulus v.width*suffix v t) := by
  cases t <;> simp only [volume,prefixSize,suffix,modulus] <;> ring

theorem index_split {v : Descriptor} (x : Address v) (t : Target) :
    Fin.cast (split_volume v t) (index x) = FiberLayoutData.index (prefixIndex x t) (coordinate x t) (suffixIndex x t) := by
  apply Fin.ext
  cases t
  · change x.after.val+v.afterD*(x.d.val+prime^v.width*(x.middle.val+v.between*(x.h.val+prime^v.width*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val))))) =
      ((x.after.val+v.afterD*(x.d.val+prime^v.width*x.middle.val))+(v.between*prime^v.width*v.afterD)*x.h.val)+
        (prime^v.width*(v.between*prime^v.width*v.afterD))*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val))
    ring
  · change x.after.val+v.afterD*(x.d.val+prime^v.width*(x.middle.val+v.between*(x.h.val+prime^v.width*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val))))) =
      (x.after.val+v.afterD*x.d.val)+(prime^v.width*v.afterD)*(x.middle.val+v.between*(x.h.val+prime^v.width*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val))))
    ring

def view {v : Descriptor} (a : Fin (volume prime v) → Fin 4) (t : Target) :
    Fin (prefixSize v t*(modulus v.width*suffix v t)) → Fin 4 :=
  fun i => a (Fin.cast (split_volume v t).symm i)

theorem view_word {v : Descriptor} (a : Fin (volume prime v) → Fin 4) (t : Target) :
    List.ofFn (view a t) = List.ofFn a := (List.ofFn_congr (split_volume v t) _).symm

def scaleAddress {v : Descriptor} (r : ℚ) (x : Address v) : Target → Address v
  | .h => { x with h := FlatAffineScalingArray.coordinate r x.h }
  | .d => { x with d := FlatAffineScalingArray.coordinate r x.d }

def array {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) : Fin (volume prime v) → Fin 4 :=
  fun i => FlatAffineScalingArray.array hr (view a t) (Fin.cast (split_volume v t) i)

theorem array_word {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) :
    List.ofFn (array hr a t) = List.ofFn (FlatAffineScalingArray.array hr (view a t)) :=
  (List.ofFn_congr (split_volume v t).symm _).symm

/-- Every spectator, including the arbitrary row field, stays unchanged. -/
theorem array_entry {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (x : Address v) :
    array hr a t (index (scaleAddress r x t)) = a (index x) := by
  have hh := FlatAffineScalingArray.array_entry hr (view a t) (prefixIndex x t) (coordinate x t) (suffixIndex x t)
  unfold array
  rw [index_split]
  have he : view a t (FiberLayoutData.index (prefixIndex x t) (coordinate x t) (suffixIndex x t)) = a (index x) := by
    rw [← index_split]
    rfl
  rw [he] at hh
  cases t <;> exact hh

/-- The finite program is independent of all seven runtime field lengths. -/
def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) :=
  FlatAffineScalingPayload.program (radix := prime) hr

def input {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (bs qs ps : List Bool) :=
  FlatAffineScalingPayload.input (radix := prime) hr (view a t) bs qs ps

def output {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (bs qs ps : List Bool) :=
  FlatAffineScalingPayload.output (radix := prime) hr (view a t) bs qs ps

theorem realizes_hoare {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (hv : v.Positive)
    (bs qs ps : List Bool) (hb : Counter.value bs = suffix v t)
    (hq : Counter.value qs = modulus v.width) (hp : Counter.value ps = prefixSize v t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps) :
    HoareTime (program hr) (fun w => w = input hr a t bs qs ps) (fun w => w = output hr a t bs qs ps)
      ((2064+120*(r.num.natAbs+r.den))*volume prime v+254) := by
  have hmod := ActualAffineScaling.modulus_pos v.width
  have hpre : 0 < prefixSize v t := by
    rcases hv with ⟨ha,hr,hb,hc,he⟩
    cases t <;> simp only [prefixSize] <;> positivity
  have hsuf : 0 < suffix v t := by
    rcases hv with ⟨ha,hr,hb,hc,he⟩
    cases t <;> simp only [suffix] <;> positivity
  have hh := FlatAffineScalingPayload.realizes_hoare (radix := prime) hr (view a t)
    hsuf hpre bs qs ps hb hq hp cb cq cp
  simpa only [program,input,output,← split_volume] using hh

/-- Canonical physical input without reordering any row or spectator. -/
theorem input_payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (bs qs ps : List Bool) :
    SharedPayload.payload (input hr a t bs qs ps) (FlatAffineScaling.sourceSlot r)
      (ActualAffineScalingStream.destinationSlot r) = FlatAffineScalingPayload.pair a := by
  unfold input
  rw [FlatAffineScalingPayload.input_payload]
  unfold FlatAffineScalingPayload.pair
  rw [view_word]

/-- The same source/scratch pair returns the canonical transformed array. -/
theorem output_payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (bs qs ps : List Bool) :
    SharedPayload.payload (output hr a t bs qs ps) (FlatAffineScaling.sourceSlot r)
      (ActualAffineScalingStream.destinationSlot r) = FlatAffineScalingPayload.pair (array hr a t) := by
  unfold output
  rw [FlatAffineScalingPayload.output_payload]
  unfold FlatAffineScalingPayload.pair
  rw [array_word]

/-- One actual machine simultaneously satisfies the full tape contract and
seven-field address semantics; supplied descriptors remain explicit premises. -/
theorem realizes_array {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (volume prime v) → Fin 4) (t : Target) (hv : v.Positive)
    (bs qs ps : List Bool) (hb : Counter.value bs = suffix v t)
    (hq : Counter.value qs = modulus v.width) (hp : Counter.value ps = prefixSize v t)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cp : GrowingCounterData.Canonical ps) :
    HoareTime (program hr) (fun w => w = input hr a t bs qs ps)
      (fun w => w = output hr a t bs qs ps ∧
        SharedPayload.payload w (FlatAffineScaling.sourceSlot r) (ActualAffineScalingStream.destinationSlot r) =
          FlatAffineScalingPayload.pair (array hr a t) ∧
        ∀ x : Address v, array hr a t (index (scaleAddress r x t)) = a (index x))
      ((2064+120*(r.num.natAbs+r.den))*volume prime v+254) := by
  apply (realizes_hoare hr a t hv bs qs ps hb hq hp cb cq cp).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,output_payload hr a t bs qs ps,array_entry hr a t⟩

end
end IntegerMultBounds.Machine.RecursiveInterchangeScaling
