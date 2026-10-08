import IntegerMultBounds.Machine.RecursiveInterchangeScaling
import IntegerMultBounds.Machine.FlatRepeatedControlArray

/-! Actual normalized H-controlled D shifts on the seven-factor recursive
layout. The four canonical dimension descriptors and prepared zero control are
explicit inputs; they are not assumed to have been generated from blank tapes. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeShift
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Address index)
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

def initial (v : Descriptor) : List (Fin prime) := RadixCounterData.zeros (Fact.out : prime.Prime).two_le v.width
@[simp] theorem initial_length (v : Descriptor) : (initial v).length = v.width := by simp [initial]

def count (v : Descriptor) := v.beforeRows*v.rows*v.beforeH*modulus v.width

theorem split_volume (v : Descriptor) :
    volume prime v = count v*(v.between*(prime^(initial v).length*v.afterD)) := by
  simp only [count,volume,initial_length,modulus]
  ring

def prefixIndex {v : Descriptor} (x : Address v) : Fin (count v) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (x.beforeRows,x.row),x.before),x.h)

def view {v : Descriptor} (a : Fin (volume prime v) → Fin 4) :
    Fin (count v*(v.between*(prime^(initial v).length*v.afterD))) → Fin 4 :=
  fun i => a (Fin.cast (split_volume v).symm i)

theorem view_word {v : Descriptor} (a : Fin (volume prime v) → Fin 4) : List.ofFn (view a) = List.ofFn a :=
  (List.ofFn_congr (split_volume v) _).symm

def target {v : Descriptor} (x : Address v) : Fin (prime^(initial v).length) :=
  ⟨x.d.val,by simpa [modulus] using x.d.isLt⟩

theorem index_split {v : Descriptor} (x : Address v) :
    Fin.cast (split_volume v) (index x) =
      finProdFinEquiv (prefixIndex x,FiberLayoutData.index x.middle (target x) x.after) := by
  apply Fin.ext
  simp only [Fin.val_cast,RecursiveInterchangeScaling.index_val]
  change RecursiveInterchangeLayout.index prime v x.beforeRows.val x.row.val x.before.val
    x.h.val x.middle.val x.d.val x.after.val =
    (x.after.val+v.afterD*x.d.val+(prime^(initial v).length*v.afterD)*x.middle.val)+
      (v.between*(prime^(initial v).length*v.afterD))*(x.h.val+prime^v.width*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val)))
  simp only [RecursiveInterchangeLayout.index,initial_length]
  ring

def array {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) : Fin (volume prime v) → Fin 4 :=
  fun i => FlatRepeatedControlArray.array r (initial v) (view a) (Fin.cast (split_volume v) i)

theorem prefixIndex_val {v : Descriptor} (x : Address v) :
    (prefixIndex x).val = ((x.beforeRows.val*v.rows+x.row.val)*v.beforeH+x.before.val)*modulus v.width+x.h.val := by
  change x.h.val+prime^v.width*(x.before.val+v.beforeH*(x.row.val+v.rows*x.beforeRows.val)) = _
  simp only [modulus]
  ring

theorem offset_value {v : Descriptor} (r : ℚ) (hden : r.den < prime) (x : Address v) :
    FlatFixedControlShift.offset r (RationalTranslationStream.control (initial v) (prefixIndex x).val) =
      (Swap.Modular.ratMod (modulus v.width) r * (x.h.val : ZMod (modulus v.width))).val := by
  have hh := FlatRepeatedControlShift.offset_value r hden v.width (prefixIndex x).val
  have hp : ((prefixIndex x).val : ZMod (prime^v.width)) = (x.h.val : ZMod (prime^v.width)) := by
    rw [prefixIndex_val]
    simp [modulus]
  rw [hp] at hh
  exact hh

def shiftAddress {v : Descriptor} (r : ℚ) (x : Address v) : Address v :=
  { x with d := ⟨(x.d.val+FlatFixedControlShift.offset r
      (RationalTranslationStream.control (initial v) (prefixIndex x).val))%modulus v.width,
      Nat.mod_lt _ (ActualAffineScaling.modulus_pos v.width)⟩ }

/-- Only D changes, by the rational multiple of the original H coordinate. -/
theorem shiftAddress_d {v : Descriptor} (r : ℚ) (hden : r.den < prime) (x : Address v) :
    (shiftAddress r x).d.val =
      (x.d.val+(Swap.Modular.ratMod (modulus v.width) r*(x.h.val : ZMod (modulus v.width))).val)%modulus v.width := by
  simp only [shiftAddress,offset_value r hden x]

theorem array_entry {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (x : Address v) :
    array r a (index (shiftAddress r x)) = a (index x) := by
  have hh := FlatRepeatedControlArray.array_entry r (initial v) (view a) (prefixIndex x)
    x.middle (target x) x.after
  unfold array
  rw [index_split]
  have he : view a (finProdFinEquiv (prefixIndex x,FiberLayoutData.index x.middle (target x) x.after)) = a (index x) := by
    rw [← index_split]
    rfl
  rw [he] at hh
  simpa only [shiftAddress,target,prefixIndex,initial_length,modulus,Fin.val_cast,Fin.cast_mk] using hh

theorem array_word {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) :
    List.ofFn (array r a) = List.ofFn (FlatRepeatedControlArray.array r (initial v) (view a)) :=
  (List.ofFn_congr (split_volume v).symm _).symm

def program (r : ℚ) := FlatRepeatedControlArray.program (radix := prime) r

def input {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (bs qs cs ns : List Bool) :=
  FlatRepeatedControlShift.state r (initial v) (view a) bs qs cs ns [] 0

def output {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (bs qs cs ns : List Bool) :=
  FlatRepeatedControlArray.output r (initial v) (view a) bs qs cs ns []

theorem realizes_hoare {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4)
    (hv : v.Positive) (bs qs cs ns : List Bool)
    (hb : Counter.value bs = v.afterD) (hq : Counter.value qs = modulus v.width)
    (hc : Counter.value cs = v.between) (hn : Counter.value ns = count v)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program r) (fun w => w = input r a bs qs cs ns)
      (fun w => w = output r a bs qs cs ns) (1005*volume prime v+26) := by
  have hp := ActualAffineScaling.modulus_pos v.width
  rcases hv with ⟨hA,hR,hB,hC,hE⟩
  have hN : 0 < count v := by unfold count; positivity
  have hh := FlatRepeatedControlArray.realizes_hoare r hN hE hC (initial v) (view a)
    bs qs cs ns [] hb (by simpa [modulus] using hq) hc hn cb cq cc cn
    (by simp [GrowingCounterData.Canonical]) (by simpa [Counter.value,modulus] using hp)
  simpa only [program,input,output,← split_volume] using hh

theorem input_payload {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (bs qs cs ns : List Bool) :
    SharedPayload.payload (input r a bs qs cs ns) 10 11 = FlatRepeatedControlArray.pair a := by
  unfold input
  rw [FlatRepeatedControlArray.input_payload]
  unfold FlatRepeatedControlArray.pair
  rw [view_word]

theorem output_payload {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (bs qs cs ns : List Bool) :
    SharedPayload.payload (output r a bs qs cs ns) 10 11 = FlatRepeatedControlArray.pair (array r a) := by
  unfold output
  rw [FlatRepeatedControlArray.output_payload]
  unfold FlatRepeatedControlArray.pair
  rw [array_word]


/-- Every complete outer prefix cycle returns the physical H tape to zero. -/
theorem output_control {v : Descriptor} (r : ℚ) (a : Fin (volume prime v) → Fin 4) (bs qs cs ns : List Bool) :
    (output r a bs qs cs ns).head 15 = 1 ∧
    (output r a bs qs cs ns).tape 15 = RadixRationalBinary.source (initial v) := by
  constructor
  · rfl
  · change RadixRationalBinary.source (RationalTranslationStream.control (initial v) (count v)) = _
    exact congrArg RadixRationalBinary.source
      (RepeatedControlTranslationStream.control_prefix_cycles v.width (v.beforeRows*v.rows*v.beforeH))

/-- One actual normalized execution proves both the exact whole-bank contract
and the literal seven-factor H-controlled D semantics. -/
theorem realizes_array {v : Descriptor} (r : ℚ) (hden : r.den < prime)
    (a : Fin (volume prime v) → Fin 4) (hv : v.Positive) (bs qs cs ns : List Bool)
    (hb : Counter.value bs = v.afterD) (hq : Counter.value qs = modulus v.width)
    (hc : Counter.value cs = v.between) (hn : Counter.value ns = count v)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cc : GrowingCounterData.Canonical cs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime (program r) (fun w => w = input r a bs qs cs ns)
      (fun w => w = output r a bs qs cs ns ∧
        SharedPayload.payload w 10 11 = FlatRepeatedControlArray.pair (array r a) ∧
        ∀ x : Address v, array r a (index (shiftAddress r x)) = a (index x) ∧
          (shiftAddress r x).d.val =
            (x.d.val+(Swap.Modular.ratMod (modulus v.width) r*(x.h.val : ZMod (modulus v.width))).val)%modulus v.width)
      (1005*volume prime v+26) := by
  apply (realizes_hoare r a hv bs qs cs ns hb hq hc hn cb cq cc cn).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,output_payload r a bs qs cs ns,fun x => ⟨array_entry r a x,shiftAddress_d r hden x⟩⟩


end
end IntegerMultBounds.Machine.RecursiveInterchangeShift
