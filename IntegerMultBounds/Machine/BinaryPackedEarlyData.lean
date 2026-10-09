import IntegerMultBounds.Machine.BinaryRepeatedOffsetAction
import IntegerMultBounds.Machine.BinaryParityXorOffsetRepeatCoordinates
import IntegerMultBounds.Compact.Permutations

/-! The four actual produced offsets acting on one unchanged pair of packed
fields. Each offset is read from the current source field. The independent
spectator component can contain all dirty back, unused and payload coordinates. -/
namespace IntegerMultBounds.Machine.BinaryPackedEarlyData
open Compact (Field)
open Compact.Radix (pack digits)

abbrev Target (q n : ℕ) := Fin (2^(n*q))
abbrev Temp (b n : ℕ) := Fin (2^(n*b))
abbrev State (q b n : ℕ) (S : Type*) := Target q n × Temp b n × S

def add {w : ℕ} (x : Fin (2^w)) (a : ℕ) : Fin (2^w) :=
  ⟨(x.val+a)%2^w,Nat.mod_lt _ (by positivity)⟩

theorem add_value {w : ℕ} (x : Fin (2^w)) (a : ℕ) :
    ((add x a).val : ℤ)=((x.val : ℤ)+a)%(2 : ℤ)^w := by
  change (((x.val+a)%2^w : ℕ) : ℤ)=_
  push_cast
  rfl

def selected (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (t : Temp b n) :=
  Counter.value (BinarySelectedOffsetValue.rowWord q b n t.val Z hb hbq)
def parity (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (v : Target q n) :=
  Counter.value (BinaryAddressOffsetValue.rowWord q b n v.val hb hbq)
def correction (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (t : Temp b n) :=
  Counter.value (BinaryCorrectionOffsetValue.rowWord q b n t.val Z hb hbq)
def negative (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (v : Target q n) :=
  Counter.value (TwosComplement.negWord (BinaryParityXorOffsetData.rowWord q b n v.val Z hb hbq))

def first {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) : State q b n S :=
  (add x.1 (selected q b n Z hb hbq x.2.1),x.2)
def second {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) : State q b n S :=
  (x.1,add x.2.1 (parity q b n hb hbq x.1),x.2.2)
def third {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) : State q b n S :=
  (add x.1 (correction q b n Z hb hbq x.2.1),x.2)
def fourth {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) : State q b n S :=
  (x.1,add x.2.1 (negative q b n Z hb hbq x.1),x.2.2)
def run {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) :=
  fourth q b n Z hb hbq (third q b n Z hb hbq (second q b n hb hbq (first q b n Z hb hbq x)))

theorem spectator {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) :
    (run q b n Z hb hbq x).2.2=x.2.2 := rfl

theorem selected_value (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) (t : Temp b n) :
    (selected q b n Z hb hbq t : ℤ)=pack ((2 : ℤ)^q)
      (List.zipWith (fun z w => 2*z*w) (Z.map Compact.PowerTwo.ctrl) (digits ((2 : ℤ)^b) n t.val)) := by
  rw [selected,←BinarySelectedOffsetValue.field_eq q b n t.val Z hb hbq hZ t.isLt]
  exact BinarySelectedOffsetValue.field_value q b n t.val Z hb hbq hZ t.isLt

theorem parity_value (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (v : Target q n) :
    (parity q b n hb hbq v : ℤ)=pack ((2 : ℤ)^b) ((digits ((2 : ℤ)^q) n v.val).map (·%2)) := by
  rw [parity,←BinaryAddressOffsetValue.field_eq q b n v.val hb hbq v.isLt]
  exact BinaryAddressOffsetValue.field_value q b n v.val hb hbq v.isLt

theorem correction_value (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) (t : Temp b n) :
    (correction q b n Z hb hbq t : ℤ)=pack ((2 : ℤ)^q)
      (List.zipWith (fun z w => z*(1-2*w)) (Z.map Compact.PowerTwo.ctrl) (digits ((2 : ℤ)^b) n t.val))%(2 : ℤ)^(n*q) := by
  have h := BinaryRepeatedOffsetAction.correction_offset_value q b n 1 1 1 Z hb hbq hZ
    (0 : Fin 1) (0 : Fin (2^(n*q))) (0 : Fin 1) t (0 : Fin 1)
  rw [BinaryRepeatedOffsetAction.correction_offset q b n 1 1 1 Z hb hbq hZ] at h
  exact h

theorem negative_value (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) (v : Target q n) :
    (negative q b n Z hb hbq v : ℤ)=(-pack ((2 : ℤ)^b)
      (List.zipWith (fun v z => (v%2+z)%2) (digits ((2 : ℤ)^q) n v.val) (Z.map Compact.PowerTwo.ctrl)))%(2 : ℤ)^(n*b) := by
  rw [negative,←BinaryParityXorOffsetValue.field_eq q b n v.val Z hb hbq v.isLt]
  exact BinaryParityXorOffsetValue.field_value q b n v.val Z hb hbq hZ v.isLt

/-- Actual table offsets, including negative residues, compose in the precise
current-source order of the packed arithmetic program, on every address. -/
theorem agrees {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : State q b n S) :
    (((run q b n Z hb hbq x).1.val : ℤ),((run q b n Z hb hbq x).2.1.val : ℤ))=
      Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b) (Z.map Compact.PowerTwo.ctrl) x.1.val x.2.1.val := by
  simp only [run,fourth,third,second,first,add_value,selected_value q b n Z hb hbq hZ,
    parity_value,correction_value q b n Z hb hbq hZ,negative_value q b n Z hb hbq hZ,
    Int.add_emod_emod,Compact.packedEarly,List.length_map,hZ,pow_mul,Nat.mul_comm n q,Nat.mul_comm n b,
    sub_eq_add_neg]

/-- On the guarded set the actual four offsets toggle selected parity bits and
restore the dirty temporary exactly. No cleanliness is required of spectators. -/
theorem good_value {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : State q b n S) (ds : List Compact.DigitState)
    (hcontrols : ds.map Compact.DigitState.z=Z.map Compact.PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=pack ((2 : ℤ)^q) (ds.map Compact.DigitState.v))
    (hw : (x.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map Compact.DigitState.w))
    (hgood : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    (((run q b n Z hb hbq x).1.val : ℤ),((run q b n Z hb hbq x).2.1.val : ℤ))=
      (pack ((2 : ℤ)^q) (ds.map (fun d => Compact.toggle d.v d.z)),(x.2.1.val : ℤ)) := by
  have hq : 1≤q := by omega
  have hQ : (2 : ℤ)^q=2*2^(q-1) := by
    rw [←pow_succ']; congr 1; omega
  rw [agrees q b n Z hb hbq hZ x,hv,hw,←hcontrols,hQ]
  exact Compact.packedEarly_correct ((2 : ℤ)^b) ((2 : ℤ)^(q-1))
    (by exact_mod_cast Nat.one_le_two_pow) (by positivity) ds hgood

theorem good_temp {S : Type*} (q b n : ℕ) (Z : List Bool) (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n)
    (x : State q b n S) (ds : List Compact.DigitState)
    (hcontrols : ds.map Compact.DigitState.z=Z.map Compact.PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=pack ((2 : ℤ)^q) (ds.map Compact.DigitState.v))
    (hw : (x.2.1.val : ℤ)=pack ((2 : ℤ)^b) (ds.map Compact.DigitState.w))
    (hgood : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    (run q b n Z hb hbq x).2.1=x.2.1 := by
  apply Fin.ext
  have h := congrArg Prod.snd (good_value q b n Z hb hbq hZ x ds hcontrols hv hw hgood)
  dsimp only at h
  exact_mod_cast h

end IntegerMultBounds.Machine.BinaryPackedEarlyData
