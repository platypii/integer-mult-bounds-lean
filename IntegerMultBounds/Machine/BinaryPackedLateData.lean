import IntegerMultBounds.Machine.BinaryPackedEarlyData
import IntegerMultBounds.Machine.CountedPackedParityValue
import IntegerMultBounds.Machine.CountedPackedControlLoadValue
import IntegerMultBounds.Compact.PackedInverseValue

/-! Actual fixed-width parity and load words compose two early row actions.
The dirty control is independent of both early fields and all spectators;
no initial zero contents are required. Physical placement is separate. -/
namespace IntegerMultBounds.Machine.BinaryPackedLateData
noncomputable section
open BinaryPackedEarlyData (Target Temp)
open BinaryAddressTableData (row)

abbrev State (q b n : ℕ) (S : Type*) := Target q n × Temp b n × Temp b n × S

def controls (b n : ℕ) (u : Temp b n) :=
  CountedPackedParityRun.parities b (row (n*b) u.val) n

@[simp] theorem controls_length (b n : ℕ) (u : Temp b n) :
    (controls b n u).length=n := by simp [controls,CountedPackedParityRun.parities]

theorem controls_value (b n : ℕ) (hb : 1≤b) (u : Temp b n) :
    (controls b n u).map Compact.PowerTwo.ctrl=
      (Compact.Radix.digits ((2 : ℤ)^b) n u.val).map (·%2) := by
  have h := CountedPackedParityValue.controls_eq_digit_parities b hb (row (n*b) u.val) n
    (BinaryAddressTableData.row_length _ _)
  simpa only [controls,BinaryAddressTableData.row_rank _ _ u.isLt] using h

def loadedWord (b n : ℕ) (hb : 1≤b) (X : List Bool) (u : Temp b n) :=
  CountedPackedControlLoadRun.word ColumnTransducer.addRule b hb (row (n*b) u.val) X

def unloadedWord (b n : ℕ) (hb : 1≤b) (X : List Bool) (u : Temp b n) :=
  CountedPackedControlLoadRun.word ColumnTransducer.subRule b hb (row (n*b) u.val) X

@[simp] theorem loadedWord_length (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) :
    (loadedWord b n hb X u).length=n*b := by
  rw [loadedWord,CountedPackedControlLoadRun.word_length]
  · exact BinaryAddressTableData.row_length _ _
  · simp [hX]
@[simp] theorem unloadedWord_length (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) :
    (unloadedWord b n hb X u).length=n*b := by
  rw [unloadedWord,CountedPackedControlLoadRun.word_length]
  · exact BinaryAddressTableData.row_length _ _
  · simp [hX]

def load (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) : Temp b n :=
  ⟨Counter.value (loadedWord b n hb X u),by simpa only [loadedWord_length b n hb X hX u] using Counter.value_lt (loadedWord b n hb X u)⟩
def unload (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) : Temp b n :=
  ⟨Counter.value (unloadedWord b n hb X u),by simpa only [unloadedWord_length b n hb X hX u] using Counter.value_lt (unloadedWord b n hb X u)⟩

theorem load_value (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) :
    ((load b n hb X hX u).val : ℤ)=
      ((u.val : ℤ)+Compact.Radix.pack ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl))%((2 : ℤ)^b)^n := by
  have h := CountedPackedControlLoadRun.load_value b hb (row (n*b) u.val) X (by simp [hX])
  simpa only [load,loadedWord,BinaryAddressTableData.row_rank _ _ u.isLt,hX] using h

theorem unload_value (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) :
    ((unload b n hb X hX u).val : ℤ)=
      ((u.val : ℤ)-Compact.Radix.pack ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl))%((2 : ℤ)^b)^n := by
  have h := CountedPackedControlLoadRun.unload_value b hb (row (n*b) u.val) X (by simp [hX])
  simpa only [unload,unloadedWord,BinaryAddressTableData.row_rank _ _ u.isLt,hX] using h

/-- Modular load/unload restores an arbitrary dirty control address. -/
theorem unload_load (b n : ℕ) (hb : 1≤b) (X : List Bool) (hX : X.length=n) (u : Temp b n) :
    unload b n hb X hX (load b n hb X hX u)=u := by
  apply Fin.ext
  have h := unload_value b n hb X hX (load b n hb X hX u)
  rw [load_value,Compact.PowerTwo.emod_cancel_add] at h
  have hu : (u.val : ℤ)<((2 : ℤ)^b)^n := by
    exact_mod_cast (show u.val<(2^b)^n by simpa [pow_mul,Nat.mul_comm n b] using u.isLt)
  rw [Int.emod_eq_of_lt (by positivity) hu] at h
  exact_mod_cast h

def early {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) : State q b n S :=
  BinaryPackedEarlyData.run q b n (controls b n x.2.2.1) hb hbq x

def run {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : State q b n S) : State q b n S :=
  let f := early q b n hb hbq x
  let u := load b n hb X hX f.2.2.1
  let s := early q b n hb hbq (f.1,f.2.1,u,f.2.2.2)
  (s.1,s.2.1,unload b n hb X hX s.2.2.1,s.2.2.2)

@[simp] theorem early_control {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) :
    (early q b n hb hbq x).2.2=x.2.2 := rfl

theorem early_value {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (x : State q b n S) :
    (((early q b n hb hbq x).1.val : ℤ),((early q b n hb hbq x).2.1.val : ℤ))=
      Compact.packedEarly ((2 : ℤ)^q) ((2 : ℤ)^b)
        ((Compact.Radix.digits ((2 : ℤ)^b) n x.2.2.1.val).map (·%2)) x.1.val x.2.1.val := by
  rw [early,BinaryPackedEarlyData.agrees q b n _ hb hbq (controls_length _ _ _),controls_value b n hb]

/-- The exact produced row words implement packedLate on every address,
including carries and borrows on exceptional addresses. -/
theorem agrees {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : State q b n S) :
    (((run q b n hb hbq X hX x).1.val : ℤ),((run q b n hb hbq X hX x).2.1.val : ℤ),
      ((run q b n hb hbq X hX x).2.2.1.val : ℤ))=
      Compact.packedLate ((2 : ℤ)^q) ((2 : ℤ)^b) (X.map Compact.PowerTwo.ctrl)
        x.1.val x.2.1.val x.2.2.1.val := by
  have hf := early_value q b n hb hbq x
  have hs := early_value q b n hb hbq
    ((early q b n hb hbq x).1,(early q b n hb hbq x).2.1,
      load b n hb X hX x.2.2.1,x.2.2.2)
  simp only [run,early_control] at *
  rw [load_value b n hb X hX] at hs
  simp only [Compact.packedLate,List.length_map,hX]
  rw [←hf]
  rw [←congrArg Prod.fst hs,←congrArg Prod.snd hs]
  simp only [unload_value,load_value]

/-- Both early stages retain the control while the actual load/unload words
restore it, without a guard hypothesis. -/
theorem restored_control {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : State q b n S) :
    (run q b n hb hbq X hX x).2.2.1=x.2.2.1 :=
  unload_load b n hb X hX x.2.2.1

/-- On the real late guard, the produced rows toggle the selected target
bits and retain both dirty fields, with all spectator contents arbitrary. -/
theorem good_value {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : State q b n S) (ds : List Compact.LateDigitState)
    (hcontrols : ds.map Compact.LateDigitState.x=X.map Compact.PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^q) (ds.map Compact.LateDigitState.v))
    (hw : (x.2.1.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (ds.map Compact.LateDigitState.w))
    (hu : (x.2.2.1.val : ℤ)=Compact.Radix.pack ((2 : ℤ)^b) (ds.map Compact.LateDigitState.u))
    (hgood : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    (((run q b n hb hbq X hX x).1.val : ℤ),((run q b n hb hbq X hX x).2.1.val : ℤ),
      ((run q b n hb hbq X hX x).2.2.1.val : ℤ))=
      (Compact.Radix.pack ((2 : ℤ)^q) (ds.map (fun d => Compact.toggle d.v d.x)),
        (x.2.1.val : ℤ),(x.2.2.1.val : ℤ)) := by
  have hq : 1≤q := by omega
  have hQ : (2 : ℤ)^q=2*2^(q-1) := by
    rw [←pow_succ']; congr 1; omega
  rw [agrees q b n hb hbq X hX x,hv,hw,hu,←hcontrols,hQ]
  exact Compact.packedLate_correct ((2 : ℤ)^b) ((2 : ℤ)^(q-1))
    (by exact_mod_cast Nat.one_le_two_pow) (by positivity) ds hgood

theorem spectator {S : Type*} (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (X : List Bool) (hX : X.length=n) (x : State q b n S) :
    (run q b n hb hbq X hX x).2.2.2=x.2.2.2 := rfl

end
end IntegerMultBounds.Machine.BinaryPackedLateData
