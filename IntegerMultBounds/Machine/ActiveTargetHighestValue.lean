import IntegerMultBounds.Machine.ActiveTargetHighestRun

/-! The actual rational coefficient-one one-bit rotation is the elementary
highest selected XOR, with every prefix/intervening/suffix coordinate fixed. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestValue
noncomputable section
open ActiveTargetHighestRun
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def bit (z : Bool) : Fin 2 := ⟨if z then 1 else 0,by cases z <;> decide⟩
def sourceBit (G i : ℕ) : Bool := decide (i/2^G%2=1)

theorem sourceBit_value (G i : ℕ) : (bit (sourceBit G i)).val=i/2^G%2 := by
  have hm := Nat.mod_lt (i/2^G) (by decide : 0<2)
  by_cases h : i/2^G%2=1
  · simp [sourceBit,bit,h]
  · simp [sourceBit,bit,h]
    omega

theorem offset (G L i : ℕ) :
    FlatControlledShift.physicalOffset (radix := 2) (1 : ℚ) low (width G L) i=(bit (sourceBit G i)).val := by
  change (Swap.Modular.ratMod 2 1*((i/2^G%2 : ℕ) : ZMod 2)).val=_
  rw [Swap.Modular.ratMod_one,one_mul,ZMod.val_natCast,Nat.mod_mod]
  exact (sourceBit_value G i).symm

theorem xor_rotation (y z : Bool) : ((bit y).val+(bit z).val)%2=(bit (xor y z)).val := by
  cases y <;> cases z <;> rfl

/-- This is the exact full-array transport of the checked physical machine.
The source control is the actual prefix bit; no offset-word premise appears. -/
theorem entry (G L B : ℕ) (a : Array G L B) (i : Fin (prefixSize G L)) (y : Bool) (j : Fin B) :
    array G L a (FiberLayoutData.index i (bit (xor y (sourceBit G i.val))) j)=
      a (FiberLayoutData.index i (bit y) j) := by
  have h := FlatControlledShiftArray.array_entry (radix := 2) (1 : ℚ) low high (width G L) a i (bit y) j
  rw [offset] at h
  simp only [width,Matrix.cons_val_zero,pow_one] at h
  have he : (⟨((bit y).val+(bit (sourceBit G i.val)).val)%2,by omega⟩ : Fin 2)=
      bit (xor y (sourceBit G i.val)) := Fin.ext (xor_rotation _ _)
  rw [he] at h
  exact h

/-- One fixed physical machine with exact XOR transport and full cleanup. -/
theorem realizes (G L B : ℕ) (hB : 0<B) (ws : Fin 3 → List Bool) (a : Array G L B) (bs qs ns : List Bool)
    (hw : ∀ i, Counter.value (ws i)=width G L i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (hb : Counter.value bs=B) (hq : Counter.value qs=2) (hn : Counter.value ns=prefixSize G L)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs) (cn : GrowingCounterData.Canonical ns) :
    HoareTime program (fun v => v=ActiveTargetHighestRun.input G L ws a bs qs ns)
      (fun v => v=output G L ws a bs qs ns ∧
        ∀ (i : Fin (prefixSize G L)) (y : Bool) (j : Fin B),
          array G L a (FiberLayoutData.index i (bit (xor y (sourceBit G i.val))) j)=
            a (FiberLayoutData.index i (bit y) j)) (constant*volume G L B) := by
  exact (runs G L B hB ws a bs qs ns hw cw hb hq hn cb cq cn).consequence
    (fun _ h => h) (fun _ h => ⟨h,entry G L B a⟩) le_rfl

end
end IntegerMultBounds.Machine.ActiveTargetHighestValue
