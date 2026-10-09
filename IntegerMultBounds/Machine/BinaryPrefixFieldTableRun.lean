import IntegerMultBounds.Machine.BinaryPrefixFieldTableCleanup

/-! End-to-end full-prefix field projection from three original descriptors.
All source addresses and dummy controls are physically generated and erased;
no extracted field stream or count descriptor is supplied. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableRun
noncomputable section
open CompactGadgetReservationHeadersCore (bank)
open BinaryPrefixFieldTableData (word)
open BinaryPrefixFieldTableGather (values)
open RecursiveChildQuotientsConstant (bits)

def program := seq (seq BinaryPrefixFieldTableSetup.program BinaryPrefixFieldTableGather.program)
  BinaryPrefixFieldTableCleanup.program

def cost (hs : Fin 3 → List Bool) (W d : ℕ) :=
  BinaryPrefixFieldTableSetup.cost hs W+1+169*((2^W+1)*(W+d+1))+1+BinaryPrefixFieldTableCleanup.cost hs W d

def input (hs : Fin 3 → List Bool) := bank (BinaryPrefixFieldTableSetup.base hs)
def output (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  bank (BinaryPrefixFieldTableCleanup.output hs W start d h)

theorem constructs (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=input hs) (fun v => v=output hs W start d h) (cost hs W d) :=
  ((BinaryPrefixFieldTableSetup.constructs hs W (hv 0) (hc 0)).seq
    (BinaryPrefixFieldTableGather.runs hs W start d h hv hc)).seq
    (BinaryPrefixFieldTableCleanup.cleans hs W start d h)

def constant := FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+1000

theorem cost_bound (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost hs W d ≤ constant*(2^W*(W+1)) := by
  let N := 2^W
  let V := N*(W+1)
  have hN : 1≤N := Nat.one_le_pow _ _ (by decide)
  have hV : 1≤V := Nat.mul_pos hN (by omega)
  have hNV : N≤V := Nat.le_mul_of_pos_right _ (by omega)
  have hWV : W+1≤V := Nat.le_mul_of_pos_left _ hN
  have hd := GrowingCounterData.canonical_width (hs 2) (hc 2)
  rw [hv 2] at hd
  change (hs 2).length≤d.log2+1 at hd
  have hlogd := Nat.log2_le_self d
  have hdV : (hs 2).length≤V := by omega
  have hcount := GrowingCounterData.canonical_width (bits N) (RecursiveChildQuotientsConstant.bits_canonical N)
  rw [RecursiveChildQuotientsConstant.bits_value] at hcount
  have hlogN := Nat.log2_le_self N
  have hcV : (bits N).length≤2*V := by omega
  have hg0 := Nat.mul_le_mul (by omega : N+1≤2*N) (by omega : W+d+1≤2*(W+1))
  have hg : 169*((N+1)*(W+d+1))≤676*V := by dsimp only [V]; nlinarith
  have hNW : N*W≤V := Nat.mul_le_mul_left N (by omega)
  have hNd : N*d≤V := Nat.mul_le_mul_left N (by omega)
  have hAV := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hNV
  unfold cost BinaryPrefixFieldTableSetup.cost BinaryPrefixFieldTableCleanup.cost constant
  change FixedBasePowerDescriptor.constant 2*N+1+6+1+(2*(hs 2).length+5)+1+
    BinaryAddressTable.constant*((W+1)*N)+1+(8*N+7*(bits N).length+39)+1+
    169*((N+1)*(W+d+1))+1+
    ((N*W+2)+1+(N+3)+1+(2*(bits N).length+4)+1+4+1+(2*(hs 2).length+4)+1+(N*d+2)) ≤
    (FixedBasePowerDescriptor.constant 2+BinaryAddressTable.constant+1000)*V
  have hvEq : (W+1)*N=V := Nat.mul_comm _ _
  rw [hvEq]
  nlinarith

theorem constructs_linear (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=input hs) (fun v => v=output hs W start d h)
      (constant*(2^W*(W+1))) :=
  (constructs hs W start d h hv hc).consequence (fun _ h => h) (fun _ h => h) (cost_bound hs W start d h hv hc)

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTableRun
